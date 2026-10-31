import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Madvise

/-! # Checks.Cases.Checks.Sys.Mm.Mmap — what the mmap checker answers, read off against Linux

Pins over `Checks.Sys.Mm.Mmap`'s `check_mmap` and `mmap_witness`, the
twins of `theories/LinuxProcessSem/Checks/Sys/Mm/Mmap.v` and
`theories/LinuxProcessSem/Checks/Witness/Mm/Mmap.v`, and over its
`Checks/Sys/Table.lean` arm.  Not part of the trusted specification: this
file is QA on the definitions, written to be READ, and every claim in it
is a claim about what the kernel does, with the citation beside it.
Kernel readings are Linux v6.18.46 (commit 1f99e9ab748f) throughout.

WHAT THIS TWINS.  Rocq keeps the checker's worked examples beside the
spec's, in `theories/LinuxProcessSem/Checks/Cases/Mm/Mmap.v`, stated on
`check_syscall` and on `check_mmap` itself.  That file's spec-level half
is `Checks/Cases/Mm/Mmap.lean`'s; its checker-level half is what this
file restates, under this file's own names and against the same
fixtures, the way `Checks/Cases/Checks/Sys/Fs/Timerfd.lean` does for its
checker.  Nothing registers the correspondence:
`tools/check_lean_cases_parity.py` reads a coverage header at the Rocq
file's mirrored path, which is the spec twin's
(`Checks/Cases/Mm/Mmap.lean`), and K6c did not write that header
either: its section keeps the spec twin untouched, for the reason given
there.  The tool cannot name this file's theorems: it requires every
`covers:` target to be a top-level theorem of the claiming file itself,
so the Rocq checker cases stay "unclaimed" to it until either their
claims are restated in the spec twin or the tool learns to read a second
file.  Until then a Rocq checker case with no pin here is found by
reading, not by a tool — K6c's section restates the file's mmap-family
`= CheckReject` lemmas under their Rocq names for that reader.  The
dispatcher-level pins at the end of K6b's section are where the Lean
checker first answers a real `mmap` call.

WHAT IS UNDER TEST is the ACCEPTOR, not the spec.  `Checks/Cases/Mm/Mmap.lean`
reads `mmap_spec` off `mm/mmap.c` and `mm/vma.c`, and the four proofs in the
checker's file tie `check_mmap` to that spec at every input.  What those
proofs cannot say is which concrete answer the checker gives — a checker
that accepted everything and a spec that admitted everything would
satisfy all four — so each pin here offers the checker one concrete
effect and pins the verdict.  Every accepting pin is paired with the
refusal of a different return, a different ledger or a different shape,
so that "the model accepts this" is not the vacuous reading of a checker
that accepts everything.  The refusals are stated as `= CheckReject`,
which `tools/check_lean_pin_evidence.py` classes as positive, so they
carry kernel readings rather than the probes' `reject` cases (the reading
`Checks/Cases/Checks/Sys/Kernel/Exit.lean`'s header records).

HOW THESE CLOSE.  Two ways, and K6c measured the line between them (the
numbers are in its section at the end of this file).  `rfl` is the twin
of Rocq's `vm_compute. reflexivity.`, the closer of
`read_bad_fd_success_rejected` in
`theories/LinuxProcessSem/Checks/Cases/Fs/ReadWrite.v`: a `check_syscall`
statement at a closed input, effect and model closes by it, through
`lookup_ca`, the arm and the fixture — in milliseconds when the request
resolves in the NULL-hint arms, and in about half a second under
`set_option maxRecDepth 32768 in` when it resolves in a MAP_FIXED arm,
the effect carries an errno return, or the statement is a `CheckOk` whose
post-state has to be computed, since at the default depth of 512 those
exceed `maxRecDepth`.  `decide` is not available at all: `check_result`
carries a `Model` and `Model` has no `DecidableEq`.  And `rfl` closes a
statement at a VARIABLE model only when the checker's answer never reads
it (`Checks/Cases/Checks/Sys/Kernel/Exit.lean` closes
`check_syscall_rejects_a_return_at_exit_over_the_real_table` so, at a
variable `m`); a refusal that turns on the ledger, which is what most of
K6b's pins state — one that holds at every ledger says more than one at
a fixture — closes by `sys_norm` after one `unfold` of the checker
and of `check_ret_only`, whose match on the effect's shape is what the
offered effect has to pass: the `sys_simp` set reads the fixture and the
post-state builders, `+decide` settles each closed `Bool` gate and
`+ground` evaluates the rest.  The macros below are that sequence, so
that a pin's proof says what kind of claim it is.  The table and
dispatcher pins go through `lookup_mmap_in`, the lookup computed once,
so that the dispatcher pins are the checker pins under one rewrite
and not a second `isDefEq` over the whole checker.

WHAT THE PROBE EVIDENCE IS.  No probe under `testing/syscall-check/`
evaluates the Lean checker: the harness runs the extracted Rocq model.
Where a pin cites a probe case, the case states the same fact of the Rocq
checker against the pinned kernel, and this file states it of the Lean
one.  A probe's grant is placed by the kernel, so its address is a
run-time value; the pins use the fixtures' addresses and the probes' own
lengths, prots and flag words, which are constants in the probes' source.

WHAT IS NOT PINNED HERE.  The ledger obligation, `arm_mmap_preserves_vm`
in `Checks/VmMapsDisjoint/Arms.lean`, is discharged by the build: an arm
with no alternative of its own in that alternation fails it by name.

WHAT MEASURES THESE PINS.  Nothing in the tree: `tools/lean_mutate.py`
builds a spec mutant and elaborates `Checks/Cases/Mm/Mmap.lean` against
it, so no mutant of the checker is ever compiled against this file.  This
paragraph stops being true when that tool lists a checker's pins beside
the spec's, and is deleted then.

The brk and munmap halves of the checker's file are C-Mm-Mmap-brk-munmap's,
and that ticket's sections go after the sentinel line at the end of this
file. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mmap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

section K6b

/-! ## K6b — `check_mmap`, `mmap_witness`, the arm -/

/-! ### The fixtures, the input and the closers

The ledgers are `Checks/Cases/Prelude.lean`'s `one_map_model` and
`Checks/Cases/Mm/Mmap.lean`'s `one_page_left_model`, `spent_budget_model`,
`adjacent_maps_model`, `three_pages_zero_budget`, `reserved_page_model`
and `noaccess_three_pages_model`, so that a checker pin and the spec pin
it answers to read the same fixture; the one below is this file's own,
because only its pins read it. -/

/-- `adjacent_maps_model`'s two live pages under an exactly-spent 8 KiB
budget: what a spanning request meets when nothing is left to charge. -/
def adjacent_maps_spent_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 0 0 8192 0 demo_sp)

/-- An `mmap` input: `a7 = 222`, the six arguments in `a0`..`a5` in
`riscv_sys_mmap`'s order (`addr, len, prot, flags, fd, offset`); no
memory.  The number is a numeral, which is how
`tools/check_lean_pin_evidence.py` reads a pin's syscall off its input. -/
def mmap_in (addr len prot flags fd off : word) : SyscallInput :=
  SyscallInput.mkInput 222 [addr, len, prot, flags, fd, off] (fun _ => none) (fun _ => none)

/-- Read a concrete `check_mmap` off and close the equation the pin
states.  `scoped`, because `Checks/Cases/Checks/Sys/Kernel/Groups.lean`
declares a `check_norm` and a `witness_norm` too, unscoped and with bodies
that unfold ITS checkers: a tactic macro is not namespaced, two
declarations of one name become a `choice` node, and Lean stops at the
first alternative that ERRORS rather than the first that fails to apply,
so in a file importing both pin modules one file's body would run on
every goal (the deep review of #1065 reproduced it in both import
orders).  Scoping keeps these inside `open` of this namespace, which
every pin here is under. -/
scoped macro "check_norm" : tactic =>
  `(tactic| (unfold check_mmap check_ret_only; sys_norm))

/-- Read a concrete `check_mmap` off at a VARIABLE model and close the
refusal the pin states.  `sys_norm` alone stops at
`(false && decide (r + n ≤ alloc_top …) && …) = true`, the placement
conjunction whose head `sys_norm` has decided false while its second
conjunct reads the model it cannot see; the three named rewrites finish
it. -/
scoped macro "check_refute_norm" : tactic =>
  `(tactic| (unfold check_mmap check_ret_only; sys_norm;
             simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]))

/-- Read a concrete `mmap_witness` off. -/
scoped macro "witness_norm" : tactic =>
  `(tactic| (unfold mmap_witness witness_errno ret_outcome; sys_norm))

set_option maxRecDepth 4096 in
/-- The lookup the dispatcher performs on an `mmap_in`, computed once:
`in_sysno` is `222` whatever the six registers hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_mmap_in (addr len prot flags fd off : word) :
    lookup_ca checked_table (bv_unsigned (mmap_in addr len prot flags fd off).in_sysno)
      = some arm_mmap :=
  lookup_ca_checked_table_mmap

/-- Read a concrete `check_syscall` at an `mmap_in` off: the lookup, the
arm's `arm_unfold`, then `check_norm`. -/
scoped macro "dispatch_norm" : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [lookup_mmap_in];
             simp only [arm_unfold]; check_norm))

/-- `dispatch_norm` for a refusal at a VARIABLE model (see `check_refute_norm`). -/
scoped macro "dispatch_refute_norm" : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [lookup_mmap_in];
             simp only [arm_unfold]; check_refute_norm))

/-- Read a concrete `syscall_spec_witness` at an `mmap_in` off. -/
scoped macro "dispatch_witness_norm" : tactic =>
  `(tactic| (unfold syscall_spec_witness table_witness; rw [lookup_mmap_in];
             simp only [arm_unfold]; witness_norm))

/-! ### Gate 1: a misaligned offset is -EINVAL before anything else -/

/-- `mmap(0, 4096, rw, PRIVATE|ANONYMOUS, -1, 1)`: riscv's wrapper answers
-EINVAL on `offset & (PAGE_SIZE - 1)` before any generic mm code runs, so
the checker accepts the errno at every model.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem misaligned_off_is_einval (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 1 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  check_norm

/-- …and admits no other errno there: -ENOMEM is `do_mmap`'s and
`__mmap_prepare`'s, neither of which the misaligned call reaches.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:do_mmap@v6.18.46 -/
theorem misaligned_off_is_not_enomem (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 1 (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckReject := by
  check_norm

/-- …nor a placement: the -EINVAL is unconditional.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem misaligned_off_admits_no_placement (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 1 (mkEffect 0x40000000 [] [(0x40000000, 4096)]) m
      = CheckReject := by
  check_norm

/-- The offset gate is read before the flags: a FILE-BACKED request with
a misaligned offset is the same -EINVAL, at every model, although the
file-backed shape is otherwise declined whole (`file_backed_is_unmodeled`
below).  The probe's call names a closed fd; `riscv_sys_mmap` answers
before `ksys_mmap_pgoff` could `fget` it.
probe: testing/syscall-check/tests/mmap_file_backed.c#conform -- misaligned -/
theorem misaligned_off_on_a_file_backed_call_is_einval (m : Model) :
    check_mmap 0 4096 1 2 999 1 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  check_norm

/-- …so the closed fd's -EBADF does not get to answer.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem misaligned_off_on_a_file_backed_call_is_not_ebadf (m : Model) :
    check_mmap 0 4096 1 2 999 1 (mkEffect (errno_ret EBADF) [] []) m = CheckReject := by
  check_norm

/-- The widest length whose page-rounding does not wrap, `2^64 - 4096`,
keeps the -EINVAL: `mmap_pglen_ok_b` is a test on `PAGE_ALIGN(len)`, and
one page below the wrap it passes.
probe: testing/syscall-check/tests/mmap_file_backed.c#conform -- page-len -/
theorem misaligned_off_with_the_widest_aligned_len_is_einval (m : Model) :
    check_mmap 0 (Z_to_bv 64 (2 ^ 64 - 4096)) 1 2 999 1 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  check_norm

/-- A misaligned offset with a length whose page-rounding wraps is
declined, whatever effect is offered: the pinned kernel answers -EINVAL
here and qemu-user answers -ENOMEM (`target_mmap` rounds the length
first), and `mmap_pglen_ok_b`'s docstring says why the spec proves
neither.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:do_mmap@v6.18.46 -/
theorem misaligned_off_with_wrapping_len_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 (Z_to_bv 64 (-1)) 3 34 mmap_fd_none 1 eff m = CheckUnmodeled := by
  check_norm

/-! ### Gate 2: a file-backed request is declined whole -/

/-- `MAP_PRIVATE` without `MAP_ANONYMOUS` is `fget(fd)` and a file mapping,
which the model does not carry: declined before the length is read,
whatever effect is offered.  The probe's `file` case is this decline
(`mmap_shapes.c`, `fail-closed -- file`); it is cited in prose because
`tools/check_lean_pin_evidence.py` classes a `= CheckUnmodeled` pin as
positive, and a positive pin may cite only a conforming case.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem file_backed_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 4096 3 2 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- …and before the length: a zero-length file-backed request is the same
decline, not the plain shape's -EINVAL, because `ksys_mmap_pgoff` resolves
the file before `do_mmap` reads `len`.
kernel: mm/mmap.c:ksys_mmap_pgoff,do_mmap@v6.18.46 -/
theorem zero_len_file_backed_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 0 3 2 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-! ### Gate 3: a zero length in the plain anonymous shape is -EINVAL -/

/-- `mmap(0, 0, rw, PRIVATE|ANONYMOUS, -1, 0)` is `do_mmap`'s
`if (!len) return -EINVAL`, accepted at every model.  The probe's `ok`
case asserts this very call after its grant.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- ok -/
theorem zero_len_is_einval (m : Model) :
    check_mmap 0 0 3 34 mmap_fd_none 0 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  check_norm

/-- …and a placement of the zero-length request is refused: nothing is
mapped by a call that fails before placing.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem zero_len_admits_no_placement (m : Model) :
    check_mmap 0 0 3 34 mmap_fd_none 0 (mkEffect 0x40000000 [] [(0x40000000, 4096)]) m
      = CheckReject := by
  check_norm

/-- …and no other errno: the length gate precedes `errno_from`.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem zero_len_is_not_enomem (m : Model) :
    check_mmap 0 0 3 34 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckReject := by
  check_norm

/-- A zero-length `MAP_FIXED` request is -EINVAL too: `MAP_FIXED` is inside
the plain anonymous shape, and `do_mmap` reads the length before the
address.
probe: testing/syscall-check/tests/mmap_shape_args.c#conform -- len0-fixed -/
theorem zero_len_fixed_is_einval (m : Model) :
    check_mmap 65536 0 0 50 mmap_fd_none 0 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  check_norm

/-- A zero-length `MAP_HUGETLB` request is outside the plain shape:
`ksys_mmap_pgoff` takes the hugetlb branch before `do_mmap` sees the
length, so the call is declined rather than answered -EINVAL.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem zero_len_hugetlb_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 0 3 262178 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-! ### The plain rw grant: `mmap(0, 4096, rw, PRIVATE|ANONYMOUS, -1, 0)` -/

/-- The page-aligned, positive placement of a free page under budget, with
the zero-fill of exactly the rounded range, is accepted; the post-model
owns the page.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- ok -/
theorem rw_grant_is_accepted :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 0x40000000 [] [(0x40000000, 4096)])
        one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0
          demo_sp)) [] := by
  check_norm

/-- -ENOMEM is admitted at every ledger, with the model unchanged: the
charge `__mmap_prepare` refuses is a run-time fact no fixture decides.
probe: testing/syscall-check/tests/errno_mmap.c#conform --mutate mmap:ret=-ENOMEM,drop-zeros -- mmap -/
theorem rw_grant_enomem_is_accepted (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckOk m [] := by
  check_norm

/-- -EBADF is refused: the anonymous arm never resolves `fd`, so no
descriptor error can come out of it.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem rw_grant_ebadf_is_refused (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect (errno_ret EBADF) [] []) m
      = CheckReject := by
  check_refute_norm

/-- -EEXIST is refused: `do_mmap` answers it only under `MAP_FIXED_NOREPLACE`
(its `find_vma_intersection` test), a flag the NULL-hint shape does not
carry, so a checker that let the NOREPLACE arms' refusal leak into the
hint arm would let it through here.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_eexist_is_refused (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect (errno_ret EEXIST) [] []) m
      = CheckReject := by
  check_refute_norm

/-- -EPERM is refused: `do_mmap`'s -EPERM needs `MAP_LOCKED` without the
privilege, or a sealed file, neither of which the anonymous rw shape has.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_eperm_is_refused (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect (errno_ret EPERM) [] []) m
      = CheckReject := by
  check_refute_norm

/-- -EAGAIN is refused: `do_mmap`'s -EAGAIN is `mlock_future_ok`'s, under
`MAP_LOCKED` alone.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_eagain_is_refused (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect (errno_ret EAGAIN) [] []) m
      = CheckReject := by
  check_refute_norm

/-- An errno that still zeroed a page is refused: a failed call maps
nothing.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem rw_grant_enomem_with_zeros_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] [(0x40000000, 4096)])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- A placement at address 0 is refused, and not by policy: a NULL hint
skips `round_hint_to_min` and goes to the searches, whose floor is
`PAGE_SIZE` top-down (`generic_get_unmapped_area_topdown`) and
`mm->mmap_base` bottom-up (`generic_get_unmapped_area`), raised to
`mmap_min_addr` by `unmapped_area` / `unmapped_area_topdown` (mm/vma.c) —
so no search returns 0 under any `vm.mmap_min_addr`, and
`security_mmap_addr` is never asked about page zero on this path.
kernel: mm/mmap.c:round_hint_to_min,generic_get_unmapped_area,generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_at_zero_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 0 [] [(0, 4096)]) one_page_left_model
      = CheckReject := by
  check_norm

/-- A misaligned placement is refused: `__get_unmapped_area` returns
-EINVAL on `offset_in_page` of the address it would hand back.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem rw_grant_misaligned_placement_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 0x40000001 [] [(0x40000001, 4096)])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- A zero-fill wider than the rounded length is refused: the grant is
`PAGE_ALIGN(len)` and no more.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_wide_zeros_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 0x40000000 [] [(0x40000000, 8192)])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- A success that zeroed nothing is refused: a fresh anonymous grant hands
back readable zeroes over its whole range, each page backed on first
touch by a zeroed folio or the zero page.
kernel: mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem rw_grant_without_zeros_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 0x40000000 [] []) one_page_left_model
      = CheckReject := by
  check_norm

/-- A placement on the page the process already owns is refused: a
NULL-hint grant lands in a gap `vm_unmapped_area` finds free.
kernel: mm/mmap.c:__get_unmapped_area,vm_unmapped_area@v6.18.46 -/
theorem rw_grant_on_an_owned_page_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 4096)]) one_page_left_model
      = CheckReject := by
  check_norm

/-- …and so is a placement on an IMAGE page: the loaded segments are VMAs
too, and the gap search skips them like any other.  This is the
`vm_reserved` half of the placement's `region_free` test, which the owned
page above does not reach.
kernel: mm/mmap.c:__get_unmapped_area,vm_unmapped_area@v6.18.46 -/
theorem rw_grant_on_an_image_page_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 4096)])
        (reserved_page_model demo_limit)
      = CheckReject := by
  check_norm

/-- A success that also reports a byte write is refused: `mmap` takes six
register arguments and hands back an address, and neither reads nor
writes user memory on the way.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem rw_grant_with_a_write_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [(0x40000000, [0])] [(0x40000000, 4096)] [] [] [])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- A NORESERVE grant on a spent budget is accepted, with the granted
interior recorded as lazily backed: `accountable_mapping` wants
`VM_NORESERVE` clear before `__mmap_prepare` charges anything.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem rw_grant_noreserve_over_a_spent_budget_is_accepted :
    check_mmap 0 4096 3 16418 mmap_fd_none 0 (mkEffect 0x40000000 [] [(0x40000000, 4096)])
        spent_budget_model
      = CheckOk (with_vm_backing [(0x40000000, 4096)] []
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 4096 0
            demo_sp))) [] := by
  check_norm

/-- A placement over a spent budget is refused: the checker's budget gate
is the spec's `choose` guard, so the only admitted answer there is -ENOMEM
(`Checks/Cases/Mm/Mmap.lean`'s `rw_grant_over_budget_is_enomem`).
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem rw_grant_over_budget_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect 0x40000000 [] [(0x40000000, 4096)])
        spent_budget_model
      = CheckReject := by
  check_norm

/-- A placement ending exactly at the model's ceiling is accepted: the
bound is on the grant's END.  `0x7fff7f7ff000 + 4096` is `demo_top`, the
`alloc_top` of every demo fixture, and the probe's `several` case injects
this very address.
probe: testing/syscall-check/tests/mmap_null_hint.c#conform --mutate mmap:ret=0x7fff7f7ff000,drop-zeros,smuggle-zeros:0x7fff7f7ff000:4096 -- several -/
theorem rw_grant_ending_at_the_ceiling_is_accepted :
    check_mmap 0 4096 3 34 mmap_fd_none 0
        (mkEffect 0x7fff7f7ff000 [] [(0x7fff7f7ff000, 4096)]) one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x7fff7f7ff000, 4096), (65536, 4096)] [] 0 0 8192
          0 demo_sp)) [] := by
  check_norm

/-- …and one page higher, starting AT the ceiling, is refused.  The bound
is the model's, not Linux's: `State.alloc_top` keeps every grant below
the stack's `RLIMIT_STACK` reach so that a symbolic `sp` stays one atom,
while `__get_unmapped_area` bounds a placement by `TASK_SIZE` alone — the
legacy bottom-up layout, or the top-down search's fallback when nothing
fits under `mmap_base`, can place there.  What that refusal costs on a
real trace is `bugs/grants-into-the-stack-band.md`'s.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem rw_grant_starting_at_the_ceiling_is_refused :
    check_mmap 0 4096 3 34 mmap_fd_none 0
        (mkEffect 0x7fff7f800000 [] [(0x7fff7f800000, 4096)]) one_page_left_model
      = CheckReject := by
  check_norm

/-! ### The PROT_NONE reservation: `mmap(0, 4096, PROT_NONE, PRIVATE|ANONYMOUS, fd, 0)` -/

/-- A fresh inaccessible reservation is accepted with the unmap of exactly
its range and no zero-fill; the post-model owns the page and lists it
inaccessible.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- protnone -/
theorem noaccess_grant_is_accepted :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
          [(0x40000000, 4096)] 0 0 8192 0 demo_sp)) [] := by
  check_norm

/-- …and the same placement reported as a zero-fill is refused: a
PROT_NONE mapping exposes no bytes, so the spec's PROT_NONE arm takes an
empty zero list.
model: the zero list records bytes the executor may read, and a range
that faults on every access offers none -/
theorem noaccess_grant_with_zeros_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0 (mkEffect 0x40000000 [] [(0x40000000, 4096)])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- …and one reported with no unmap at all is refused: the reservation
erases whatever mutable bytes the range held.
model: the unmap list is how a grant tells the executor its range stopped
being readable, and the spec's PROT_NONE arm requires exactly the rounded
range there -/
theorem noaccess_grant_without_unmap_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0 (mkEffect 0x40000000 [] []) one_page_left_model
      = CheckReject := by
  check_norm

/-- A PROT_NONE reservation is free of charge: `accountable_mapping` wants
`VM_WRITE`, so a spent budget still admits it.
kernel: mm/vma.c:accountable_mapping,__mmap_prepare@v6.18.46 -/
theorem noaccess_grant_over_a_spent_budget_is_accepted :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) spent_budget_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
          [(0x40000000, 4096)] 0 0 4096 0 demo_sp)) [] := by
  check_norm

/-- Any `fd` is fine on the anonymous arm: the probe passes `0` in `a4`,
and it is never read.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- protnone-fd -/
theorem noaccess_grant_ignores_fd :
    check_mmap 0 4096 0 34 0 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
          [(0x40000000, 4096)] 0 0 8192 0 demo_sp)) [] := by
  check_norm

/-- …and so is the rw arm's: `fd = 3` on `MAP_ANONYMOUS` is never fetched
(`ksys_mmap_pgoff` calls `fget` only under `!(flags & MAP_ANONYMOUS)`), so
the grant is read exactly as with `-1`.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem rw_grant_ignores_fd :
    check_mmap 0 4096 3 34 3 0 (mkEffect 0x40000000 [] [(0x40000000, 4096)]) one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0
          demo_sp)) [] := by
  check_norm

/-- A NON-NULL hint without `MAP_FIXED` is a hint and nothing more: the
searches take it when the range is free and look elsewhere when it is not
(`generic_get_unmapped_area_topdown`'s `if (addr)` block), so the arm reads
`addr` as no gate and admits a placement anywhere the NULL hint would.
Here the hint names the owned page and the grant lands elsewhere.  Rocq:
`mmap_nonnull_hint_low_grant_admitted`.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,generic_get_unmapped_area@v6.18.46 -/
theorem rw_grant_with_a_hint_is_accepted :
    check_mmap 65536 4096 3 34 mmap_fd_none 0 (mkEffect 0x40000000 [] [(0x40000000, 4096)])
        one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0
          demo_sp)) [] := by
  check_norm

/-- …and the PROT_NONE arm reads a hint the same way.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,generic_get_unmapped_area@v6.18.46 -/
theorem noaccess_grant_with_a_hint_is_accepted :
    check_mmap 65536 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
          [(0x40000000, 4096)] 0 0 8192 0 demo_sp)) [] := by
  check_norm

/-- …and so is an open one: `ksys_mmap_pgoff` resolves a file only inside
`if (!(flags & MAP_ANONYMOUS))`.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem noaccess_grant_ignores_an_open_fd :
    check_mmap 0 4096 0 34 3 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
          [(0x40000000, 4096)] 0 0 8192 0 demo_sp)) [] := by
  check_norm

/-- -ENOMEM is admitted at every ledger with nothing unmapped: the
reservation is uncharged, but `may_expand_vm`'s `RLIMIT_AS` test and the
VMA allocation can still fail it.  The probe's call is two pages.
probe: testing/syscall-check/tests/noaccess_vm.c#conform --mutate mmap:ret=-ENOMEM,drop-unmaps -- fresh-stop -/
theorem noaccess_grant_enomem_is_accepted (m : Model) :
    check_mmap 0 8192 0 34 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckOk m [] := by
  check_norm

/-- …and an errno that still unmapped the range is refused: a NULL-hint
request gathers nothing, so a failed one erases nothing.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem noaccess_grant_enomem_with_unmap_is_refused :
    check_mmap 0 8192 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(0x40000000, 8192)] [] [])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- -EBADF is refused on the PROT_NONE arm as on the rw one: no `fd` is
resolved.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem noaccess_grant_ebadf_is_refused (m : Model) :
    check_mmap 0 4096 0 34 mmap_fd_none 0 (mkEffect (errno_ret EBADF) [] []) m
      = CheckReject := by
  check_refute_norm

/-- A PROT_NONE placement at address 0 is refused for the reason the rw one
is: the searches' floors (`PAGE_SIZE`, `mm->mmap_base`, `mmap_min_addr`)
never yield 0, for a reservation as for a grant.
kernel: mm/mmap.c:round_hint_to_min,generic_get_unmapped_area,generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem noaccess_grant_at_zero_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0 (SyscallEffect.mkEffectU 0 [] [] [(0, 4096)] [] [])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- A misaligned PROT_NONE placement is refused: `__get_unmapped_area`'s
`offset_in_page` test reads the address it would hand back, whatever the
protection.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noaccess_grant_misaligned_placement_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000001 [] [] [(0x40000001, 4096)] [] []) one_page_left_model
      = CheckReject := by
  check_norm

/-- A PROT_NONE placement on the owned page is refused: the gap search is
the same one the rw grant takes.
kernel: mm/mmap.c:__get_unmapped_area,vm_unmapped_area@v6.18.46 -/
theorem noaccess_grant_on_an_owned_page_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) one_page_left_model
      = CheckReject := by
  check_norm

/-- …and on an image page too: the `vm_reserved` half of the test.
kernel: mm/mmap.c:__get_unmapped_area,vm_unmapped_area@v6.18.46 -/
theorem noaccess_grant_on_an_image_page_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) (reserved_page_model demo_limit)
      = CheckReject := by
  check_norm

/-- An unmap wider than the rounded length is refused: the reservation is
`PAGE_ALIGN(len)` and no more.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noaccess_grant_wide_unmap_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 8192)] [] []) one_page_left_model
      = CheckReject := by
  check_norm

/-- A reservation that also reports a byte read is refused: `mmap` reads
no user memory.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem noaccess_grant_with_a_copyin_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [(0x40000000, 1)])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- A PROT_NONE reservation ending exactly at the model's ceiling is
accepted, as the rw grant is: the bound is on the END.
model: `State.alloc_top` is an inclusive bound on a grant's end, read by
the PROT_NONE arm as by the rw one -/
theorem noaccess_grant_ending_at_the_ceiling_is_accepted :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x7fff7f7ff000 [] [] [(0x7fff7f7ff000, 4096)] [] [])
        one_page_left_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x7fff7f7ff000, 4096), (65536, 4096)]
          [(0x7fff7f7ff000, 4096)] 0 0 8192 0 demo_sp)) [] := by
  check_norm

/-- …and one page higher is refused, for the reason
`rw_grant_starting_at_the_ceiling_is_refused` gives.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem noaccess_grant_starting_at_the_ceiling_is_refused :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x7fff7f800000 [] [] [(0x7fff7f800000, 4096)] [] [])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- PROT_NONE | MAP_NORESERVE: the same reservation, and the bit still
selects the lazy ledger — the post-model records the interior as lazy
although a PROT_NONE range is never charged.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noaccess_noreserve_grant_records_lazy :
    check_mmap 0 4096 0 16418 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) one_map_model
      = CheckOk (with_vm_backing [(0x40000000, 4096)] []
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
            [(0x40000000, 4096)] 0 0 demo_limit 0 demo_sp))) [] := by
  check_norm

/-! ### MAP_FIXED, contained: the request inside one owned entry -/

/-- The rw commit of the live page: accepted at its own address with the
zero-fill of exactly the range, and the ledger is what it was — the
page was owned already.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- fixed-rw -/
theorem fixed_rw_contained_is_accepted :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 4096)]) one_map_model
      = CheckOk one_map_model [] := by
  check_norm

/-- …and the zero list is load-bearing on the contained arm too: the same
commit reporting no zeroes is refused — the replacement is a fresh
anonymous VMA (`__mmap_new_vma`) whose pages fault in zero-filled
(`do_anonymous_page`), so the committed bytes ARE zero.  The harness twin
is `mmap_shapes.c`'s `reject --mutate mmap#2:drop-zeros -- fixed-rw`
case; a positive pin cannot cite a `reject` case, so the kernel reading
stands here.
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma; mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem fixed_rw_contained_without_zeros_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect 65536 [] []) one_map_model
      = CheckReject := by
  check_norm

/-- …and so is a zero list wider than the request: the new VMA spans
`[addr, addr + PAGE_ALIGN(len))` and nothing more (`__mmap_prepare` sets
`map->end` from the request), so the commit exposes EXACTLY the range it
was asked for, not the whole owner.  Rocq:
`mmap_fixed_rw_wider_zero_fill_rejected`; harness twin `mmap_shapes.c`'s
`reject --mutate mmap#2:grow-zeros:4096 -- fixed-rw` case.
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma; mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem fixed_rw_contained_wide_zeros_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 8192)]) one_map_model
      = CheckReject := by
  check_norm

/-- -EEXIST at a MAP_FIXED commit is refused: `MAP_FIXED` replaces, it is
`MAP_FIXED_NOREPLACE` that answers -EEXIST over an occupied range
(`do_mmap`'s `find_vma_intersection` test), and 50 does not carry that
bit.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_rw_contained_eexist_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect (errno_ret EEXIST) [] []) one_map_model
      = CheckReject := by
  check_norm

/-- The contained commit charges the DELTA, which over an accounted page is
zero: a spent budget admits it.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_contained_over_a_spent_budget_is_accepted :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 4096)])
        spent_budget_model
      = CheckOk spent_budget_model [] := by
  check_norm

/-- A MAP_FIXED failure that left the range in place: -ENOMEM with nothing
unmapped, the model unchanged.
probe: testing/syscall-check/tests/mmap_shapes.c#conform --mutate mmap#2:ret=-ENOMEM,drop-zeros -- fixed-rw-stop -/
theorem fixed_rw_contained_enomem_is_accepted :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckOk one_map_model [] := by
  check_norm

/-- …and the DESTRUCTIVE failure: -ENOMEM with the range unmapped, the page
gone from the ledger — once `vms_clean_up_area` has torn the range down,
`vms_abort_munmap_vmas` writes NULL over it rather than restoring it
(before the teardown, with `clear_ptes` still set, it `reattach_vmas`
instead, which is the in-place failure above).
probe: testing/syscall-check/tests/mmap_shapes.c#conform --mutate mmap#2:ret=-ENOMEM,drop-zeros,smuggle-unmap:a0:4096 -- fixed-rw-stop -/
theorem fixed_rw_contained_destructive_enomem_is_accepted :
    check_mmap 65536 4096 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- The destructive failure in the MIDDLE of a three-page owner splits it:
`vms_gather_munmap_vmas` cuts the owner at the request's start and end
(`__split_vma`) before the teardown, and the abort's NULL store covers
only `[vms->start, vms->end)`, so both remnants survive it — on both
ledgers here, the pages being owned and inaccessible.  This is the one
pin whose `maps_subtract` leaves a remnant on EACH side of the request.
Rocq: `mmap_fixed_rw_destructive_failure_leaves_a_hole`.
kernel: mm/vma.c:vms_gather_munmap_vmas,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_destructive_enomem_splits_the_owner :
    check_mmap 69632 4096 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] [])
        three_pages_zero_budget
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (73728, 4096)]
          [(65536, 4096), (73728, 4096)] 0 0 0 0 demo_sp)) [] := by
  check_norm

/-- A destructive failure that unmapped MORE than the request is refused:
the abort covers `[vms->start, vms->end)` and nothing beyond.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_contained_wide_destruction_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- A failure that still zeroed the range is refused: a failed commit
exposes nothing.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_contained_enomem_with_zeros_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] [(65536, 4096)])
        one_map_model
      = CheckReject := by
  check_norm

/-- A success at another address is refused: MAP_FIXED hands back the
address it was given — the searches' `if (flags & MAP_FIXED) return addr`.
kernel: mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown@v6.18.46 -/
theorem fixed_rw_contained_other_return_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect 69632 [] [(65536, 4096)]) one_map_model
      = CheckReject := by
  check_norm

/-- A success that left a hole instead of zeroes is refused: the rw
replacement exposes readable zeroes, it does not unmap — `__mmap_prepare`
tears the old range down and `__mmap_new_vma` puts the new VMA over all
of it, so the rw arm's effect shape has an empty unmap list.
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma@v6.18.46 -/
theorem fixed_rw_contained_success_with_unmap_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- A success that also reports a byte write is refused, on the fixed arm
as on the NULL-hint one.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem fixed_rw_contained_with_a_write_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [(65536, [0])] [(65536, 4096)] [] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- -EINVAL is refused at an aligned, contained MAP_FIXED request: every
-EINVAL test of the path — the offset, the zero length, `offset_in_page`
of the address — has passed, and the errno the arm admits is -ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_contained_einval_is_refused :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckReject := by
  check_norm

/-- The rw commit of a RESERVED page charges that page: over an owned but
inaccessible range `vms->nr_accounted` is zero and `__mmap_prepare`
charges the whole request.  With room in the budget the commit is
accepted, the page leaving `vm_noaccess` and the ledger otherwise as it
was.
kernel: mm/vma.c:__mmap_prepare,accountable_mapping@v6.18.46 -/
theorem fixed_rw_commit_of_a_reserved_page_is_accepted :
    check_mmap 69632 4096 3 50 mmap_fd_none 0 (mkEffect 69632 [] [(69632, 4096)])
        (noaccess_three_pages_model demo_limit)
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
          0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- A PROT_NONE MAP_FIXED over a page that is ALREADY inaccessible re-cuts
the old no-access entry around the request before consing the new one:
Linux splits the VMA it meets (`vms_gather_munmap_vmas`) and puts the new
one in the gap, and the ledger's `maps_subtract` is that split.  Every
other contained PROT_NONE pin reads a fixture with an empty `vm_noaccess`,
where the subtraction is the identity; this one is where dropping it would
show.
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_contained_over_an_inaccessible_page_recuts_it :
    check_mmap 69632 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 69632 [] [] [(69632, 4096)] [] [])
        (noaccess_three_pages_model demo_limit)
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)]
          [(69632, 4096), (65536, 4096), (73728, 4096)] 0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- Two pages lazily reserved, the first of them materialized, under the
demo budget: what a replacement must FORGET.  `fixture` leaves the backing
ledgers empty, so no other checker pin can tell `with_mmap_replacement`
from `with_mmap_backing`. -/
def lazy_materialized_model : Model :=
  with_vm_backing [(65536, 8192)] [65536, 69632]
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp))

/-- A PROT_NONE replacement of the first page forgets its lazy entry and its
materialization and keeps the second page's: `vms_gather_munmap_vmas`
splits the owner and the replaced half goes with it, backing and all.
Rocq: `mmap_fixed_noaccess_replacement_forgets_replaced_backing`.
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas,__mmap_new_vma@v6.18.46 -/
theorem fixed_noaccess_contained_forgets_the_replaced_backing :
    check_mmap 65536 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) lazy_materialized_model
      = CheckOk (with_vm_backing [(69632, 4096)] [69632]
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 4096)] 0 0 demo_limit 0
            demo_sp))) [] := by
  check_norm

/-- …and the rw replacement forgets the same half.
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas,__mmap_new_vma@v6.18.46 -/
theorem fixed_rw_contained_forgets_the_replaced_backing :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 4096)])
        lazy_materialized_model
      = CheckOk (with_vm_backing [(69632, 4096)] [69632]
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp))) [] := by
  check_norm

/-- …and over a budget of zero the same commit is refused: the checker's
`mmap_fixed_rw_budget_ok` is the spec's gate on the post-state, which
`Checks/Cases/Mm/Mmap.lean`'s `fixed_rw_commit_over_budget_iff` pins to
the two errno resolutions.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_commit_of_a_reserved_page_over_a_spent_budget_is_refused :
    check_mmap 69632 4096 3 50 mmap_fd_none 0 (mkEffect 69632 [] [(69632, 4096)])
        three_pages_zero_budget
      = CheckReject := by
  check_norm

/-- …leaving the errno with the range in place…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_commit_of_a_reserved_page_over_a_spent_budget_enomem_is_accepted :
    check_mmap 69632 4096 3 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] [])
        three_pages_zero_budget
      = CheckOk three_pages_zero_budget [] := by
  check_norm

/-- …while the NORESERVE spelling of the commit is lazy and accepted
under that budget, the committed page recorded as lazily backed.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem fixed_rw_noreserve_commit_of_a_reserved_page_over_a_spent_budget_is_accepted :
    check_mmap 69632 4096 3 16434 mmap_fd_none 0 (mkEffect 69632 [] [(69632, 4096)])
        three_pages_zero_budget
      = CheckOk (with_vm_backing [(69632, 4096)] []
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
            0 0 0 0 demo_sp))) [] := by
  check_norm

/-- The PROT_NONE guard punched into the live page: accepted with the
unmap of exactly the range, the page now listed inaccessible.
probe: testing/syscall-check/tests/noaccess_vm.c#conform -- fixed -/
theorem fixed_noaccess_contained_is_accepted :
    check_mmap 65536 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 demo_limit 0
          demo_sp)) [] := by
  check_norm

/-- …and its destructive failure removes the page from both ledgers.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_contained_destructive_enomem_is_accepted :
    check_mmap 65536 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- A PROT_NONE guard reported as a zero-fill is refused: it exposes no
bytes.
model: the zero list records bytes the executor may read, and the spec's
PROT_NONE arms take an empty one -/
theorem fixed_noaccess_contained_with_zeros_is_refused :
    check_mmap 65536 4096 0 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 4096)]) one_map_model
      = CheckReject := by
  check_norm

/-- The guard's non-destructive failure: -ENOMEM with the page in place.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_noaccess_contained_enomem_is_accepted :
    check_mmap 65536 4096 0 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckOk one_map_model [] := by
  check_norm

/-- A destructive failure that unmapped MORE than the request is refused
on the PROT_NONE arm as on the rw one.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_contained_wide_destruction_is_refused :
    check_mmap 65536 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- A guard installed at another address is refused: MAP_FIXED hands back
the address it was given.
kernel: mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown@v6.18.46 -/
theorem fixed_noaccess_contained_other_return_is_refused :
    check_mmap 65536 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 69632 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- A guard reported with no unmap is refused: the overwrite erases the
old page's bytes.
model: the unmap list is how a grant tells the executor its range stopped
being readable, and the spec's PROT_NONE arms require exactly the
request there -/
theorem fixed_noaccess_contained_without_unmap_is_refused :
    check_mmap 65536 4096 0 50 mmap_fd_none 0 (mkEffect 65536 [] []) one_map_model
      = CheckReject := by
  check_norm

/-! ### MAP_FIXED, free and spanning -/

/-- MAP_FIXED over territory nothing owns is an ordinary grant at the
named address.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- fixed-rw-fresh -/
theorem fixed_rw_free_is_accepted :
    check_mmap 0x40000000 4096 3 50 mmap_fd_none 0
        (mkEffect 0x40000000 [] [(0x40000000, 4096)]) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0
          demo_limit 0 demo_sp)) [] := by
  check_norm

/-- …charged in full, so a spent budget refuses the placement and leaves
-ENOMEM.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_free_over_a_spent_budget_is_refused :
    check_mmap 0x40000000 4096 3 50 mmap_fd_none 0
        (mkEffect 0x40000000 [] [(0x40000000, 4096)]) spent_budget_model
      = CheckReject := by
  check_norm

/-- A free-range MAP_FIXED failure unmaps nothing: `__mmap_prepare` finds
no VMA under the request, so nothing is gathered and
`vms_abort_munmap_vmas` returns at its `!vms->nr_pages` test; a
destructive report is refused.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_free_destructive_enomem_is_refused :
    check_mmap 0x40000000 4096 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(0x40000000, 4096)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- …its plain failure is admitted with the ledger unchanged…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_free_enomem_is_accepted :
    check_mmap 0x40000000 4096 3 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckOk one_map_model [] := by
  check_norm

/-- …a success at another address is refused…
kernel: mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown@v6.18.46 -/
theorem fixed_rw_free_other_return_is_refused :
    check_mmap 0x40000000 4096 3 50 mmap_fd_none 0
        (mkEffect 0x40001000 [] [(0x40000000, 4096)]) one_map_model
      = CheckReject := by
  check_norm

/-- …and so is one that zeroed nothing: the fresh range reads back zero.
kernel: mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem fixed_rw_free_without_zeros_is_refused :
    check_mmap 0x40000000 4096 3 50 mmap_fd_none 0 (mkEffect 0x40000000 [] []) one_map_model
      = CheckReject := by
  check_norm

/-- The NORESERVE spelling of the free-range grant ignores the budget and
records the range as lazily backed.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem fixed_rw_free_noreserve_over_a_spent_budget_is_accepted :
    check_mmap 0x40000000 4096 3 16434 mmap_fd_none 0
        (mkEffect 0x40000000 [] [(0x40000000, 4096)]) spent_budget_model
      = CheckOk (with_vm_backing [(0x40000000, 4096)] []
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 4096 0
            demo_sp))) [] := by
  check_norm

/-- A free-range MAP_FIXED grant ending exactly at the model's ceiling is
accepted: the fixed arms read the same inclusive bound on the END as the
NULL-hint ones.
model: `State.alloc_top` is an inclusive bound on a grant's end, read by
the MAP_FIXED arms as by the NULL-hint ones -/
theorem fixed_rw_ending_at_the_ceiling_is_accepted :
    check_mmap 0x7fff7f7ff000 4096 3 50 mmap_fd_none 0
        (mkEffect 0x7fff7f7ff000 [] [(0x7fff7f7ff000, 4096)]) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x7fff7f7ff000, 4096), (65536, 4096)] [] 0 0
          demo_limit 0 demo_sp)) [] := by
  check_norm

/-- PROT_NONE MAP_FIXED over free territory is an ordinary reservation at
the named address.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- fixed-none-fresh -/
theorem fixed_noaccess_free_is_accepted :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
          [(0x40000000, 4096)] 0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- …free of charge, so a spent budget admits it too.
kernel: mm/vma.c:accountable_mapping,__mmap_prepare@v6.18.46 -/
theorem fixed_noaccess_free_over_a_spent_budget_is_accepted :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] []) spent_budget_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)]
          [(0x40000000, 4096)] 0 0 4096 0 demo_sp)) [] := by
  check_norm

/-- …and ending exactly at the model's ceiling.
model: `State.alloc_top` is an inclusive bound on a grant's end, read by
the MAP_FIXED arms as by the NULL-hint ones -/
theorem fixed_noaccess_ending_at_the_ceiling_is_accepted :
    check_mmap 0x7fff7f7ff000 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x7fff7f7ff000 [] [] [(0x7fff7f7ff000, 4096)] [] []) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(0x7fff7f7ff000, 4096), (65536, 4096)]
          [(0x7fff7f7ff000, 4096)] 0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- Its plain failure is admitted with the ledger unchanged…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_noaccess_free_enomem_is_accepted :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckOk one_map_model [] := by
  check_norm

/-- …a destructive report is refused, there being no VMA under the request
for `__mmap_prepare` to gather and nothing for `vms_abort_munmap_vmas` to
undo…
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_free_destructive_enomem_is_refused :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(0x40000000, 4096)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- …-EBADF is refused, no `fd` being resolved…
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem fixed_noaccess_free_ebadf_is_refused :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0 (mkEffect (errno_ret EBADF) [] []) one_map_model
      = CheckReject := by
  check_norm

/-- …a success at another address is refused…
kernel: mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown@v6.18.46 -/
theorem fixed_noaccess_free_other_return_is_refused :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40001000 [] [] [(0x40000000, 4096)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- …one with no unmap is refused…
model: the unmap list is how a grant tells the executor its range stopped
being readable, and the spec's PROT_NONE arms require exactly the
request there -/
theorem fixed_noaccess_free_without_unmap_is_refused :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0 (mkEffect 0x40000000 [] []) one_map_model
      = CheckReject := by
  check_norm

/-- …one whose unmap is wider than the rounded request is refused…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_noaccess_free_wide_unmap_is_refused :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 8192)] [] []) one_map_model
      = CheckReject := by
  check_norm

/-- …one reported as a zero-fill is refused: a PROT_NONE range exposes no
bytes…
model: the zero list records bytes the executor may read, and the spec's
PROT_NONE arms take an empty one -/
theorem fixed_noaccess_free_with_zeros_is_refused :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0
        (mkEffect 0x40000000 [] [(0x40000000, 4096)]) one_map_model
      = CheckReject := by
  check_norm

/-- …and one that also reports a byte read is refused: `mmap` reads no
user memory.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem fixed_noaccess_free_with_a_copyin_is_refused :
    check_mmap 0x40000000 4096 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [(0x40000000, 1)])
        one_map_model
      = CheckReject := by
  check_norm

/-- …and the rw spelling of the free-range grant refuses the copyin the same
way.  The free rw arm has no other shape refusal, so a checker that let a
sixth list through on it would show here and nowhere else.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem fixed_rw_free_with_a_copyin_is_refused :
    check_mmap 0x40000000 4096 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 0x40000000 [] [(0x40000000, 4096)] [] [] [(0x40000000, 1)])
        one_map_model
      = CheckReject := by
  check_norm

/-- A request covered by two ADJACENT entries is spanning, not contained,
and is replaced whole: one entry over the request, zeroes over all of it.
probe: testing/syscall-check/tests/mmap_fixed_span.c#conform -- span -/
theorem fixed_rw_span_is_accepted :
    check_mmap 65536 8192 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 8192)])
        adjacent_maps_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp))
          [] := by
  check_norm

/-- …its destructive failure removes both entries…
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_span_destructive_enomem_is_accepted :
    check_mmap 65536 8192 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] []) adjacent_maps_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- …and a success that zeroed only the first page is refused: the
replacement exposes the whole rounded request, every page of it
zero-filled on first touch.
kernel: mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem fixed_rw_span_narrow_zeros_is_refused :
    check_mmap 65536 8192 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 4096)])
        adjacent_maps_model
      = CheckReject := by
  check_norm

/-- …its non-destructive failure keeps both entries…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_span_enomem_is_accepted :
    check_mmap 65536 8192 3 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) adjacent_maps_model
      = CheckOk adjacent_maps_model [] := by
  check_norm

/-- …a destructive failure that unmapped only the first page is refused:
the abort covers `[vms->start, vms->end)` whole…
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_span_partial_destruction_is_refused :
    check_mmap 65536 8192 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) adjacent_maps_model
      = CheckReject := by
  check_norm

/-- …a success at another address is refused…
kernel: mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown@v6.18.46 -/
theorem fixed_rw_span_other_return_is_refused :
    check_mmap 65536 8192 3 50 mmap_fd_none 0 (mkEffect 69632 [] [(65536, 8192)])
        adjacent_maps_model
      = CheckReject := by
  check_norm

/-- …and a success that left a hole beside its zeroes is refused: the rw
replacement keeps the range mapped and readable (`__mmap_prepare` then
`__mmap_new_vma` over the whole request), so the rw arms' effect shape
has an empty unmap list.
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma@v6.18.46 -/
theorem fixed_rw_span_success_with_unmap_is_refused :
    check_mmap 65536 8192 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [(65536, 8192)] [(65536, 8192)] [] []) adjacent_maps_model
      = CheckReject := by
  check_norm

/-- A request meeting one owned page and one free page is spanning too,
and the part that met nothing is newly owned: one entry over the request.
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas@v6.18.46 -/
theorem fixed_rw_span_past_an_owned_page_is_accepted :
    check_mmap 65536 12288 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 12288)]) one_map_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 demo_limit 0 demo_sp))
          [] := by
  check_norm

/-- …and that part is CHARGED — `map->charged = map->pglen - vms->nr_accounted`
counts only the accounted pages the gather detached — so under a budget
one page short of it the placement is refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_span_over_budget_is_refused :
    check_mmap 65536 12288 3 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 12288)])
        one_page_left_model
      = CheckReject := by
  check_norm

/-- …leaving the errno with the range in place.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_span_over_budget_enomem_is_accepted :
    check_mmap 65536 12288 3 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] [])
        one_page_left_model
      = CheckOk one_page_left_model [] := by
  check_norm

/-- A request covering the second of two adjacent pages and the free page
above it keeps the first as a remnant: the entries it meets are re-cut
around it, not removed.
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas@v6.18.46 -/
theorem fixed_rw_span_keeps_the_remnant :
    check_mmap 69632 8192 3 50 mmap_fd_none 0 (mkEffect 69632 [] [(69632, 8192)])
        adjacent_maps_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(69632, 8192), (65536, 4096)] [] 0 0 demo_limit 0
          demo_sp)) [] := by
  check_norm

/-- …and so does its destructive failure: `vms_abort_munmap_vmas` writes
NULL over the request and nothing beyond, so the split remnant survives.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_span_destruction_keeps_the_remnant :
    check_mmap 69632 8192 3 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 8192)] [] []) adjacent_maps_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 demo_limit 0 demo_sp))
          [] := by
  check_norm

/-- The PROT_NONE spelling of the same replacement: owned and inaccessible
whole.
probe: testing/syscall-check/tests/mmap_fixed_span.c#conform -- span-none -/
theorem fixed_noaccess_span_is_accepted :
    check_mmap 65536 8192 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 8192)] [] []) adjacent_maps_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 demo_limit 0
          demo_sp)) [] := by
  check_norm

/-- …free of charge, so it is accepted over an exactly-spent budget too.
kernel: mm/vma.c:accountable_mapping,__mmap_prepare@v6.18.46 -/
theorem fixed_noaccess_span_over_a_spent_budget_is_accepted :
    check_mmap 65536 8192 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 8192)] [] []) adjacent_maps_spent_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0
          demo_sp)) [] := by
  check_norm

/-- Its non-destructive failure keeps both entries…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_noaccess_span_enomem_is_accepted :
    check_mmap 65536 8192 0 50 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) adjacent_maps_model
      = CheckOk adjacent_maps_model [] := by
  check_norm

/-- …its destructive failure removes both…
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_span_destructive_enomem_is_accepted :
    check_mmap 65536 8192 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] []) adjacent_maps_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) [] := by
  check_norm

/-- …a destructive failure that unmapped only the first page is refused…
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_span_partial_destruction_is_refused :
    check_mmap 65536 8192 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) adjacent_maps_model
      = CheckReject := by
  check_norm

/-- …a success at another address is refused…
kernel: mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown@v6.18.46 -/
theorem fixed_noaccess_span_other_return_is_refused :
    check_mmap 65536 8192 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 69632 [] [] [(65536, 8192)] [] []) adjacent_maps_model
      = CheckReject := by
  check_norm

/-- …a success that unmapped only the first page is refused: the
replacement covers the rounded request whole…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_noaccess_span_narrow_unmap_is_refused :
    check_mmap 65536 8192 0 50 mmap_fd_none 0
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) adjacent_maps_model
      = CheckReject := by
  check_norm

/-- …and one reported as a zero-fill is refused: a PROT_NONE range
exposes no bytes.
model: the zero list records bytes the executor may read, and the spec's
PROT_NONE arms take an empty one -/
theorem fixed_noaccess_span_with_zeros_is_refused :
    check_mmap 65536 8192 0 50 mmap_fd_none 0 (mkEffect 65536 [] [(65536, 8192)]) adjacent_maps_model
      = CheckReject := by
  check_norm

/-! ### MAP_FIXED, the gates before the ledger -/

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_wrapping_end_is_unmodeled (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)) 3 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- The page-rounded length wraps to zero.
Linux returns -ENOMEM before `__get_unmapped_area` tests the address.
The checker rejects -EINVAL for this length wrap.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_wrapping_misaligned_is_not_einval (m : Model) :
    check_mmap 0x1001 (Z_to_bv 64 (-1)) 0 50 mmap_fd_none 0 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckReject := by
  check_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_wrapping_end_is_unmodeled (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)) 0 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- …and the rw spelling of the misaligned wrapping request refuses
-EINVAL.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_rw_wrapping_misaligned_is_not_einval (m : Model) :
    check_mmap 0x1001 (Z_to_bv 64 (-1)) 3 50 mmap_fd_none 0 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckReject := by
  check_norm

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_misaligned_wrapping_range_declines_enomem (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 3 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_misaligned_wrapping_range_declines_qemu_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 3 50 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_in_the_error_band_declines_the_shared_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) 4096 3 50 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_misaligned_wrapping_range_declines_enomem (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 0 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_misaligned_wrapping_range_declines_qemu_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 0 50 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_in_the_error_band_declines_the_shared_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) 4096 0 50 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- A MAP_FIXED request ending above the model's ceiling but inside the
address space is declined whatever effect is offered: Linux would place it
(the bound in `__get_unmapped_area` is `TASK_SIZE`), the model stops at
the stack's reach.  `demo_top` is the fixtures' `alloc_top`.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_above_the_ceiling_is_unmodeled (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 demo_top) 4096 0 50 mmap_fd_none 0 eff one_map_model
      = CheckUnmodeled := by
  check_norm

/-- …and the rw arm declines the same request.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem fixed_rw_above_the_ceiling_is_unmodeled (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 demo_top) 4096 3 50 mmap_fd_none 0 eff one_map_model
      = CheckUnmodeled := by
  check_norm

/-- A misaligned MAP_FIXED address under the ceiling is -EINVAL:
`__get_unmapped_area`'s `offset_in_page(addr)`.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_misaligned_is_einval :
    check_mmap 0x1001 4096 0 50 mmap_fd_none 0 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] := by
  check_norm

/-- …on the rw arm as on the PROT_NONE one…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_misaligned_is_einval :
    check_mmap 0x1001 4096 3 50 mmap_fd_none 0 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] := by
  check_norm

/-- …and a success at the misaligned address is refused: the -EINVAL is
deterministic once the address-space tests have passed.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_misaligned_success_is_refused :
    check_mmap 0x1001 4096 3 50 mmap_fd_none 0 (mkEffect 0x1001 [] [(0x1001, 4096)]) one_map_model
      = CheckReject := by
  check_norm

/-- …but the ceiling is read first: a misaligned address above it is
declined, not answered -EINVAL.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_misaligned_above_the_ceiling_is_unmodeled (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (demo_top + 1)) 4096 0 50 mmap_fd_none 0 eff one_map_model
      = CheckUnmodeled := by
  check_norm

/-- …on the rw arm too.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_misaligned_above_the_ceiling_is_unmodeled (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (demo_top + 1)) 4096 3 50 mmap_fd_none 0 eff one_map_model
      = CheckUnmodeled := by
  check_norm

/-- MAP_FIXED at address 0 is declined: `security_mmap_addr` is
`__get_unmapped_area`'s last test, and its baseline `cap_mmap_addr`
answers -EPERM below `dac_mmap_min_addr` — whose default is 4096, which
the `vm.mmap_min_addr` sysctl moves and CAP_SYS_RAWIO overrides — a policy
the model does not carry.  Above zero the arms answer the default policy
alone; the `bugs/` entry #895 landed on the day branch,
`mmap-fixed-below-mmap-min-addr-admits-default-policy-alone`, records what
that costs.
kernel: mm/mmap.c:__get_unmapped_area; security/security.c:security_mmap_addr; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem fixed_at_zero_is_unmodeled (eff : SyscallEffect) :
    check_mmap 0 4096 3 50 mmap_fd_none 0 eff one_map_model = CheckUnmodeled := by
  check_norm

/-- …and the PROT_NONE arm declines address 0 the same way.
kernel: mm/mmap.c:__get_unmapped_area; security/security.c:security_mmap_addr; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem fixed_noaccess_at_zero_is_unmodeled (eff : SyscallEffect) :
    check_mmap 0 4096 0 50 mmap_fd_none 0 eff one_map_model = CheckUnmodeled := by
  check_norm

/-- A MAP_FIXED request over an IMAGE page is outside the three
resolutions and declined: Linux would gather and replace the page, the
model does not replace what `vm_reserved` holds.
kernel: mm/vma.c:vms_gather_munmap_vmas@v6.18.46 -/
theorem fixed_over_the_image_is_unmodeled (eff : SyscallEffect) :
    check_mmap 65536 4096 3 50 mmap_fd_none 0 eff (reserved_page_model demo_limit)
      = CheckUnmodeled := by
  check_norm

/-- …and so is a PROT_NONE guard over it.
kernel: mm/vma.c:vms_gather_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_over_the_image_is_unmodeled (eff : SyscallEffect) :
    check_mmap 65536 4096 0 50 mmap_fd_none 0 eff (reserved_page_model demo_limit)
      = CheckUnmodeled := by
  check_norm

/-! ### The ceiling is the fixture's `vm_init_sp`, not a constant

Every other fixture here has `demo_sp` for its stack pointer, so
`alloc_top` is one constant across them and a checker that hard-coded
`sp_window_lo - stack_max_size` would pass every pin above.  Under
`Checks/Cases/Mm/Mmap.lean`'s `hi_sp` the same placement at `demo_top` is
inside the ceiling on all three arms that read it.  Rocq:
`grant_at_demo_top_admitted_under_high_sp`,
`noaccess_grant_at_demo_top_admitted_under_high_sp`. -/

/-- An empty ledger under the high stack pointer. -/
def hi_sp_model : Model := fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 hi_sp)

/-- The rw grant at `demo_top`, refused under `demo_sp` by
`rw_grant_starting_at_the_ceiling_is_refused`, is accepted under `hi_sp`.
model: `State.alloc_top` is `vm_init_sp - stack_max_size`, read off the
fixture; the placement is below Linux's `TASK_SIZE` bound either way -/
theorem rw_grant_at_demo_top_under_a_high_sp_is_accepted :
    check_mmap 0 4096 3 34 mmap_fd_none 0
        (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) hi_sp_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)] [] 0 0 demo_limit 0
          hi_sp)) [] := by
  check_norm

/-- …the PROT_NONE reservation likewise…
model: `State.alloc_top`, read off the fixture's `vm_init_sp` -/
theorem noaccess_grant_at_demo_top_under_a_high_sp_is_accepted :
    check_mmap 0 4096 0 34 mmap_fd_none 0
        (SyscallEffect.mkEffectU (Z_to_bv 64 demo_top) [] [] [(Z_to_bv 64 demo_top, 4096)] [] [])
        hi_sp_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)]
          [(Z_to_bv 64 demo_top, 4096)] 0 0 demo_limit 0 hi_sp)) [] := by
  check_norm

/-- …and the MAP_FIXED rw grant at `demo_top`, declined under `demo_sp` by
`fixed_rw_above_the_ceiling_is_unmodeled`, is the free-range grant under
`hi_sp`.
model: `State.alloc_top`, read off the fixture's `vm_init_sp` -/
theorem fixed_rw_at_demo_top_under_a_high_sp_is_accepted :
    check_mmap (Z_to_bv 64 demo_top) 4096 3 50 mmap_fd_none 0
        (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) hi_sp_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)] [] 0 0 demo_limit 0
          hi_sp)) [] := by
  check_norm

/-! ### The shape gate's other declines, read at the checker

`Checks/Cases/Mm/Mmap.lean` pins these on `mmap_spec`; the checker's
`else CheckUnmodeled` is the same gate, and a checker that widened
`mmap_modeled_b`'s reading would show here first.  Each is decided
before the model is read, so each holds at every model and for every
effect offered. -/

/-- A page-aligned nonzero offset on the anonymous rw shape is declined:
`__get_unmapped_area` zeroes `pgoff` for anonymous memory, so Linux
grants it, and the model narrows to offset 0.  Rocq:
`mmap_anonymous_page_aligned_offset_is_unmodeled`.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem page_aligned_nonzero_offset_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 4096 eff m = CheckUnmodeled := by
  check_norm

/-- `MAP_POPULATE` (0x8000) beside the modeled flags is declined: the
prefault is a request about memory the model does not represent.  Rocq:
`mmap_populate_bit_still_unmodeled`.
kernel: mm/mmap.c:do_mmap; mm/util.c:vm_mmap_pgoff@v6.18.46 -/
theorem populate_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 4096 3 32802 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- `MAP_SHARED|MAP_ANONYMOUS` is shmem-backed on Linux (`do_mmap`'s
`MAP_SHARED` arm) and declined here.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem shared_anonymous_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 4096 3 33 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- `PROT_EXEC` on the anonymous shape is declined: no executable-permission
ledger.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem exec_prot_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 4096 7 34 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- `PROT_READ` alone is declined: no readable-but-not-writable page.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem read_only_anonymous_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_mmap 0 4096 1 34 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-! ### The witness -/

/-- The witness at the plain rw shape is -ENOMEM with the model unchanged,
the errno arm every ledger admits.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_rw_grant_is_enomem (m : Model) :
    mmap_witness 0 4096 3 34 mmap_fd_none 0 m = ret_outcome (errno_ret ENOMEM) m := by
  witness_norm

/-- …and the checker accepts that answer at every model.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_rw_grant_is_accepted (m : Model) :
    check_mmap 0 4096 3 34 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- The witness at a misaligned offset is the -EINVAL the wrapper answers.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem witness_at_misaligned_off_is_einval (m : Model) :
    mmap_witness 0 4096 3 34 mmap_fd_none 1 m = ret_outcome (errno_ret EINVAL) m := by
  witness_norm

/-- The witness at a file-backed request is the decline.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem witness_at_file_backed_is_unmodeled (m : Model) :
    mmap_witness 0 4096 3 2 mmap_fd_none 0 m = Unmodeled := by
  witness_norm

/-- The witness at the contained rw commit keeps the errno resolution that
leaves the range in place.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_fixed_rw_contained_is_enomem :
    mmap_witness 65536 4096 3 50 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret ENOMEM) one_map_model := by
  witness_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem witness_at_fixed_wrapping_end_is_unmodeled (m : Model) :
    mmap_witness (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)) 3 50 mmap_fd_none 0 m
      = Unmodeled := by
  witness_norm

/-- The witness at MAP_FIXED address 0 is the decline the checker gives.
kernel: security/security.c:security_mmap_addr@v6.18.46 -/
theorem witness_at_fixed_zero_is_unmodeled :
    mmap_witness 0 4096 3 50 mmap_fd_none 0 one_map_model = Unmodeled := by
  witness_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem witness_at_fixed_noaccess_wrapping_end_is_unmodeled (m : Model) :
    mmap_witness (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)) 0 50 mmap_fd_none 0 m
      = Unmodeled := by
  witness_norm

/-- …and PROT_NONE at address 0 is the decline at the witness as at the
checker.
kernel: mm/mmap.c:__get_unmapped_area; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem witness_at_fixed_noaccess_zero_is_unmodeled :
    mmap_witness 0 4096 0 50 mmap_fd_none 0 one_map_model = Unmodeled := by
  witness_norm

/-- The witness above the model's ceiling is the decline, on both MAP_FIXED
arms (the checker's `fixed_above_the_ceiling_is_unmodeled` and
`fixed_rw_above_the_ceiling_is_unmodeled`).
model: `State.alloc_top`, the band `bugs/grants-into-the-stack-band.md`
records -/
theorem witness_at_fixed_noaccess_above_the_ceiling_is_unmodeled :
    mmap_witness (Z_to_bv 64 demo_top) 4096 0 50 mmap_fd_none 0 one_map_model = Unmodeled := by
  witness_norm

/-- …the rw arm.
model: `State.alloc_top`, the band `bugs/grants-into-the-stack-band.md`
records -/
theorem witness_at_fixed_rw_above_the_ceiling_is_unmodeled :
    mmap_witness (Z_to_bv 64 demo_top) 4096 3 50 mmap_fd_none 0 one_map_model = Unmodeled := by
  witness_norm

/-- The witness at a misaligned offset with a wrapping length is the decline
Gate 1's second half gives.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:do_mmap@v6.18.46 -/
theorem witness_at_misaligned_off_wrapping_len_is_unmodeled (m : Model) :
    mmap_witness 0 (Z_to_bv 64 (-1)) 3 34 mmap_fd_none 1 m = Unmodeled := by
  witness_norm

/-- The witness at the zero-length `MAP_HUGETLB` request is the decline.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem witness_at_zero_len_hugetlb_is_unmodeled (m : Model) :
    mmap_witness 0 0 3 262178 mmap_fd_none 0 m = Unmodeled := by
  witness_norm

/-- The witness at the PROT_NONE reservation is -ENOMEM too.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_noaccess_grant_is_enomem (m : Model) :
    mmap_witness 0 4096 0 34 mmap_fd_none 0 m = ret_outcome (errno_ret ENOMEM) m := by
  witness_norm

/-- The witness at the zero-length plain request is its -EINVAL.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem witness_at_zero_len_is_einval (m : Model) :
    mmap_witness 0 0 3 34 mmap_fd_none 0 m = ret_outcome (errno_ret EINVAL) m := by
  witness_norm

/-- The witness at a free-range PROT_NONE MAP_FIXED request is -ENOMEM
with the ledger in place.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_fixed_noaccess_free_is_enomem :
    mmap_witness 0x40000000 4096 0 50 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret ENOMEM) one_map_model := by
  witness_norm

/-- …at the free-range rw request…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_fixed_rw_free_is_enomem :
    mmap_witness 0x40000000 4096 3 50 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret ENOMEM) one_map_model := by
  witness_norm

/-- …at the contained PROT_NONE request…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_fixed_noaccess_contained_is_enomem :
    mmap_witness 65536 4096 0 50 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret ENOMEM) one_map_model := by
  witness_norm

/-- …and at the spanning requests of either protection.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_fixed_rw_span_is_enomem :
    mmap_witness 65536 8192 3 50 mmap_fd_none 0 adjacent_maps_model
      = ret_outcome (errno_ret ENOMEM) adjacent_maps_model := by
  witness_norm

/-- …the PROT_NONE spelling of the same request.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem witness_at_fixed_noaccess_span_is_enomem :
    mmap_witness 65536 8192 0 50 mmap_fd_none 0 adjacent_maps_model
      = ret_outcome (errno_ret ENOMEM) adjacent_maps_model := by
  witness_norm

/-- The witness at a misaligned MAP_FIXED address is the -EINVAL, on
either arm.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem witness_at_fixed_misaligned_is_einval :
    mmap_witness 0x1001 4096 3 50 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret EINVAL) one_map_model := by
  witness_norm

/-- …the PROT_NONE spelling of the same request.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem witness_at_fixed_noaccess_misaligned_is_einval :
    mmap_witness 0x1001 4096 0 50 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret EINVAL) one_map_model := by
  witness_norm

/-- The witness at a MAP_FIXED request over an image page is the decline,
on either arm.
kernel: mm/vma.c:vms_gather_munmap_vmas@v6.18.46 -/
theorem witness_at_fixed_over_the_image_is_unmodeled :
    mmap_witness 65536 4096 0 50 mmap_fd_none 0 (reserved_page_model demo_limit) = Unmodeled := by
  witness_norm

/-- …the rw spelling of the same request.
kernel: mm/vma.c:vms_gather_munmap_vmas@v6.18.46 -/
theorem witness_at_fixed_rw_over_the_image_is_unmodeled :
    mmap_witness 65536 4096 3 50 mmap_fd_none 0 (reserved_page_model demo_limit) = Unmodeled := by
  witness_norm

/-! ### The arm and its registers -/

/-- The arm reads `off` from `a5`: a `1` there is the misaligned offset and
the arm accepts -EINVAL.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem arm_mmap_reads_off_from_a5 (m : Model) :
    arm_mmap.ca_check (mmap_in 0 4096 3 34 mmap_fd_none 1) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  simp only [arm_unfold]
  check_norm

/-- …and a `1` in `a4` is the `fd`, which the anonymous arm never reads:
the call is the plain rw shape and -EINVAL is refused there.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem arm_mmap_does_not_read_off_from_a4 (m : Model) :
    arm_mmap.ca_check (mmap_in 0 4096 3 34 1 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckReject := by
  simp only [arm_unfold]
  check_refute_norm

/-- The arm reads `len` from `a1`: a zero there with 4096 in `a0` is the
zero-length -EINVAL.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; mm/mmap.c:do_mmap@v6.18.46 -/
theorem arm_mmap_reads_len_from_a1 (m : Model) :
    arm_mmap.ca_check (mmap_in 4096 0 3 34 mmap_fd_none 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  simp only [arm_unfold]
  check_norm

/-- The arm reads `prot` from `a2` and `flags` from `a3`: transposed, the
flags word `3` has no `MAP_ANONYMOUS` and the call is declined.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem arm_mmap_reads_prot_and_flags_in_order (eff : SyscallEffect) (m : Model) :
    arm_mmap.ca_check (mmap_in 0 4096 34 3 mmap_fd_none 0) eff m = CheckUnmodeled := by
  simp only [arm_unfold]
  check_norm

/-- The arm's spec is `mmap_spec` at the six registers: over a spent
budget it admits exactly the -ENOMEM `Checks/Cases/Mm/Mmap.lean`'s
`rw_grant_over_budget_is_enomem` reads off `__mmap_prepare`.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem arm_mmap_spec_over_budget_is_enomem (o : outcome SyscallEffect) :
    arm_mmap.ca_arm.sa_spec (mmap_in 0 4096 3 34 mmap_fd_none 0) spent_budget_model o
      ↔ o = Ok (mkEffect (errno_ret ENOMEM) [] []) spent_budget_model [] := by
  simp only [arm_unfold]
  sys_norm

/-- The arm's witness is `mmap_witness` at the six registers.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem arm_mmap_witness_at_rw_grant_is_enomem (m : Model) :
    arm_mmap.ca_witness (mmap_in 0 4096 3 34 mmap_fd_none 0) m
      = ret_outcome (errno_ret ENOMEM) m := by
  simp only [arm_unfold]
  witness_norm

/-! ### The table: 222, after 93 and 94 -/

/-- The table finds `mmap` at 222 and hands back the trusted arm.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_mmap@v6.18.46 -/
theorem checked_table_finds_mmap : lookup_ca checked_table 222 = some arm_mmap :=
  lookup_ca_checked_table_mmap

/-- The number sits in the table once.  Stated as a FILTER of the table's
numbers, as `Checks/Cases/Checks/Sys/Kernel/Exit.lean` states its two, so
that the pin survives the next registration.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_mmap@v6.18.46 -/
theorem checked_table_carries_222_once :
    (checked_table.map ca_no).filter (fun n => n == 222) = [222] := by decide

/-! ### The dispatcher instances, over the real table

`check_syscall` and `syscall_spec_witness` dispatch over `checked_table`
itself; these pins are where the real table first answers an `mmap`
call. -/

/-- `check_syscall` at the plain rw grant over the tree's own table admits
-ENOMEM: the lookup finds `arm_mmap`, and the answer is `check_mmap`'s.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem check_syscall_accepts_mmap_enomem_over_the_real_table (m : Model) :
    check_syscall (mmap_in 0 4096 3 34 mmap_fd_none 0) (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckOk m [] := by
  dispatch_norm

/-- …and refuses -EBADF there: the arm the real table hands the dispatcher
is not one that accepts everything.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem check_syscall_rejects_mmap_ebadf_over_the_real_table (m : Model) :
    check_syscall (mmap_in 0 4096 3 34 mmap_fd_none 0) (mkEffect (errno_ret EBADF) [] []) m
      = CheckReject := by
  dispatch_refute_norm

/-- `check_syscall` at the contained rw commit over the tree's own table:
the six registers reach the checker in order and the ledger stays.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- fixed-rw -/
theorem check_syscall_accepts_fixed_rw_contained_over_the_real_table :
    check_syscall (mmap_in 65536 4096 3 50 mmap_fd_none 0) (mkEffect 65536 [] [(65536, 4096)])
        one_map_model
      = CheckOk one_map_model [] := by
  dispatch_norm

/-- `check_syscall` at a file-backed request over the tree's own table is
the checker's decline, not the dispatcher's: the arm is found and declines
(the probe's `fail-closed -- file` case, cited in prose for the reason
`file_backed_is_unmodeled` gives).
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem check_syscall_declines_file_backed_mmap_over_the_real_table (eff : SyscallEffect)
    (m : Model) :
    check_syscall (mmap_in 0 4096 3 2 mmap_fd_none 0) eff m = CheckUnmodeled := by
  dispatch_norm

/-- The tree's witness at the plain rw grant is not the decline: it is
`mmap_witness`'s -ENOMEM.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem the_trees_witness_at_mmap_is_enomem (m : Model) :
    syscall_spec_witness (mmap_in 0 4096 3 34 mmap_fd_none 0) m
      = ret_outcome (errno_ret ENOMEM) m := by
  dispatch_witness_norm

/-- …and at a file-backed request it is the decline, the arm's own.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem the_trees_witness_at_file_backed_mmap_is_the_decline (m : Model) :
    syscall_spec_witness (mmap_in 0 4096 3 2 mmap_fd_none 0) m = Unmodeled := by
  dispatch_witness_norm

end K6b

section K6c

/-! ## K6c — Rocq's `= CheckReject` lemmas by name, and what `rfl` costs

WHAT THIS SECTION IS.  The thirty-five mmap-family `= CheckReject`
lemmas of `theories/LinuxProcessSem/Checks/Cases/Mm/Mmap.v` (read at
Rocq baseline `f44244ad6b8041aa83053d9ca91e090037ed743b`, whose lemma
statements and fixtures are this tree's copy's, character for character;
only comments were re-pinned after it, 71 lines of them), restated under
the Rocq names on the Rocq fixtures and closed by `rfl`, nine of the
checker-level `= CheckOk` admissions the Rocq file states beside them,
restated the same way so that those refusals keep their accepting
partners, and one admission the Rocq file does not state, marked as such
where it stands.
K6b's `_is_refused` pins above state
refusals of the same kinds on K6b's own fixtures and under `sys_norm`;
this section is the by-name mirror, so that a reader holding a Rocq
lemma finds its Lean twin by searching for the name, and it is the
measurement the paragraph "HOW THESE CLOSE" reports.  Two of the names
are taken in the opened `Checks/Cases/Mm/Mmap.lean`, by that file's
SPEC-level twins of the same Rocq cases
(`noaccess_grant_at_demo_top_rejected_under_low_sp`,
`noaccess_grant_at_demo_top_admitted_under_high_sp`); the checker-level
twins here carry the suffix `_by_the_checker`.

THE PATTERN, for the `V-` tickets to copy.  Rocq closes a checker
refusal at closed arguments by `vm_compute` and `reflexivity`: bare, as
`Proof. vm_compute. reflexivity. Qed.` in `read_bad_fd_success_rejected`
(`theories/LinuxProcessSem/Checks/Cases/Fs/ReadWrite.v`), or as
`check_eq` (`theories/LinuxProcessSem/Checks/Cases/Prelude.v`), whose
first alternative after `vm_compute` is `reflexivity` and which closes
the thirty-five here.  The Lean twin of both is the term `rfl`: definitional unfolding walks
`check_syscall` to `lookup_ca` over `checked_table`, into the arm,
through `check_mmap`'s gates and into the fixture, and the two sides
meet at `CheckReject`.  The twin is the Rocq statement transliterated,
with no closer to keep in step with the checker's shape.
`Checks/Cases/Checks/Sys/Mm/Mremap.lean` closes every one of its
checker-level pins this way already, under one file-wide
`set_option maxRecDepth 32768`; this section is the same closer with the
raise per declaration, so that the marker says which statements need it,
and with the depth measured.  Two limits, both measured on the
thirty-five below (Lean 4.34, this file's imports built, one theorem at a
time):

- The depth.  At the default `maxRecDepth` (512), `rfl` closes the
  nineteen twins whose request resolves in the NULL-hint arms —
  placement, ceiling, overlap, budget, the stray-fd shape — each in
  milliseconds.  The sixteen whose request resolves in a MAP_FIXED arm,
  or whose offered effect carries an errno return, exceed it, and close
  under `set_option maxRecDepth N in` for N = 18000 and not for
  N = 16000 (10000, 12000 and 14000 fail the same sixteen; 20000,
  50000, 100000 and 200000 pass them all), at about half a second each.
  Those sixteen carry `set_option maxRecDepth 32768 in` below, one by
  one, so that the marker says which statements need the deeper stack.
  The ten `= CheckOk` statements all exceed the default depth, NULL-hint
  arms included — a `CheckOk` carries the post-state, so `rfl` has to
  compute the ledger the checker returns and meet the one the statement
  spells, and that walk is the deeper one — and all close at 32768, at
  about half a second each.  The section adds about ten seconds to this
  file.
- The alternatives.  `decide` is not available: `check_result` carries a
  `Model`, `Model` has no `DecidableEq`, and
  `Decidable (check_syscall … = CheckReject)` cannot be synthesised.
  `simp only [check_syscall, check_syscall_in, arm_unfold]; rfl` fails on
  exactly the sixteen `rfl` alone fails on, at the same depth, so the
  rewrite buys nothing.  `unfold check_syscall check_syscall_in
  check_mmap; rfl` fails on all thirty-five: `unfold` cannot open
  `check_mmap` behind the `match` on `lookup_ca` that `check_syscall_in`
  leaves.  K6b's `dispatch_refute_norm` closes all thirty-five in under
  three seconds together, and is what a statement at a VARIABLE model or
  under a hypothesis has to use whenever the checker's answer reads that
  model: `rfl` closes such a statement only where the answer never does
  (`Checks/Cases/Checks/Sys/Kernel/Exit.lean`'s
  `check_syscall_rejects_a_return_at_exit_over_the_real_table`, at a
  variable `m`), and every refusal here turns on the ledger.

WHY THIS FILE AND NOT THE SPEC TWIN.  The spec twin
`Checks/Cases/Mm/Mmap.lean` is left untouched on purpose.
`tools/lean_mutate.py` keys the committed mutation score of
`Sys/Mm/Mmap.lean` on the import closure of that spec twin, and no spec
twin in the tree imports the checker layer.  Importing
`Checks/Sys/Mm/Mmap.lean` there would put the checker's soundness and
completeness proofs against `mmap_spec` into every spec mutant's build:
a mutant that changes the spec's answer breaks those proofs before it
reaches a pin and is scored STILLBORN, the outcome that never counts
against the gate, instead of KILLED.  The gate would keep its number
and lose its teeth.  So the checker's pins stay in the checker's pin
file, and the sentence in the spec twin's header saying the Lean tree
"has no executable checker yet", stale since K6b, is not corrected here
for the same reason.

WHAT IS NOT TWINNED.  The Rocq file's fifty-six `= CheckReject`
occurrences are these thirty-five, nine on `brk` and `munmap`
(C-Mm-Mmap-brk-munmap's, after the sentinel below), and twelve on the
MAP_FIXED_NOREPLACE arms — eleven inside the seven NOREPLACE lemmas and
one in the `asan` shadow sequence — twinned in A18's section
below.  One refusal the Rocq file states as `<> CheckOk` rather
than `= CheckReject` is not twinned: `mmap_null_hint_above_top_never_accepted`,
a `forall` over the stack pointer and the placement, which no `rfl` can
state.  Its NOREPLACE partner, `mmap_noreplace_free_range_never_eexist`,
is twinned below by a walk of `check_mmap`.
Of the Rocq file's checker-level `= CheckOk` mmap admissions only the
nine named below are twinned; the rest — among them
`mmap_fixed_rw_span_errno_preserves_the_range`,
`mmap_noaccess_at_ceiling_boundary_grants`,
`mmap_modeled_adjacent_to_live_map_grants`,
`mmap_noaccess_adjacent_to_live_map_grants`,
`mmap_beyond_budget_fails_enomem`, `mmap_misaligned_offset_is_einval`,
`mmap_fixed_errno_may_destroy_the_range` and
`mmap_fixed_errno_may_preserve_the_range`, the partners of refusals
twinned above — are not.  Nothing registers the correspondence: the coverage header
`tools/check_lean_cases_parity.py` reads lives at the spec twin's path
and is not written by this ticket. -/

/-! ### Rocq's fixtures and inputs, under Rocq's names

`noaccess_base`, `tight_model`, `ceiling_room_model` and
`region_live_model` are `Checks/Cases/Prelude.lean`'s already
(`ceiling_room_model` there is `fixture demo_vm`, Rocq's
`with_vmmaps (mkVmMaps [] [] 0 0 demo_limit)` over `init_model`, the same
ledger); the rest are the Rocq file's, transliterated.  The run
parameters they take are shared too: `demo_sp`, `demo_top`, `demo_limit`
and `demo_input` are `Checks/Cases/Prelude.lean`'s, `mmap_base_max` is
`State/Geometry.lean`'s, the six-argument `mmap_in` is K6b's above, and
`hi_sp` — Rocq's `sp_window_lo + 0x10000000`, character for character —
is the opened spec twin `Checks/Cases/Mm/Mmap.lean`'s, so
`top_hi_model_rocq` starts where Rocq's `top_hi_model` does.  Rocq's
`top_hi_model` is defined with the accepting partners below, as
`top_hi_model_rocq`. -/

/-- Rocq's `mmap_in len`: the plain rw NULL-hint request of `len` bytes. -/
def null_rw_in (len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [0, len, 3, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- Rocq's `mmap_noaccess_in len`: the same request at PROT_NONE. -/
def null_none_in (len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [0, len, 0, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- A live 8 KiB owner at 65536 under a 16 KiB budget: what a spanning
MAP_FIXED request over `[69632, 77824)` meets half-mapped. -/
def span_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base

/-- One live page at 65536 under an 8 KiB budget: a 12 KiB spanning
request needs 8 KiB of new backing against the 4 KiB left. -/
def span_tight_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192) noaccess_base

/-- The placement fixture: an empty ledger started at `demo_sp` under the
demo budget, its `mmap_base` at the top-down layout's maximum. -/
def placement_model : Model :=
  init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp demo_limit (demo_input [] IEof)

/-- Two reservations with a one-page hole at `0x3aaaaab000` between them,
the second running up to `demo_top`. -/
def holed_reservation : List (word × word) :=
  [(Z_to_bv 64 0x2aaaaab000, Z_to_bv 64 0x1000000000),
   (Z_to_bv 64 0x3aaaaac000, Z_to_bv 64 (demo_top - 0x3aaaaac000))]

/-- `placement_model` with `holed_reservation` both reserved and live. -/
def holed_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] holed_reservation holed_reservation 0 0
      demo_limit (Z_to_bv 64 mmap_base_max) demo_sp) placement_model

/-- `placement_model` with one live page at `0x7fff7f7ff000`, the page
below `demo_top`. -/
def placement_model_1 : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x7fff7f7ff000, 4096)] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model

/-- `placement_model` with the binary's LOAD reservation `[0x10000, 0x12000)`
and no live map. -/
def placement_model_img : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [(Z_to_bv 64 0x10000, 8192)] [] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model

/-- Rocq's `top_lo_model`: `placement_model` under its Rocq pair name, the
low-sp half of the pair whose high-sp half is `top_hi_model_rocq` below. -/
def top_lo_model : Model :=
  init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp demo_limit (demo_input [] IEof)

/-! ### The MAP_FIXED shapes and the errno-carrying effects: the deeper stack -/

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_commit_over_backed_budget_rejected`.  An rw
MAP_FIXED commit over the first page of an 8 KiB PROT_NONE owner under a
2 KiB budget: the page it exposes is newly charged — `accountable_mapping`
holds for a private writable mapping, and `__mmap_prepare` puts
`pglen - nr_accounted` to `security_vm_enough_memory_mm` — so the
success is refused.
kernel: mm/vma.c:__mmap_prepare,accountable_mapping; mm/util.c:__vm_enough_memory@v6.18.46 -/
theorem mmap_fixed_rw_commit_over_backed_budget_rejected :
    check_syscall (mmap_in 65536 4096 3 50 mmap_fd_none 0) (mkEffect 65536 [] [(65536, 4096)])
        (with_vmmaps (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 2048 0 demo_sp)
          noaccess_base)
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_span_errno_partial_unmap_rejected`.  A spanning
MAP_FIXED failure leaves the range intact or leaves the whole request as
a hole, nothing between: `vms_abort_munmap_vmas` reattaches every VMA
the gather detached, or stores NULL over exactly `[vms->start, vms->end)`.
An -ENOMEM announcing an unmap of PART of the request describes a ledger
no kernel reaches.
kernel: mm/vma.c:__mmap_region,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_rw_span_errno_partial_unmap_rejected :
    check_syscall (mmap_in 69632 8192 3 50 mmap_fd_none 0)
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] []) span_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_span_errno_unmapping_the_remnant_rejected`.  The
abort's store covers the request, not everything the gather split: the
remnant of the owner at 65536 is not part of the hole, and a failure
claiming it is, is refused.
kernel: mm/vma.c:__mmap_region,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_rw_span_errno_unmapping_the_remnant_rejected :
    check_syscall (mmap_in 69632 8192 3 50 mmap_fd_none 0)
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 12288)] [] []) span_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_span_errno_with_zeros_rejected`.  No failure
exposes bytes: the abort path builds no VMA, so there is nothing for a
fault to zero-fill, and -ENOMEM with a zero-fill attached is refused
whichever way the range resolved.
kernel: mm/vma.c:__mmap_region,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_rw_span_errno_with_zeros_rejected :
    check_syscall (mmap_in 69632 8192 3 50 mmap_fd_none 0)
        (mkEffect (errno_ret ENOMEM) [] [(69632, 8192)]) span_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_span_partial_zero_fill_rejected`.  The success
zeroes the WHOLE request: `__mmap_new_vma` sets the new VMA over
`[map->addr, map->end)`, and every page of a fresh anonymous VMA reads
as zero at `do_anonymous_page`.  A success exposing only the half that
was mapped before is refused.
kernel: mm/vma.c:__mmap_region,__mmap_new_vma; mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem mmap_fixed_rw_span_partial_zero_fill_rejected :
    check_syscall (mmap_in 69632 8192 3 50 mmap_fd_none 0)
        (mkEffect 69632 [] [(69632, 4096)]) span_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_span_success_with_unmaps_rejected`.  The success
unmaps nothing: the gather's tear-down of the overlapped half ends inside
the one new mapping `__mmap_new_vma` stores, and the zero-fill over the
whole request already subsumes it.  A success that also announces an
unmap describes a transition the model does not have.
kernel: mm/vma.c:__mmap_region,__mmap_prepare,__mmap_new_vma@v6.18.46 -/
theorem mmap_fixed_rw_span_success_with_unmaps_rejected :
    check_syscall (mmap_in 69632 8192 3 50 mmap_fd_none 0)
        (SyscallEffect.mkEffectU 69632 [] [(69632, 8192)] [(69632, 8192)] [] []) span_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_span_over_budget_rejected`.  The part of a
spanning request that met nothing is newly owned and charged
(`map->charged = map->pglen - vms->nr_accounted`): 8 KiB of new charge
against the 4 KiB `span_tight_model` has left refuses the success.
kernel: mm/vma.c:__mmap_prepare,accountable_mapping; mm/util.c:__vm_enough_memory@v6.18.46 -/
theorem mmap_fixed_rw_span_over_budget_rejected :
    check_syscall (mmap_in 65536 12288 3 50 mmap_fd_none 0)
        (mkEffect 65536 [] [(65536, 12288)]) span_tight_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_noaccess_span_errno_partial_unmap_rejected`.  The
PROT_NONE abort is all-or-nothing in the same way as the rw one: the pin
is on the arm, not on `prot`.
kernel: mm/vma.c:__mmap_region,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_noaccess_span_errno_partial_unmap_rejected :
    check_syscall (mmap_in 69632 8192 0 50 mmap_fd_none 0)
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] []) span_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_noaccess_span_success_with_zeros_rejected`.  A
PROT_NONE mapping exposes nothing — a load on a VMA without `VM_READ` or
`VM_WRITE` is `access_error`'s fault — so a success carrying a zero-fill
is refused.
kernel: mm/vma.c:__mmap_new_vma; arch/riscv/mm/fault.c:access_error@v6.18.46 -/
theorem mmap_fixed_noaccess_span_success_with_zeros_rejected :
    check_syscall (mmap_in 69632 8192 0 50 mmap_fd_none 0)
        (mkEffect 69632 [] [(69632, 8192)]) span_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_wider_zero_fill_rejected`.  The commit exposes
EXACTLY the range it was asked for: `do_mmap` page-rounds `len`, and the
VMA `__mmap_new_vma` stores ends at `map->end`.  A kernel claiming to
have zeroed the whole 8 KiB owner in answer to a 4 KiB request is
refused, not accepted as an over-delivery.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_new_vma@v6.18.46 -/
theorem mmap_fixed_rw_wider_zero_fill_rejected :
    check_syscall (mmap_in 65536 4096 3 50 mmap_fd_none 0) (mkEffect 65536 [] [(65536, 8192)])
        (with_vmmaps (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
          noaccess_base)
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_success_with_unmap_rejected`.  The contained
SUCCESS unmaps nothing: the committed page stays in the ledger as the new
VMA, and the zero-fill already makes every covered byte defined.
kernel: mm/vma.c:__mmap_region,__mmap_new_vma@v6.18.46 -/
theorem mmap_fixed_rw_success_with_unmap_rejected :
    check_syscall (mmap_in 65536 4096 3 50 mmap_fd_none 0)
        (SyscallEffect.mkEffectU 65536 [] [(65536, 4096)] [(65536, 4096)] [] [])
        (with_vmmaps (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
          noaccess_base)
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_fresh_over_budget_rejected`.  A MAP_FIXED grant
into free space is metered like any other: against a 2 KiB budget the
4 KiB charge fails `security_vm_enough_memory_mm`, and only the errno is
left.
kernel: mm/vma.c:__mmap_prepare,accountable_mapping; mm/util.c:__vm_enough_memory@v6.18.46 -/
theorem mmap_fixed_rw_fresh_over_budget_rejected :
    check_syscall (mmap_in 65536 4096 3 50 mmap_fd_none 0) (mkEffect 65536 [] [(65536, 4096)])
        (with_vmmaps (mkVmMaps [] [] 0 0 2048) noaccess_base)
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_failure_with_zeros_rejected`.  A contained
FAILURE never exposes bytes either: -ENOMEM with a zero-fill attached is
refused whichever way the range resolved.
kernel: mm/vma.c:__mmap_region,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_rw_failure_with_zeros_rejected :
    check_syscall (mmap_in 65536 4096 3 50 mmap_fd_none 0)
        (mkEffect (errno_ret ENOMEM) [] [(65536, 4096)])
        (with_vmmaps (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
          noaccess_base)
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_overflowing_len_rejects_einval`.  `do_mmap` rounds
the length with `PAGE_ALIGN` and answers -ENOMEM on the wrap before
`__get_unmapped_area` reaches `offset_in_page(addr)`, so -EINVAL on a
misaligned MAP_FIXED request whose length wraps is the wrong errno.
`do_mmap` decides the case; `__get_unmapped_area` is cited as the
function that spells the -EINVAL this refusal is about, which is what
KMENTION asks of a statement it reads as positive (`= CheckReject` is
one to it), not as a second decider.  The admitted answer is
`mmap_fixed_overflowing_len_is_enomem` below.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem mmap_fixed_overflowing_len_rejects_einval :
    check_syscall (mmap_in 4097 18446744073709551615 0 50 mmap_fd_none 0)
        (mkEffect (errno_ret EINVAL) [] []) noaccess_base
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_misaligned_offset_ebadf_is_rejected`.  riscv's wrapper
answers -EINVAL on a misaligned offset before `ksys_mmap_pgoff` could
`fget` the fd, so the closed fd's -EBADF is not available here.  Nor
under qemu-user, whose `target_mmap` tests the offset's alignment before
any fd use (`Sys/Mm/Mmap.lean`'s `mmap_pglen_ok_b` docstring carries the
QEMU reading); the 4 KiB length does not wrap, so the ordering the two
disagree on (`bugs/mmap-fixed-wrap-gate-admits-linux-alone.md`) does not
reach this input.  `riscv_sys_mmap` decides; `ksys_mmap_pgoff` is cited
as the function spelling the -EBADF refused, for KMENTION.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem mmap_misaligned_offset_ebadf_is_rejected :
    check_syscall (mmap_in 0 4096 1 2 999 1) (mkEffect (errno_ret EBADF) [] []) noaccess_base
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_errno_unmap_must_be_the_request`.  The gap a failed
MAP_FIXED leaves is exactly the requested range: `vms_gather_munmap_vmas`
splits the owner at `vms->start` and `vms->end`, and the abort's store
covers `[vms->start, vms->end)` and nothing more.  An -ENOMEM unmapping
the whole 8 KiB owner is not a shape the abort path produces.
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas,vms_abort_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_errno_unmap_must_be_the_request :
    check_syscall (mmap_in 65536 4096 0 50 mmap_fd_none 0)
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] [])
        (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) noaccess_base)
      = CheckReject :=
  rfl

/-! ### The NULL-hint shapes: `rfl` at the default depth -/

/-- Rocq: `mmap_anonymous_other_fd_bad_placement_is_rejected`.  With
MAP_ANONYMOUS the fd is not read — `ksys_mmap_pgoff` calls `fget` only
without the flag — so a stray fd widens the shape match and nothing
else: a grant at address 0 is still below the floor
(`generic_get_unmapped_area_topdown` searches from `PAGE_SIZE` up, and
`cap_mmap_addr` refuses below `dac_mmap_min_addr` to a task without
`CAP_SYS_RAWIO`).
kernel: mm/mmap.c:ksys_mmap_pgoff,generic_get_unmapped_area_topdown; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mmap_anonymous_other_fd_bad_placement_is_rejected :
    check_syscall (mmap_in 0 4096 3 34 3 0) (mkEffect 0 [] [(0, 4096)]) noaccess_base
      = CheckReject :=
  rfl

/-- Rocq: `mmap_fresh_noaccess_zeros_are_rejected`.  A fresh PROT_NONE
grant's range goes AWAY (its `eff_unmaps`); an effect that also
zero-fills the same range claims the pages are unmapped and readable at
once, and a load on that VMA is `access_error`'s fault.  No trace
produces the shape, which is why it is stated here.
kernel: mm/vma.c:__mmap_new_vma; arch/riscv/mm/fault.c:access_error@v6.18.46 -/
theorem mmap_fresh_noaccess_zeros_are_rejected :
    check_syscall (mmap_in 0 4096 0 34 mmap_fd_none 0)
        (SyscallEffect.mkEffectU 65536 [] [(65536, 4096)] [(65536, 4096)] [] []) noaccess_base
      = CheckReject :=
  rfl

/-- Rocq: `mmap_beyond_budget_rejected`.  Address space is plentiful on
`tight_model` and the ceiling nowhere near; an 8 KiB grant against the
4 KiB left of its budget is refused by the charge alone.
kernel: mm/vma.c:__mmap_prepare,accountable_mapping; mm/util.c:__vm_enough_memory@v6.18.46 -/
theorem mmap_beyond_budget_rejected :
    check_syscall (null_rw_in 8192) (mkEffect 131072 [] [(131072, 8192)]) tight_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_modeled_zero_placement_is_rejected`.  Address 0 is
page-aligned, below the ceiling, disjoint and within budget; what refuses
it is the floor.  A NULL hint never yields it: with no hint to test,
`generic_get_unmapped_area_topdown` searches from
`info.low_limit = PAGE_SIZE`, and its bottom-up fallback from
`TASK_UNMAPPED_BASE`.  Behind the search, `__get_unmapped_area` asks
`security_mmap_addr` of every answer, whose DAC half `cap_mmap_addr`
wants `CAP_SYS_RAWIO` below `dac_mmap_min_addr` — the `vm.mmap_min_addr`
sysctl, `CONFIG_DEFAULT_MMAP_MIN_ADDR` at boot — and whose LSM half adds
`CONFIG_LSM_MMAP_MIN_ADDR` where an LSM is built in; the model's `0 < a`
is the loosest envelope over all of them.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,__get_unmapped_area; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mmap_modeled_zero_placement_is_rejected :
    check_syscall (null_rw_in 4096) (mkEffect 0 [] [(0, 4096)]) ceiling_room_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_noaccess_zero_placement_is_rejected`: the PROT_NONE arm
reads the same floor.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,__get_unmapped_area; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mmap_noaccess_zero_placement_is_rejected :
    check_syscall (null_none_in 4096) (SyscallEffect.mkEffectU 0 [] [] [(0, 4096)] [] [])
        ceiling_room_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_modeled_unaligned_placement_is_rejected`.  65537 is one
byte past a page boundary; the top-down search returns page-aligned
gaps only (`mmap_base` is `PAGE_ALIGN`ed and every VMA end is), so
alignment is the one conjunct that refuses this otherwise exact grant.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area_topdown; mm/util.c:mmap_base@v6.18.46 -/
theorem mmap_modeled_unaligned_placement_is_rejected :
    check_syscall (null_rw_in 4096) (mkEffect 65537 [] [(65537, 4096)]) ceiling_room_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_noaccess_unaligned_placement_is_rejected`: the PROT_NONE arm.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area_topdown; mm/util.c:mmap_base@v6.18.46 -/
theorem mmap_noaccess_unaligned_placement_is_rejected :
    check_syscall (null_none_in 4096) (SyscallEffect.mkEffectU 65537 [] [] [(65537, 4096)] [] [])
        ceiling_room_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_modeled_past_ceiling_is_rejected`.  A grant AT `demo_top`
(140735332483072) ends one page past the run's grant ceiling,
`alloc_top` = `vm_init_sp − stack_max_size`: the bottom of THIS run's
stack under the 8 MiB `RLIMIT_STACK` the model fixes.  The stack grows
down into that band and no further — `expand_downwards` accounts each
growth through `acct_stack_growth`, which refuses a stack larger than
`rlimit(RLIMIT_STACK)` — so a grant ending at or under the line is
disjoint from every stack the run can grow.  Linux's own top-down
placements stop lower still: `mmap_base` is
`PAGE_ALIGN(STACK_TOP − gap − rnd)` with `gap` the stack limit plus
`stack_guard_gap`, and the search's `high_limit` is it.  What the bound
refuses that Linux can do — a hinted grant into the band, or the
bottom-up fallback `generic_get_unmapped_area_topdown` takes once
nothing under `mmap_base` fits — is `bugs/grants-into-the-stack-band.md`'s.
Region and budget are as permissive as for the grant one page lower,
which is accepted.  The bound is the model's, so the evidence line is
K6b's for the same refusal; the kernel functions above are what make it
sound where it is, and the entry is where it is not.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem mmap_modeled_past_ceiling_is_rejected :
    check_syscall (null_rw_in 4096) (mkEffect 140735332483072 [] [(140735332483072, 4096)])
        ceiling_room_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_noaccess_past_ceiling_is_rejected`: the PROT_NONE arm
reads the same `alloc_top`.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem mmap_noaccess_past_ceiling_is_rejected :
    check_syscall (null_none_in 4096)
        (SyscallEffect.mkEffectU 140735332483072 [] [] [(140735332483072, 4096)] [] [])
        ceiling_room_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_modeled_overlapping_live_map_is_rejected`.  A grant at the
live mapping's own start overlaps it exactly; the gap search returns
unmapped space only, so disjointness alone refuses it.
kernel: mm/mmap.c:vm_unmapped_area; mm/vma.c:unmapped_area_topdown@v6.18.46 -/
theorem mmap_modeled_overlapping_live_map_is_rejected :
    check_syscall (null_rw_in 4096) (mkEffect 131072 [] [(131072, 4096)]) region_live_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_noaccess_overlapping_live_map_is_rejected`: the PROT_NONE arm.
kernel: mm/mmap.c:vm_unmapped_area; mm/vma.c:unmapped_area_topdown@v6.18.46 -/
theorem mmap_noaccess_overlapping_live_map_is_rejected :
    check_syscall (null_none_in 4096)
        (SyscallEffect.mkEffectU 131072 [] [] [(131072, 4096)] [] []) region_live_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_null_hint_inside_the_reservation_rejected`.  The page below
the hole at `0x3aaaaab000` lies inside the first reservation; a NULL-hint
grant may skip the hole (the Rocq file's accepting case), but not land on
owned space.
kernel: mm/mmap.c:vm_unmapped_area; mm/vma.c:unmapped_area_topdown@v6.18.46 -/
theorem mmap_null_hint_inside_the_reservation_rejected :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x3aaaaaa000) [] [(Z_to_bv 64 0x3aaaaaa000, 4096)]) holed_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_null_hint_unaligned_rejected`.  One byte off a page
boundary, everything else identical to an accepted grant.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area_topdown; mm/util.c:mmap_base@v6.18.46 -/
theorem mmap_null_hint_unaligned_rejected :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x80000001) [] [(Z_to_bv 64 0x80000001, 4096)]) placement_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_null_hint_zero_rejected`.  Address 0 is refused under
every setting of `mmap_min_addr`: a NULL-hint search starts at
`info.low_limit = PAGE_SIZE` (its bottom-up fallback at
`TASK_UNMAPPED_BASE`) and never answers 0, whatever the floor is set to.
That floor is no single stock value: `cap_mmap_addr` reads
`dac_mmap_min_addr`, `CONFIG_DEFAULT_MMAP_MIN_ADDR` at boot and the
`vm.mmap_min_addr` sysctl after, and `update_mmap_min_addr` takes the
`umax` of it and `CONFIG_LSM_MMAP_MIN_ADDR` where an LSM is built in —
4096 on the tree's VM kernel, which builds none, 65536 under riscv's
defconfig.  The spec's `0 < a` is the loosest envelope over every one.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown; security/commoncap.c:cap_mmap_addr; security/min_addr.c:update_mmap_min_addr@v6.18.46 -/
theorem mmap_null_hint_zero_rejected :
    check_syscall (null_rw_in 4096) (mkEffect 0 [] [(0, 4096)]) placement_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_null_hint_above_ceiling_rejected`.  A grant whose end
passes the run's grant top, `alloc_top` = `vm_init_sp − stack_max_size`,
would not be disjoint from every stack this run can grow:
`acct_stack_growth` lets the stack reach `rlimit(RLIMIT_STACK)` below
its top, 8 MiB in the model.  Linux's top-down search places below
`mmap_base`, itself under that line by `stack_guard_gap`; its bottom-up
fallback can place above, and that refusal is
`bugs/grants-into-the-stack-band.md`'s.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem mmap_null_hint_above_ceiling_rejected :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) placement_model
      = CheckReject :=
  rfl

/-- Rocq: `mmap_null_hint_overlapping_live_rejected`.  The page below
`demo_top` is live in `placement_model_1`; the accepting case places
below it, and a grant ON it is refused.
kernel: mm/mmap.c:vm_unmapped_area; mm/vma.c:unmapped_area_topdown@v6.18.46 -/
theorem mmap_null_hint_overlapping_live_rejected :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x7fff7f7ff000) [] [(Z_to_bv 64 0x7fff7f7ff000, 4096)])
        placement_model_1
      = CheckReject :=
  rfl

/-- Rocq: `mmap_null_hint_over_image_rejected`.  Disjointness covers the
binary's LOAD reservation too, and separately: the gap search walks the
VMA tree, where the image's segments are VMAs like any other, so a grant
over `[0x10000, 0x12000)` is refused with `vm_maps` empty.
kernel: mm/mmap.c:vm_unmapped_area; mm/vma.c:unmapped_area_topdown@v6.18.46 -/
theorem mmap_null_hint_over_image_rejected :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x11000) [] [(Z_to_bv 64 0x11000, 4096)]) placement_model_img
      = CheckReject :=
  rfl

/-- Rocq: `grant_at_demo_top_rejected_under_low_sp`.  The grant top is
read from the ledger, not from a constant: started at `demo_sp`, the
run's top is `demo_top`, and a grant ending one page past it is refused,
where the same effect against `top_hi_model_rocq` (started 256 MiB
higher) is accepted, `grant_at_demo_top_admitted_under_high_sp` below.
The ceiling is `alloc_top`, read from `vm_init_sp`: the stack this run
was started with is the one `acct_stack_growth` lets grow 8 MiB down, so
the line follows the stack pointer and not a constant — the mistake
Rocq's `mmap_null_hint_above_top_never_accepted` says this pair retired.
(`mmap_base`, `PAGE_ALIGN(STACK_TOP − gap − rnd)`, follows a stack too —
but the constant `STACK_TOP`'s, before randomisation, not this run's
`sp`: two runs differing only in their stack draw share `mmap_base` and
differ in `alloc_top`, which is the dependence this pair pins.)
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem grant_at_demo_top_rejected_under_low_sp :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) top_lo_model
      = CheckReject :=
  rfl

/-- Rocq: `noaccess_grant_at_demo_top_rejected_under_low_sp`, whose name
`Checks/Cases/Mm/Mmap.lean` holds for the spec-level twin.  The PROT_NONE
arm reads the same field.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem noaccess_grant_at_demo_top_rejected_under_low_sp_by_the_checker :
    check_syscall (null_none_in 4096)
        (SyscallEffect.mkEffectU (Z_to_bv 64 demo_top) [] [] [(Z_to_bv 64 demo_top, 4096)] [] [])
        top_lo_model
      = CheckReject :=
  rfl

/-! ### Rocq's accepting partners of the refusals above

Each refusal above has an admission beside it in the Rocq file, one
page or one errno away, and nine of those checker-level `= CheckOk`
statements are twinned below: the anchors of the NULL-hint placement
refusals — the grant one page away, or the same grant under the higher
stack — the grant that spends the budget exactly, the -ENOMEM of the
wrapping length, and the errno resolution of the span-budget refusal;
one more admission, Rocq's nowhere, closes the subsection.  They are
here so that those pairs stay pairs, and because they measure the other
half of the pattern: `rfl` on a `CheckOk` has to compute the post-state on the left
and meet the one the statement spells on the right, constructor for
constructor, and the depth that costs is recorded on each.  Rocq's
`top_hi_model` is `init_model` at `hi_sp` with `mmap_base_max` in the
ledger; the opened `Checks/Cases/Mm/Mmap.lean` holds that name for a
fixture with 0 there, so the Rocq-faithful fixture is `top_hi_model_rocq`
(no arm's verdict reads the field's value — `check_mmap` only copies it
into the post-state it returns — so the two accept the same effects and
differ in that slot of the ledger a `CheckOk` spells; that the value,
`sp_window_hi - 128 MiB`, sits above `demo_sp` itself is inert for the
same reason). -/

/-- Rocq's `top_hi_model`: `top_lo_model` started 256 MiB higher, under
the name the spec twin leaves free. -/
def top_hi_model_rocq : Model :=
  init_model [] 0 (Z_to_bv 64 mmap_base_max) hi_sp demo_limit (demo_input [] IEof)

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_null_hint_skipping_a_free_gap_admitted`.  A NULL-hint grant
on the page just below the lower block of `holed_reservation`, while the
one-page hole at `0x3aaaaab000` — a gap that fits the request — lies
free above it: the checker asks nothing about which gap a search would
have taken first.  `__get_unmapped_area` hands the choice to the arch and
layout hooks, and every placement they can make is admitted.
kernel: mm/mmap.c:__get_unmapped_area,vm_unmapped_area; mm/vma.c:unmapped_area_topdown@v6.18.46 -/
theorem mmap_null_hint_skipping_a_free_gap_admitted :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x2aaaaaa000) [] [(Z_to_bv 64 0x2aaaaaa000, 4096)]) holed_model
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] ((Z_to_bv 64 0x2aaaaaa000, 4096) :: holed_reservation)
              holed_reservation 0 0 demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)
            holed_model) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_null_hint_beside_live_admitted`, the anchor of
`mmap_null_hint_overlapping_live_rejected`: one page below the live page
of `placement_model_1`, disjoint from every live mapping, is admitted
where the live page itself is refused.  `unmapped_area_topdown` returns
only a gap free of every VMA in the interval it searches.
kernel: mm/vma.c:unmapped_area_topdown; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mmap_null_hint_beside_live_admitted :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x7fff7f7fe000) [] [(Z_to_bv 64 0x7fff7f7fe000, 4096)])
        placement_model_1
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull []
              [(Z_to_bv 64 0x7fff7f7fe000, 4096), (Z_to_bv 64 0x7fff7f7ff000, 4096)] []
              0 0 demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)
            placement_model_1) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_null_hint_low_grant_admitted`.  A first NULL-hint grant at
0x80000000 on an empty ledger: page-aligned, positive, below the ceiling
and free, and no floor conjunct refuses it (the resolution of issue #417
in the Rocq file's words).  Linux admits any gap `unmapped_area_topdown`
finds between `mmap_min_addr` and `mmap_base`, and the model quantifies
over the layout that decides which one.
kernel: mm/vma.c:unmapped_area_topdown; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mmap_null_hint_low_grant_admitted :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x80000000) [] [(Z_to_bv 64 0x80000000, 4096)]) placement_model
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 4096)] [] 0 0 demo_limit
              (Z_to_bv 64 mmap_base_max) demo_sp)
            placement_model) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_modeled_at_ceiling_boundary_grants`.  The last page-aligned
start admitting a 4 KiB grant under `demo_top`, so that the grant ends
at the ceiling exactly: admitted, where one page higher
(`mmap_modeled_past_ceiling_is_rejected`) is refused.  The bound is `≤`:
a grant ending exactly at `alloc_top` leaves the stack the whole 8 MiB
reach `acct_stack_growth` allows it above the line — and a gap ending
exactly at a search's `high_limit` is a gap to `unmapped_area_topdown`
too.  The probe is K6b's for `rw_grant_ending_at_the_ceiling_is_accepted`:
its `several` case injects this very address, and the emulator's own
placements under it pass the same bound.
probe: testing/syscall-check/tests/mmap_null_hint.c#conform --mutate mmap:ret=0x7fff7f7ff000,drop-zeros,smuggle-zeros:0x7fff7f7ff000:4096 -- several -/
theorem mmap_modeled_at_ceiling_boundary_grants :
    check_syscall (null_rw_in 4096)
        (mkEffect 140735332478976 [] [(140735332478976, 4096)]) ceiling_room_model
      = CheckOk
          (with_vmmaps (mkVmMaps [] [(140735332478976, 4096)] 0 0 demo_limit)
            ceiling_room_model) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_within_budget_grants`, the anchor of
`mmap_beyond_budget_rejected`: on `tight_model`, 4 KiB live under an 8 KiB
budget, the 4 KiB grant that spends the budget exactly is admitted where
the 8 KiB one is refused, and the ledger it returns charges the
page-rounded length.  The budget test is `≤`, as the kernel's are —
`may_expand_vm` refuses only a total OVER `RLIMIT_AS`, and
`__vm_enough_memory` only pages beyond what is committable — so the
boundary lands on the accepting side.
kernel: mm/vma.c:__mmap_prepare,accountable_mapping; mm/mmap.c:may_expand_vm; mm/util.c:__vm_enough_memory@v6.18.46 -/
theorem mmap_within_budget_grants :
    check_syscall (null_rw_in 4096) (mkEffect 131072 [] [(131072, 4096)]) tight_model
      = CheckOk
          (with_vmmaps (mkVmMaps [] [(131072, 4096), (65536, 4096)] 0 0 8192) tight_model) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `grant_at_demo_top_admitted_under_high_sp`, the accepting half of
`grant_at_demo_top_rejected_under_low_sp`: started 256 MiB higher, the
run's top moves up with the stack and the grant ending at `demo_top`
fits.  `alloc_top` is `vm_init_sp − stack_max_size`, so the ceiling
follows the stack pointer the run was started with: the stack
`acct_stack_growth` bounds is this run's, and its 8 MiB under `hi_sp`
end above `demo_top`.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem grant_at_demo_top_admitted_under_high_sp :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) top_hi_model_rocq
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)] [] 0 0 demo_limit
              (Z_to_bv 64 mmap_base_max) hi_sp)
            top_hi_model_rocq) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `noaccess_grant_at_demo_top_admitted_under_high_sp`, whose name
`Checks/Cases/Mm/Mmap.lean` holds for the spec-level twin.  The PROT_NONE
arm reads the same field, and records the grant in `vm_noaccess` too.
model: `State.alloc_top`, the band `vm_init_sp - stack_max_size` the
model imposes and `bugs/grants-into-the-stack-band.md` records -/
theorem noaccess_grant_at_demo_top_admitted_under_high_sp_by_the_checker :
    check_syscall (null_none_in 4096)
        (SyscallEffect.mkEffectU (Z_to_bv 64 demo_top) [] [] [(Z_to_bv 64 demo_top, 4096)] [] [])
        top_hi_model_rocq
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)] [(Z_to_bv 64 demo_top, 4096)]
              0 0 demo_limit (Z_to_bv 64 mmap_base_max) hi_sp)
            top_hi_model_rocq) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_rw_span_over_budget_errno_admitted`, the resolution
`mmap_fixed_rw_span_over_budget_rejected` leaves.  A 12 KiB rw MAP_FIXED
span over the 4 KiB live page of `span_tight_model` would leave 12 KiB
backed against the 8 KiB budget — Linux's charge is the 8 KiB of it that
met no live page, against the 4 KiB left — so -ENOMEM with no unmap and
no zeros is the forced out-of-memory answer: `__mmap_prepare` fails
`may_expand_vm` or `security_vm_enough_memory_mm` before `__mmap_region`
merges (`vma_merge_new_range`) or creates (`__mmap_new_vma`) any VMA, and
its `abort_munmap` path, `vms_abort_munmap_vmas`, reattaches the VMAs the
gather detached while no PTE has been cleared, so the pages the ledger
records stay mapped and the ledger is unchanged.
kernel: mm/vma.c:__mmap_prepare,__mmap_region,vms_abort_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_rw_span_over_budget_errno_admitted :
    check_syscall (mmap_in 65536 12288 3 50 mmap_fd_none 0)
        (mkEffect (errno_ret ENOMEM) [] []) span_tight_model
      = CheckOk span_tight_model [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_overflowing_len_is_enomem`, the answer
`mmap_fixed_overflowing_len_rejects_einval` above leaves.  A length within
a page of 2^64 rounds to zero in `do_mmap`'s machine arithmetic, and
`len = PAGE_ALIGN(len); if (!len) return -ENOMEM;` is answered before
`__get_unmapped_area` could read the misaligned address, so -ENOMEM with
no unmap and no zeros is admitted on the unchanged ledger.  qemu-user's
`target_mmap` rounds the length first too and answers the same -ENOMEM
(the reading is on `Sys/Mm/Mmap.lean`'s `mmap_pglen_ok_b`), so the answer
is inside the intersection.  Without this pin a checker refusing EVERY
errno at this input passes the refusal above.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_fixed_overflowing_len_is_enomem :
    check_syscall (mmap_in 4097 18446744073709551615 0 50 mmap_fd_none 0)
        (mkEffect (errno_ret ENOMEM) [] []) noaccess_base
      = CheckOk noaccess_base [] :=
  rfl

set_option maxRecDepth 32768 in
/-- NOT Rocq's: the accepting partner `mmap_null_hint_over_image_rejected`
has in no file of either tree.  On the same image-carrying ledger, a
NULL-hint grant on the free page just above the LOAD reservation,
`[0x12000, 0x13000)`, is admitted, so what the refusal above reads is the
image's own pages and not the presence of a reservation: a checker
refusing every grant on a non-empty `vm_reserved` passes every pin of
this section and of the Rocq file, and fails this one.
`unmapped_area_topdown` returns a gap free of the image's VMAs as of any
other's, and one abutting a VMA's end is a gap.
kernel: mm/vma.c:unmapped_area_topdown; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mmap_null_hint_beside_image_admitted :
    check_syscall (null_rw_in 4096)
        (mkEffect (Z_to_bv 64 0x12000) [] [(Z_to_bv 64 0x12000, 4096)]) placement_model_img
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [(Z_to_bv 64 0x10000, 8192)] [(Z_to_bv 64 0x12000, 4096)] []
              0 0 demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)
            placement_model_img) [] :=
  rfl

end K6c

section A18

/-! ## A18 — the MAP_FIXED_NOREPLACE arms

Rocq's block headed "MAP_FIXED_NOREPLACE: placed exactly, refused rather
than replaced" in `theories/LinuxProcessSem/Checks/Cases/Mm/Mmap.v`, under
Rocq's names, stated on `check_syscall` and closed by `rfl` as K6c's
section above closes its, except the two universal lemmas, which walk
`check_mmap` the way the checker's own proofs do.  Between Rocq's examples
and those two sit pins with no Rocq counterpart: the refusal at its edges,
the operands the spec and the checker share, the wrap-gate tripwires with
the address-0 wrap after them, and the witness at both new shapes; then
Rocq's one madvise example over this bit.  The brk block after the two
lemmas has no Rocq counterpart either: it states a wrong answer the ledger
gives.

The Rocq block keeps its examples out of the probe because the ledger after
each call is named literally and the two universal lemmas quantify over
every ledger and every address.  Its third reason, that the -EEXIST over
the image needs an image the probe cannot map over, is false and is not
carried: the refusal maps nothing (`do_mmap` returns at mm/mmap.c:410-413,
Linux v6.18.46, before `mmap_region` at :558), a probe's image sits at
0x10000, and both runners seed `vm_reserved` from its PT_LOAD headers
(`elf_load_reservations`, testing/syscall-check/main.ml:293-326;
`seedModel`, lean/LpsRunner/Replay.lean:196-199).  So that row is owed to
`mmap_fixed_noreplace.c`, and so are rows for an unaligned address inside
a live page, a range reaching `2^64` and a budget refusal (an
`--alloc-limit` case, as `mmap_noreserve.c` has); the spec twins'
`no-row:` lines name them.  Its `asan_shadow_fixed_after_null_grants_admitted`, which fixes
`placement_model_2`, is a MAP_FIXED example and is not twinned; the
fixture is. -/

/-- The flag words: the bit alone, with MAP_FIXED beside it, and with
MAP_NORESERVE beside it — the last is what a sealed sanitizer runtime
issues. -/
def noreplace_flags : word := 0x100022
def noreplace_fixed_flags : word := 0x100032
def noreplace_noreserve_flags : word := 0x104022

/-- `placement_model_1` after a second NULL-hint grant below the first:
the two floating grants a runtime has taken before it reserves its
shadows. -/
def placement_model_2 : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull []
      [(Z_to_bv 64 0x7fff7f7fe000, 4096), (Z_to_bv 64 0x7fff7f7ff000, 4096)] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model_1

/-- The sealed runtime's three reservations, at the addresses
AddressSanitizer derives from its 0x7fff8000 shadow offset on a 47-bit
address space: the low shadow (rw), the gap between the shadows
(PROT_NONE), the high shadow (rw). -/
def asan_low_shadow_in : SyscallInput :=
  mmap_in (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) 3 noreplace_noreserve_flags mmap_fd_none 0
def asan_gap_in : SyscallInput :=
  mmap_in (Z_to_bv 64 0x8fff7000) (Z_to_bv 64 0x20000000000) 0 noreplace_noreserve_flags mmap_fd_none 0
def asan_high_shadow_in : SyscallInput :=
  mmap_in (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000) 3 noreplace_noreserve_flags
    mmap_fd_none 0

/-- The ledger after each of the three. -/
def asan_after_low_shadow : Model :=
  vm_add_lazy (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000)
    (with_vmmaps
      (VmMaps.mkVmMapsFull []
        [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000),
         (Z_to_bv 64 0x7fff7f7fe000, 4096), (Z_to_bv 64 0x7fff7f7ff000, 4096)] [] 0 0 demo_limit
        (Z_to_bv 64 mmap_base_max) demo_sp) placement_model_2)
def asan_after_gap : Model :=
  vm_add_lazy (Z_to_bv 64 0x8fff7000) (Z_to_bv 64 0x20000000000)
    (with_vmmaps
      (VmMaps.mkVmMapsFull []
        [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000),
         (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000),
         (Z_to_bv 64 0x7fff7f7fe000, 4096), (Z_to_bv 64 0x7fff7f7ff000, 4096)]
        [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)] 0 0 demo_limit
        (Z_to_bv 64 mmap_base_max) demo_sp) asan_after_low_shadow)
def asan_after_high_shadow : Model :=
  vm_add_lazy (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000)
    (with_vmmaps
      (VmMaps.mkVmMapsFull []
        [(Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000),
         (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000),
         (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000),
         (Z_to_bv 64 0x7fff7f7fe000, 4096), (Z_to_bv 64 0x7fff7f7ff000, 4096)]
        [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)] 0 0 demo_limit
        (Z_to_bv 64 mmap_base_max) demo_sp) asan_after_gap)

set_option maxRecDepth 32768 in
/-- Rocq: `asan_sealed_startup_is_admitted`.  All three ranges are free,
so all three are admitted, each lands in the ledger exactly where it was
asked for, lazily backed.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem asan_sealed_startup_is_admitted :
    check_syscall asan_low_shadow_in
        (mkEffect (Z_to_bv 64 0x7fff7000) [] [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
        placement_model_2
      = CheckOk asan_after_low_shadow []
    ∧ check_syscall asan_gap_in
        (SyscallEffect.mkEffectU (Z_to_bv 64 0x8fff7000) [] []
          [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)] [] [])
        asan_after_low_shadow
      = CheckOk asan_after_gap []
    ∧ check_syscall asan_high_shadow_in
        (mkEffect (Z_to_bv 64 0x2008fff7000) [] [(Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000)])
        asan_after_gap
      = CheckOk asan_after_high_shadow [] :=
  ⟨rfl, rfl, rfl⟩

/-- A floating grant at 0x80000000, inside the future low shadow: the
collision the bit exists for. -/
def noreplace_collide_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 4096)] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model

set_option maxRecDepth 32768 in
/-- Rocq: `asan_sealed_low_shadow_over_a_grant_is_eexist`.  Under the bit
the low shadow over the grant is -EEXIST, and the ledger is untouched.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem asan_sealed_low_shadow_over_a_grant_is_eexist :
    check_syscall asan_low_shadow_in (mkEffect (errno_ret EEXIST) [] []) noreplace_collide_model
      = CheckOk noreplace_collide_model [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `asan_sealed_low_shadow_over_a_grant_success_rejected`.  The
answer MAP_FIXED would have given is refused.  (The hint arm would refuse
it too, the range not being free, so on its own this does not pin that
the bit is matched rather than stripped; the -EEXIST twin above and
`mmap_noreplace_with_fixed_over_live_is_eexist` pin that.)
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem asan_sealed_low_shadow_over_a_grant_success_rejected :
    check_syscall asan_low_shadow_in
        (mkEffect (Z_to_bv 64 0x7fff7000) [] [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
        noreplace_collide_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `asan_shadow_fixed_over_a_grant_replaces_where_noreplace_refuses`.
The same request spelled MAP_FIXED|MAP_NORESERVE (16434) over the same
ledger IS the spanning replacement: the grant inside the request is cut
out of `vm_maps` and the request takes its place.  The bit is what
separates the two answers, and both are Linux's.
kernel: mm/vma.c:__mmap_region,vms_gather_munmap_vmas@v6.18.46 -/
theorem asan_shadow_fixed_over_a_grant_replaces_where_noreplace_refuses :
    check_syscall (mmap_in (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) 3 16434 mmap_fd_none 0)
        (mkEffect (Z_to_bv 64 0x7fff7000) [] [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
        noreplace_collide_model
      = CheckOk
          (with_mmap_replacement 16434 (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000)
            (with_vmmaps
              (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)] [] 0 0
                demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)
              noreplace_collide_model)) [] :=
  rfl

/-- The request over `one_map_model`'s live page, and over the free page
above it. -/
def noreplace_over_live_in (prot flags : word) : SyscallInput :=
  mmap_in 65536 4096 prot flags mmap_fd_none 0
def noreplace_free_in (prot flags : word) : SyscallInput :=
  mmap_in 69632 4096 prot flags mmap_fd_none 0

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_over_live_is_eexist`.  Over a live page,
-EEXIST with the ledger unchanged, for both prot words.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_over_live_is_eexist :
    check_syscall (noreplace_over_live_in 3 noreplace_flags) (mkEffect (errno_ret EEXIST) [] [])
        one_map_model
      = CheckOk one_map_model []
    ∧ check_syscall (noreplace_over_live_in 0 noreplace_flags) (mkEffect (errno_ret EEXIST) [] [])
        one_map_model
      = CheckOk one_map_model [] :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_partial_overlap_is_eexist`.  ANY page of the
request: a two-page request whose second page is the live one is
refused, although its first page is free.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_partial_overlap_is_eexist :
    check_syscall (mmap_in 61440 8192 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) one_map_model
      = CheckOk one_map_model [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_over_live_success_rejected`.  A forged success
over a live page is refused, with or without the zero-fill a real grant
carries — the lie the bit exists to refuse.  Stripped, the bit-alone word
is the NULL-hint shape, which refuses a placement over a live page just
the same, so the strip is pinned by the -EEXIST twin above and by
`mmap_noreplace_with_fixed_over_live_is_eexist`.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_over_live_success_rejected :
    check_syscall (noreplace_over_live_in 3 noreplace_flags) (mkEffect 65536 [] [(65536, 4096)])
        one_map_model
      = CheckReject
    ∧ check_syscall (noreplace_over_live_in 3 noreplace_flags) (mkEffect 65536 [] []) one_map_model
      = CheckReject
    ∧ check_syscall (noreplace_over_live_in 0 noreplace_flags)
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject :=
  ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_over_live_einval_rejected`.  -EEXIST is the
errno, not just an errno: the gate's -EINVAL, which a model running the
refusal first could confuse it with, is refused on an aligned request.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem mmap_noreplace_over_live_einval_rejected :
    check_syscall (noreplace_over_live_in 3 noreplace_flags) (mkEffect (errno_ret EINVAL) [] [])
        one_map_model
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_over_live_enomem_admitted`.  `mm->map_count >
sysctl_max_map_count` is tested before the intersection (mm/mmap.c:377-378,
Linux v6.18.46) and the model counts no maps, so the environment's -ENOMEM
stays admitted.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_noreplace_over_live_enomem_admitted :
    check_syscall (noreplace_over_live_in 3 noreplace_flags) (mkEffect (errno_ret ENOMEM) [] [])
        one_map_model
      = CheckOk one_map_model [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_eexist_with_an_effect_rejected`.  A refusal
changes nothing, so an -EEXIST that also claims a zero-fill or an unmap
is refused.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_noreplace_eexist_with_an_effect_rejected :
    check_syscall (noreplace_over_live_in 3 noreplace_flags)
        (mkEffect (errno_ret EEXIST) [] [(65536, 4096)]) one_map_model
      = CheckReject
    ∧ check_syscall (noreplace_over_live_in 0 noreplace_flags)
        (SyscallEffect.mkEffectU (errno_ret EEXIST) [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_free_range_grants`.  Over a free page, an
ordinary grant naming its own address, recorded (and, rw, zero-filled)
exactly as the free-range MAP_FIXED sub-case records it.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_free_range_grants :
    check_syscall (noreplace_free_in 3 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(69632, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)
            one_map_model) []
    ∧ check_syscall (noreplace_free_in 0 noreplace_flags)
        (SyscallEffect.mkEffectU 69632 [] [] [(69632, 4096)] [] []) one_map_model
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(69632, 4096), (65536, 4096)] [(69632, 4096)] 0 0
              demo_limit 0 demo_sp)
            one_map_model) [] :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_free_range_eexist_rejected`.  On a free range
-EEXIST is not an answer: nothing the ledger records meets the request,
so `find_vma_intersection` finds nothing and Linux grants.  (What the
ledger does not record — the vdso/vvar pair, qemu-user's own guest vdso,
the host mappings qemu-user keeps for itself, such as its heap, which
without `-R` its host `mmap` answers EEXIST over
(`mmap_h_eq_g`, linux-user/mmap.c:612-625, QEMU 11.1.1, on a 4 KiB host;
`mmap_frag` or `mmap_h_gt_g`'s middle mapping, :372-386 and :884-898,
QEMU 11.1.1, on a 16 or 64 KiB host), qemu-user's reservation of the
gaps between LOAD segments, and the stack qemu-user maps whole under `-s`
or `QEMU_STACK_SIZE` above 8 MiB — is the residual of
bugs/mmap-placement-admits-unreachable-addresses.md, which names the first
three, of bugs/mmap-noreplace-refuses-qemu-user-eexist-in-a-load-gap.md
and of bugs/mmap-noreplace-refuses-qemu-user-eexist-on-a-large-stack.md.)
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_free_range_eexist_rejected :
    check_syscall (noreplace_free_in 3 noreplace_flags) (mkEffect (errno_ret EEXIST) [] [])
        one_map_model
      = CheckReject
    ∧ check_syscall (noreplace_free_in 0 noreplace_flags) (mkEffect (errno_ret EEXIST) [] [])
        one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_free_range_enomem_admitted`.  The free-range
grant keeps the environment errno, like every grant.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_noreplace_free_range_enomem_admitted :
    check_syscall (noreplace_free_in 3 noreplace_flags) (mkEffect (errno_ret ENOMEM) [] [])
        one_map_model
      = CheckOk one_map_model [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_with_fixed_over_live_is_eexist`.
MAP_FIXED | MAP_FIXED_NOREPLACE is MAP_FIXED_NOREPLACE: `do_mmap` folds
the bit into MAP_FIXED (mm/mmap.c:361-362, Linux v6.18.46) and tests the
bit alone (:410), so the combined word answers -EEXIST on a live page and
the replacement MAP_FIXED alone would perform is refused.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_noreplace_with_fixed_over_live_is_eexist :
    check_syscall (noreplace_over_live_in 3 noreplace_fixed_flags)
        (mkEffect (errno_ret EEXIST) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_syscall (noreplace_over_live_in 3 noreplace_fixed_flags)
        (mkEffect 65536 [] [(65536, 4096)]) one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_fixed_alone_over_live_replaces`, the anchor: MAP_FIXED
alone over the same page IS that replacement, so the bit, and only the
bit, turns the answer.
kernel: mm/vma.c:__mmap_region,vms_gather_munmap_vmas@v6.18.46 -/
theorem mmap_fixed_alone_over_live_replaces :
    check_syscall (noreplace_over_live_in 3 50) (mkEffect 65536 [] [(65536, 4096)]) one_map_model
      = CheckOk
          (with_mmap_replacement 50 65536 4096
            (with_vmmaps (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 demo_limit 0 demo_sp)
              one_map_model)) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_with_fixed_free_range_grants`.  On a free page
the combined word grants, as the bit alone does.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_with_fixed_free_range_grants :
    check_syscall (noreplace_free_in 3 noreplace_fixed_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(69632, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)
            one_map_model) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_over_the_image_is_eexist`.  Over the image's
LOAD reservation the MAP_FIXED spelling declines, having no way to
replace it; the NOREPLACE spelling replaces nothing and those pages are
mapped, so the answer is -EEXIST — for a request meeting the image and a
live page, and for one meeting the image alone — and a forged success
over the image is refused.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_over_the_image_is_eexist :
    check_syscall (mmap_in 65536 8192 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) image_span_model
      = CheckOk image_span_model []
    ∧ check_syscall (mmap_in 65536 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) image_span_model
      = CheckOk image_span_model []
    ∧ check_syscall (mmap_in 65536 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect 65536 [] [(65536, 4096)]) image_span_model
      = CheckReject :=
  ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_unaligned_inside_live_is_einval`.  Order is
behavior: `__get_unmapped_area`'s alignment -EINVAL is decided before
`do_mmap`'s intersection test, so an unaligned address inside the live
page is -EINVAL, and -EEXIST for it is refused.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem mmap_noreplace_unaligned_inside_live_is_einval :
    check_syscall (mmap_in 65537 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_syscall (mmap_in 65537 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_gate_matches_map_fixed`.
Linux returns -ENOMEM when the page-rounded length wraps to zero.
Linux handles zero length before address selection.
The model cannot resolve address zero or the stack band from this ledger.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem mmap_noreplace_gate_matches_map_fixed :
    check_syscall (mmap_in 4096 (Z_to_bv 64 (two_pow_64 - 1)) 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_syscall (mmap_in 0 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (mmap_in (Z_to_bv 64 demo_top) 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (mmap_in 65536 0 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Rocq: `mmap_noreplace_other_shapes_stay_unmodeled`.  The bit is
matched, not stripped, so every other declined shape stays declined with
it: an extra flag bit (MAP_POPULATE), MAP_SHARED, MAP_HUGETLB, an
executable prot, a nonzero offset, and a file-backed request.
kernel: mm/mmap.c:do_mmap,ksys_mmap_pgoff@v6.18.46 -/
theorem mmap_noreplace_other_shapes_stay_unmodeled :
    check_syscall (mmap_in 69632 4096 3 0x108022 mmap_fd_none 0) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (mmap_in 69632 4096 3 0x100021 mmap_fd_none 0) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (mmap_in 69632 4096 3 0x140022 mmap_fd_none 0) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (mmap_in 69632 4096 7 noreplace_flags mmap_fd_none 0)
        (mkEffect 69632 [] [(69632, 4096)]) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (mmap_in 69632 4096 3 noreplace_flags mmap_fd_none 4096)
        (mkEffect 69632 [] [(69632, 4096)]) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (mmap_in 69632 4096 3 0x100002 3 0) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! Beyond Rocq's block: the refusal at its edges, each with a spec twin
in `Checks/Cases/Mm/Mmap.lean`'s section of the same name. -/

set_option maxRecDepth 32768 in
/-- The destructive failure MAP_FIXED admits over a live page is no
NOREPLACE answer, for either prot word: the refusal returns at :410-413,
before `mmap_region` unmaps anything.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_over_live_destroyed_rejected :
    check_syscall (noreplace_over_live_in 3 noreplace_flags)
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject
    ∧ check_syscall (noreplace_over_live_in 0 noreplace_flags)
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- A PROT_NONE mapping refuses the request like any VMA: -EEXIST on the
middle of three inaccessible pages, and on the sealed runtime's gap
between the shadows.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_over_noaccess_is_eexist :
    check_syscall (mmap_in 69632 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) noaccess_three_pages
      = CheckOk noaccess_three_pages []
    ∧ check_syscall (mmap_in (Z_to_bv 64 0x8fff7000) 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) asan_after_gap
      = CheckOk asan_after_gap [] :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- The refusal is charged nothing: -EEXIST over the live page of a spent
budget.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_over_live_on_a_spent_budget_is_eexist :
    check_syscall (noreplace_over_live_in 3 noreplace_flags) (mkEffect (errno_ret EEXIST) [] [])
        spent_budget_model
      = CheckOk spent_budget_model [] :=
  rfl

set_option maxRecDepth 32768 in
/-- The PROT_NONE grant under the bit is free of charge, as without it
(`noaccess_grant_over_a_spent_budget_is_accepted` above), and reported as
an unmap: the same success as a zero-fill is refused.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mmap_noreplace_noaccess_grant_on_a_spent_budget :
    check_syscall (noreplace_free_in 0 noreplace_flags)
        (SyscallEffect.mkEffectU 69632 [] [] [(69632, 4096)] [] []) spent_budget_model
      = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(69632, 4096), (65536, 4096)]
          [(69632, 4096)] 0 0 4096 0 demo_sp)) []
    ∧ check_syscall (noreplace_free_in 0 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- The length is page-rounded (`do_mmap`, mm/mmap.c:368, Linux v6.18.46):
a 4097-byte request grants two pages, and the unrounded zero-fill is
refused.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_noreplace_rounds_the_length :
    check_syscall (mmap_in 69632 4097 3 noreplace_flags mmap_fd_none 0)
        (mkEffect 69632 [] [(69632, 8192)]) one_map_model
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(69632, 8192), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)
            one_map_model) []
    ∧ check_syscall (mmap_in 69632 4097 3 noreplace_flags mmap_fd_none 0)
        (mkEffect 69632 [] [(69632, 4097)]) one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- The grant-top bound is inclusive: a request ending exactly at
`alloc_top` grants.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem mmap_noreplace_ending_at_alloc_top_grants :
    check_syscall (mmap_in (Z_to_bv 64 (demo_top - 4096)) 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
        one_map_model
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096), (65536, 4096)] [] 0 0
              demo_limit 0 demo_sp)
            one_map_model) [] :=
  rfl

set_option maxRecDepth 32768 in
/-- MAP_FIXED | MAP_FIXED_NOREPLACE on the PROT_NONE spelling: -EEXIST over
the live page, and the reservation MAP_FIXED alone would make there is
refused.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_noreplace_with_fixed_noaccess_over_live_is_eexist :
    check_syscall (noreplace_over_live_in 0 noreplace_fixed_flags)
        (mkEffect (errno_ret EEXIST) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_syscall (noreplace_over_live_in 0 noreplace_fixed_flags)
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject :=
  ⟨rfl, rfl⟩

/-! The operands the spec and the checker share, read at the checker: each
pin below twins one in `Checks/Cases/Mm/Mmap.lean`'s section "Operands the
spec and the checker share", and fails on an edit that moves both sides at
once. -/

set_option maxRecDepth 32768 in
/-- The PROT_NONE spelling reads the image's LOAD reservation: over
`vm_reserved` alone the answer is -EEXIST, and the reservation a checker
reading `vm_maps` alone would accept there is refused.  Spec twins:
`noreplace_noaccess_over_the_image_iff` and its refutation.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_noaccess_over_the_image_is_eexist :
    check_syscall (mmap_in 65536 4096 0 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) image_span_model
      = CheckOk image_span_model []
    ∧ check_syscall (mmap_in 65536 4096 0 noreplace_flags mmap_fd_none 0)
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) image_span_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- The rw shape is PROT_READ|PROT_WRITE exactly: every other prot below 7
declines under the bit, offered the writable grant a widened
`mmap_noreplace_rw_b` would accept, and PROT_READ does with MAP_FIXED
beside the bit too.  Spec twins: `noreplace_read_only_is_unmodeled` and
the prots after it.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem mmap_noreplace_other_prots_stay_unmodeled :
    check_syscall (noreplace_free_in 1 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 2 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 4 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 5 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 6 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 1 noreplace_fixed_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Both shapes compare the whole prot word: a bit Linux ignores and
qemu-user refuses declines, offered Linux's grant on a free range and its
-EEXIST over the live page (0x13), with bit 31 set (0x80000003), and
beside PROT_NONE (0x10), offered the reservation.  A checker reading the
three low bits alone would accept each.  Spec twins:
`noreplace_high_prot_bit_is_unmodeled` and the pins after it.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem mmap_noreplace_high_prot_bits_stay_unmodeled :
    check_syscall (noreplace_free_in 19 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_over_live_in 19 noreplace_flags) (mkEffect (errno_ret EEXIST) [] [])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 2147483651 noreplace_flags)
        (mkEffect 69632 [] [(69632, 4096)]) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 16 noreplace_flags)
        (SyscallEffect.mkEffectU 69632 [] [] [(69632, 4096)] [] []) one_map_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- PROT_SEM beside rw (0xB) and bit 32 beside rw (0x100000003) decline
too, offered the grant both implementations give and the -EINVAL neither
gives.  A checker reading the three low bits alone would accept the grant,
and one refusing every bit past them as qemu-user refuses bits 4 to 31
would accept the -EINVAL.  Spec twins: `noreplace_prot_sem_is_unmodeled`
and the pins after it.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem mmap_noreplace_prot_sem_and_bit_32_stay_unmodeled :
    check_syscall (noreplace_free_in 11 noreplace_flags) (mkEffect 69632 [] [(69632, 4096)])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 11 noreplace_flags) (mkEffect (errno_ret EINVAL) [] [])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 4294967299 noreplace_flags)
        (mkEffect 69632 [] [(69632, 4096)]) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 4294967299 noreplace_flags)
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- MAP_LOCKED (0x102022), MAP_GROWSDOWN (0x100122) and MAP_STACK
(0x120022) beside the bit decline whatever effect is offered: MAP_LOCKED's
-EPERM (`do_mmap`, mm/mmap.c:415-417, Linux v6.18.46) and -EAGAIN
(:419-420), which a checker stripping the bit would refuse, on either prot;
the grant; and -EEXIST over the live page.  Spec twins:
`noreplace_locked_is_unmodeled` and the flag bits after it.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_flag_bits@v6.18.46 -/
theorem mmap_noreplace_vm_flag_bits_stay_unmodeled :
    check_syscall (noreplace_free_in 3 0x102022) (mkEffect (errno_ret EPERM) [] []) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 3 0x102022) (mkEffect (errno_ret EAGAIN) [] []) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 0 0x102022) (mkEffect (errno_ret EPERM) [] []) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 3 0x102022) (mkEffect 69632 [] [(69632, 4096)]) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_over_live_in 3 0x102022) (mkEffect (errno_ret EEXIST) [] [])
        one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 3 0x100122) (mkEffect 69632 [] [(69632, 4096)]) one_map_model
      = CheckUnmodeled
    ∧ check_syscall (noreplace_free_in 3 0x120022) (mkEffect 69632 [] [(69632, 4096)]) one_map_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_misaligned_wrapping_range_declines_enomem (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 3 1048610 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_misaligned_wrapping_range_declines_qemu_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 3 1048610 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_in_the_error_band_declines_the_shared_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) 4096 3 1048610 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_misaligned_wrapping_range_declines_enomem (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 0 1048610 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- Linux and QEMU check these bounds in different orders.
The spec records the source reading and the temporary decline.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_misaligned_wrapping_range_declines_qemu_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 0 1048610 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_in_the_error_band_declines_the_shared_einval (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) 4096 0 1048610 mmap_fd_none 0
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := by
  check_norm

/-- At address 0 the wrap gate is read before the address-0 decline, so a
wrapping length there is Linux's and qemu-user's -ENOMEM with the ledger
unchanged, on every ledger: `PAGE_ALIGN` wraps at mm/mmap.c:368-370
(Linux v6.18.46), before the address search runs…  Spec twin:
`noreplace_at_zero_wrapping_len_is_enomem`.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_at_zero_wrapping_len_accepts_enomem (m : Model) :
    check_mmap 0 (Z_to_bv 64 (-1)) 3 1048610 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckOk m [] := by
  check_norm

/-- …and -EEXIST there refused…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_at_zero_wrapping_len_refuses_eexist (m : Model) :
    check_mmap 0 (Z_to_bv 64 (-1)) 3 1048610 mmap_fd_none 0 (mkEffect (errno_ret EEXIST) [] []) m
      = CheckReject := by
  check_norm

/-- …on the PROT_NONE arm as on the rw one…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_noaccess_at_zero_wrapping_len_accepts_enomem (m : Model) :
    check_mmap 0 (Z_to_bv 64 (-1)) 0 1048610 mmap_fd_none 0 (mkEffect (errno_ret ENOMEM) [] []) m
      = CheckOk m [] := by
  check_norm

/-- …with -EEXIST refused there too.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_noaccess_at_zero_wrapping_len_refuses_eexist (m : Model) :
    check_mmap 0 (Z_to_bv 64 (-1)) 0 1048610 mmap_fd_none 0 (mkEffect (errno_ret EEXIST) [] []) m
      = CheckReject := by
  check_norm

/-- The witness at a NOREPLACE request past the gate is the errno arm,
over a free range and over a live page alike: both ledger sub-cases carry
it, so the witness tests no ledger.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem witness_at_noreplace_is_enomem :
    mmap_witness 69632 4096 3 1048610 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret ENOMEM) one_map_model
    ∧ mmap_witness 65536 4096 0 1048610 mmap_fd_none 0 one_map_model
      = ret_outcome (errno_ret ENOMEM) one_map_model := by
  constructor <;> witness_norm

/-- The witness at NOREPLACE address 0 is the decline the checker gives.
kernel: mm/mmap.c:__get_unmapped_area; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem witness_at_noreplace_zero_is_unmodeled :
    mmap_witness 0 4096 3 1048610 mmap_fd_none 0 one_map_model = Unmodeled := by
  witness_norm

/-! From Rocq's `theories/LinuxProcessSem/Checks/Cases/Mm/Madvise.v`
rather than this block: the one of its four examples over the mmap arm
that places its grant with this bit.  `Checks/Cases/Checks/Sys/Mm/Madvise.lean`'s
header says why their checker twins belong in this file. -/

set_option maxRecDepth 32768 in
/-- Rocq: `madvise_lazy_grant_by_noreplace`.  A MAP_FIXED_NOREPLACE grant
with MAP_NORESERVE beside it (`noreplace_noreserve_flags`, 1064994) at
65536, over the empty ledger of `Checks/Cases/Mm/Madvise.lean`, is
accepted with `madvise_lazy_granted` as its post-state, the lazy entry
that file's madvise pins are stated over: nothing meets the range
(`do_mmap`, mm/mmap.c:410-412, Linux v6.18.46), and MAP_NORESERVE becomes
VM_NORESERVE outside strict overcommit (:548-551).  So each of those pins
holds of a NOREPLACE-placed shadow mapping as it stands.  Spec twin:
`lazy_grant_by_noreplace`.
no-row: madvise_dontneed records this shape at seq 2 of traces 004-006, at the address its seq-0 grant returned rather than 65536, and that effect zero-fills the grant, which the oracle-pin corpus scan keeps no row for.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem madvise_lazy_grant_by_noreplace :
    check_syscall (mmap_in 65536 8192 3 noreplace_noreserve_flags mmap_fd_none 0)
        (mkEffect 65536 [] [(65536, 8192)]) Checks.Cases.Mm.Madvise.madvise_lazy_base
      = CheckOk Checks.Cases.Mm.Madvise.madvise_lazy_granted [] :=
  rfl

/-- Rocq: `mmap_noreplace_occupied_answers_only_errnos`.  OVER A RANGE THE
LEDGER HOLDS NOTHING BUT AN ERRNO IS ACCEPTED, for every ledger, every
address and every length: whatever the checker accepts leaves the model
unchanged, carries no zero-fill and no unmap, and returns one of the
gate's two errnos or -EEXIST.  Stated over the checker;
`check_mmap_sound_ok` and `check_mmap_complete_ok` carry it to
`mmap_spec`.  The ledger is not the VMA tree: a same-page brk grow can
ledger bytes no VMA backs, and over those this refuses the grant Linux
gives (`noreplace_over_unbacked_brk_bytes_refuses_the_grant` below;
bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md).
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_occupied_answers_only_errnos (addr len fd r : word)
    (zs us : List (word × word)) (m m' : Model) (evs : List event)
    (hocc : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false)
    (h : check_mmap addr len 3 noreplace_noreserve_flags fd 0
      (SyscallEffect.mkEffectU r [] zs us [] []) m = CheckOk m' evs) :
    m' = m ∧ evs = [] ∧ zs = [] ∧ us = []
    ∧ (r = errno_ret ENOMEM ∨ r = errno_ret EINVAL ∨ r = errno_ret EEXIST) := by
  unfold check_mmap at h
  dsimp only at h
  rw [ite_eq_right (show ¬((!mmap_off_aligned_b 0) = true) by decide),
    ite_eq_right (show ¬((!mmap_anon_b noreplace_noreserve_flags) = true) by decide)] at h
  by_cases hl : w_is0 len = true
  · rw [ite_eq_left hl,
      ite_eq_left (show mmap_plain_anon_b noreplace_noreserve_flags = true by decide)] at h
    obtain ⟨he, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    cases he
    exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inl rfl)⟩
  rw [ite_eq_right hl,
    ite_eq_right (show ¬(mmap_modeled_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_noaccess_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_fixed_noaccess_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_fixed_rw_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_noreplace_noaccess_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_left (show mmap_noreplace_rw_b 3 noreplace_noreserve_flags 0 = true by decide)] at h
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h
  by_cases hg : two_pow_64 ≤ X
  · rw [ite_eq_left hg] at h
    have hret : check_ret_only (SyscallEffect.mkEffectU r [] zs us [] [])
        (errno_ret ENOMEM) m [] = CheckOk m' evs := by
      generalize page_round_up_Z (bv_unsigned len) = N at h
      generalize bv_unsigned addr = A at h
      split at h
      · exact h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · exact h
          · cases h
    obtain ⟨he, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp hret
    cases he
    exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
  rw [ite_eq_right hg] at h
  by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
  · rw [ite_eq_left hc] at h
    cases h
  rw [ite_eq_right hc] at h
  by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
  · rw [ite_eq_left ha] at h
    obtain ⟨he, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    cases he
    exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inl rfl)⟩
  rw [ite_eq_right ha] at h
  by_cases hz : (!decide (0 < bv_unsigned addr)) = true
  · rw [ite_eq_left hz] at h
    cases h
  rw [ite_eq_right hz, hocc, ite_eq_right Bool.false_ne_true] at h
  cases zs <;> cases us <;> dsimp only at h <;> try cases h
  split at h
  · rename_i he
    cases h
    rw [Bool.or_eq_true] at he
    rcases he with he | he
    · obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
      simp only [mmap_errnos, List.mem_singleton] at hin
      subst hin
      exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inr ((bv_eqb_eq _ _).mp he))⟩
  · cases h

/-- Rocq: `mmap_noreplace_free_range_never_eexist`.  OVER A FREE RANGE
-EEXIST IS NEVER ACCEPTED, for every ledger, every address and every
length: nothing the ledger records meets the request, so no kernel reading
only its VMA tree could refuse it.  An implementation that would — holding
a mapping the ledger does not carry — is the residual
bugs/mmap-placement-admits-unreachable-addresses.md names for the vdso/vvar
pair, for qemu-user's own guest vdso and for the host mappings qemu-user
keeps for itself, such as its heap, which without `-R` its host `mmap`
answers EEXIST over
(`mmap_h_eq_g`, linux-user/mmap.c:612-625, QEMU 11.1.1, on a 4 KiB host;
`mmap_frag` or `mmap_h_gt_g`'s middle mapping, :372-386 and :884-898,
QEMU 11.1.1, on a 16 or 64 KiB host),
bugs/mmap-noreplace-refuses-qemu-user-eexist-in-a-load-gap.md names
for qemu-user's reservation of the gaps between LOAD segments, and
bugs/mmap-noreplace-refuses-qemu-user-eexist-on-a-large-stack.md names for
the stack qemu-user maps whole under `-s` or `QEMU_STACK_SIZE` above 8 MiB.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_free_range_never_eexist (addr len fd : word) (zs us : List (word × word))
    (m m' : Model) (evs : List event)
    (hfree : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true) :
    check_mmap addr len 3 noreplace_noreserve_flags fd 0
      (SyscallEffect.mkEffectU (errno_ret EEXIST) [] zs us [] []) m ≠ CheckOk m' evs := by
  intro h
  have hEEXIST : bv_unsigned (errno_ret EEXIST) = two_pow_64 - EEXIST :=
    errno_ret_unsigned EEXIST (by unfold EEXIST; omega) (by unfold EEXIST; omega)
  have hne : ∀ e, 1 ≤ e → e ≤ 4095 → e ≠ EEXIST → errno_ret EEXIST ≠ errno_ret e := by
    intro e h1 h2 hne heq
    have := congrArg bv_unsigned heq
    rw [hEEXIST, errno_ret_unsigned e h1 h2] at this
    exact hne (by omega)
  have hroom := alloc_top_room (m_vmmaps m)
  unfold stack_max_size at hroom
  unfold check_mmap at h
  dsimp only at h
  rw [ite_eq_right (show ¬((!mmap_off_aligned_b 0) = true) by decide),
    ite_eq_right (show ¬((!mmap_anon_b noreplace_noreserve_flags) = true) by decide)] at h
  by_cases hl : w_is0 len = true
  · rw [ite_eq_left hl,
      ite_eq_left (show mmap_plain_anon_b noreplace_noreserve_flags = true by decide)] at h
    obtain ⟨he, _, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    injection he with hr
    exact hne EINVAL (by unfold EINVAL; omega) (by unfold EINVAL; omega)
      (by unfold EINVAL EEXIST; omega) hr
  rw [ite_eq_right hl,
    ite_eq_right (show ¬(mmap_modeled_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_noaccess_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_fixed_noaccess_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_fixed_rw_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_right (show ¬(mmap_noreplace_noaccess_b 3 noreplace_noreserve_flags 0 = true) by decide),
    ite_eq_left (show mmap_noreplace_rw_b 3 noreplace_noreserve_flags 0 = true by decide)] at h
  have hnz := page_round_up_Z_nonneg _ (word_unsigned_range len).1
  generalize hX : bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h
  by_cases hg : two_pow_64 ≤ X
  · rw [ite_eq_left hg] at h
    have hret : check_ret_only (SyscallEffect.mkEffectU (errno_ret EEXIST) [] zs us [] [])
        (errno_ret ENOMEM) m [] = CheckOk m' evs := by
      generalize page_round_up_Z (bv_unsigned len) = N at h
      generalize bv_unsigned addr = A at h
      split at h
      · exact h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · exact h
          · cases h
    obtain ⟨he, _, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp hret
    injection he with hr
    exact hne ENOMEM (by unfold ENOMEM; omega) (by unfold ENOMEM; omega)
      (by unfold ENOMEM EEXIST; omega) hr
  rw [ite_eq_right hg] at h
  by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
  · rw [ite_eq_left hc] at h
    cases h
  rw [ite_eq_right hc] at h
  by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
  · rw [ite_eq_left ha] at h
    obtain ⟨he, _, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    injection he with hr
    exact hne EINVAL (by unfold EINVAL; omega) (by unfold EINVAL; omega)
      (by unfold EINVAL EEXIST; omega) hr
  rw [ite_eq_right ha] at h
  by_cases hz : (!decide (0 < bv_unsigned addr)) = true
  · rw [ite_eq_left hz] at h
    cases h
  rw [ite_eq_right hz, hfree, ite_eq_left rfl] at h
  have hc' := of_not_gate hc
  cases us
  · dsimp only at h
    rw [ite_eq_right (show ¬(errno_ret_in mmap_errnos (errno_ret EEXIST) = true) by
      intro hin
      obtain ⟨e, he, heq⟩ := (errno_ret_in_true _ _).mp hin
      simp only [mmap_errnos, List.mem_singleton] at he
      subst he
      exact hne ENOMEM (by unfold ENOMEM; omega) (by unfold ENOMEM; omega)
        (by unfold ENOMEM EEXIST; omega) heq)] at h
    split at h
    · rename_i hC
      rw [Bool.and_eq_true, Bool.and_eq_true, bv_eqb_eq] at hC
      have hr := congrArg bv_unsigned hC.1.1
      rw [hEEXIST] at hr
      unfold EEXIST at hr
      omega
    · cases h
  · dsimp only at h
    cases h

/-! A recorded wrong answer: bytes the ledger holds and no VMA backs.
`Checks/VmMapsDisjoint.lean`'s witness process, at its step 4, has
unmapped both heap pages on Linux and left its break mid-page in the
lower one.  A grow inside that page takes the `oldbrk == newbrk` exit
(`brk`, mm/mmap.c:153-158, Linux v6.18.46), as qemu-user's `do_brk` does
(linux-user/syscall.c:884-888, QEMU 11.1.1), and maps nothing, but
`brk_maps_next` ledgers the grown bytes.  Over them both NOREPLACE arms
refuse the grant Linux gives, which
bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md records.  The pins
state that wrong answer, beside the grant the same request gets one step
earlier. -/

/-- The witness ledger after brk(0x10834) from step 4: the hundred bytes
from the break, in a page no VMA backs. -/
def brk_unbacked_ledger : Model :=
  with_vmmaps (Checks.VmMapsDisjoint.wit_vm [(67536, 100)] 65536 67636
    Checks.VmMapsDisjoint.wit_limit) Checks.VmMapsDisjoint.wit_s0

/-- The step itself: a same-page grow from `wit_s4`'s break is accepted
with the hundred bytes in `vm_maps`, where Linux's exit maps nothing.
Recorded in bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md.
no-row: stated over the witness chain's hand-built ledger, and no recorded run makes this call.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_grow_ledgers_unbacked_bytes :
    check_syscall (brk_in 67636) (mkEffect 67636 [] []) Checks.VmMapsDisjoint.wit_s4
      = CheckOk brk_unbacked_ledger [] :=
  rfl

set_option maxRecDepth 32768 in
/-- Before that step the page is free in the ledger as on Linux, and one
NOREPLACE page at 0x10000 is granted on either prot: the rw grant lands
where `wit_s5` has it…
no-row: stated over the witness chain's hand-built ledger, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_at_the_emptied_heap_page_grants :
    check_syscall (mmap_in 65536 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect 65536 [] [(65536, 4096)]) Checks.VmMapsDisjoint.wit_s4
      = CheckOk Checks.VmMapsDisjoint.wit_s5 []
    ∧ check_syscall (mmap_in 65536 4096 0 noreplace_flags mmap_fd_none 0)
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) Checks.VmMapsDisjoint.wit_s4
      = CheckOk
          (with_vmmaps
            (VmMaps.mkVmMapsFull Checks.VmMapsDisjoint.wit_reserved [(65536, 4096)] [(65536, 4096)]
              65536 67536 Checks.VmMapsDisjoint.wit_limit Checks.VmMapsDisjoint.wit_mmap_base
              (Z_to_bv 64 sp_window_lo))
            Checks.VmMapsDisjoint.wit_s4) [] :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- …and after it the same two grants are refused, though Linux, whose
`find_vma_intersection` finds no VMA in `[0x10000, 0x11000)` (`do_mmap`,
mm/mmap.c:410-413, Linux v6.18.46), gives each: the wrong answer
bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md records.  It is
stated over the literal ledger, so a fix to brk flips the step pin above
and leaves this one standing over a ledger no run reaches; the fix
retires the two together.
no-row: stated over the witness chain's hand-built ledger, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_unbacked_brk_bytes_refuses_the_grant :
    check_syscall (mmap_in 65536 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect 65536 [] [(65536, 4096)]) brk_unbacked_ledger
      = CheckReject
    ∧ check_syscall (mmap_in 65536 4096 0 noreplace_flags mmap_fd_none 0)
        (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) brk_unbacked_ledger
      = CheckReject :=
  ⟨rfl, rfl⟩

/-! A recorded wrong answer: qemu-user's guest vdso below `alloc_top` under
`-R`.  bugs/mmap-placement-admits-unreachable-addresses.md records the
vdso qemu-user maps for its guest, which the ledger does not carry, and
the routes that put it below `alloc_top` with the entry `sp` inside
`Run.valid_sp`'s window; the pin states one of them. -/

/-- The ledger a run starts with, as measured under qemu-riscv64 11.1.1
with `-R 0x7fff81000000` on a 16 KiB arm64 host with a 52-bit address
space: the image's page-rounded LOAD pages at 0x2aaaaaab0000,
0x2aaaaaab1000 and 0x7fff807fb000, nothing mapped, the break at the
image's top, and the entry `sp` qemu gave, 0x7fff80fffe80. -/
def qemu_vdso_in_a_gap_ledger : Model :=
  fixture (VmMaps.mkVmMapsFull
    [(0x2aaaaaab0000, 0x1000), (0x2aaaaaab1000, 0x11000), (0x7fff807fb000, 0x1000)] [] []
    0x7fff807fc000 0x7fff807fc000 demo_limit 0 0x7fff80fffe80)

set_option maxRecDepth 32768 in
/-- inherited-divergence: bugs/mmap-placement-admits-unreachable-addresses.md --
qemu reserves the image's whole span, 0x2aaaaaab0000 to 0x7fff807fc000,
before it maps the segments (`load_elf_image`,
linux-user/elfload.c:1065-1075, QEMU 11.1.1), and its own lowest-fit
search from `task_unmapped_base` (`page_find_range_empty`,
accel/tcg/user-exec.c:583-621, QEMU 11.1.1) finds room for the stack only
above that span, while the vdso takes the 16 KiB left below the image, at
0x2aaaaaaac000, below `alloc_top`.  A NOREPLACE request on the vdso is
EEXIST from qemu's own page table (`page_check_range_empty`,
linux-user/mmap.c:925-931, QEMU 11.1.1), and was measured so.  The ledger
calls the page free, and the checker refuses the -EEXIST.  Stated over the
literal ledger, so the fix, which admits -EEXIST where qemu's vdso may
lie, restates it.
no-row: stated over a hand-built ledger at measured addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mmap_noreplace_on_qemus_vdso_under_r_eexist_rejected :
    check_syscall (mmap_in 0x2aaaaaaac000 4096 0 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EEXIST) [] []) qemu_vdso_in_a_gap_ledger
      = CheckReject :=
  rfl

set_option maxRecDepth 32768 in
/-- Recorded in
bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md:
qemu-user run without `-R` on a 16 or 64 KiB host with `guest_base` 0
maps a request at 4096 through host page 0 and hands back the host's
-EPERM, which `cap_mmap_addr` gives a caller without `CAP_SYS_RAWIO`
there at the default floor (security/commoncap.c:1459-1471, Linux
v6.18.46); the checker refuses it.  The spec twin, with the route, is
`noreplace_first_host_page_eperm_rejected` in `Checks/Cases/Mm/Mmap.lean`.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: security/commoncap.c:cap_mmap_addr; mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_noreplace_first_host_page_eperm_rejected :
    check_syscall (mmap_in 4096 4096 3 noreplace_flags mmap_fd_none 0)
        (mkEffect (errno_ret EPERM) [] []) one_map_model
      = CheckReject :=
  rfl

end A18

-- lean-port sentinel: ticket C-Mm-Mmap-brk-munmap appends below this line

section C_Mm_Mmap_brk_munmap

/-! ## C-Mm-Mmap-brk-munmap — `check_brk`, `check_munmap` and their witnesses

WHAT IS TWINNED.  `theories/LinuxProcessSem/Checks/Cases/Mm/Mmap.v` states
its brk and munmap examples on `check_syscall`, the dispatcher of
`Checks/ExecutableSpecs.v`, and closes each by `vm_compute`.  The Lean
`check_syscall` over `checked_table` carries no row for 214 or 215 until
the conformance ticket registers the two arms (BRIEF.md section 5, the
VERIFY block: registration first), so each twin here is stated on the
checker itself — `check_brk` at the request Rocq's `brk_in` carries in
`a0`, `check_munmap` at the address and length Rocq's `mkInput 215 [addr;
len; …]` carries in `a0` and `a1` — with the same offered effect and the
same fixture, the way `Checks/Cases/Checks/Sys/Mm/Mprotect.lean` states
its checker's.  Which register each argument is read from is the arm's
claim and goes with the registration; the dispatcher-level restatements
of these twins go with it too.  The names are the Rocq examples' names, in
this file's own namespace: `Checks/Cases/Mm/Mmap.lean` already carries a
spec-level pin of each claim, stated on `brk_spec` or `munmap_spec` with
the kernel reading beside it — under the same name, except that
`munmap_unaligned_einval`, `munmap_len_zero_einval`,
`munmap_ordinary_still_succeeds` and `munmap_partial_is_error` keep their
Rocq names here while the spec-level pins are `munmap_unaligned_is_einval`,
`munmap_len_zero_is_einval`, `munmap_exact_grant` and
`munmap_partial_is_unmodeled` — so the two files together say (spec ↔
kernel) and (checker → the same answer), and the soundness and
completeness lemmas of `Checks/Sys/Mm/Mmap.lean` say the two agree
everywhere and not only here.  The section "Beyond the Rocq twins" holds
pins with no Rocq checker example behind them; each takes the name of the
spec-level pin whose answer it carries down to the checker, or its own
where there is none.  Every `= CheckReject` example the Rocq file states
on brk or munmap is here under its Rocq name; those are the ones K6c's
paragraph WHAT IS NOT TWINNED leaves to this section.  The subsection
after the witnesses' states, for each decision the twins reach from one
side only, the other side.

HOW A PIN CLOSES.  Rocq's `check_eq` is `vm_compute`, then
`reflexivity` — descending by `f_equal` and closing a `bv` leaf by
`bv_eq` where an opaque `BvWf` proof stands in the way
(`Checks/Cases/Prelude.v:20-25`).  The closer here is the tree's
normalizer, `sys_norm`,
after the checker or witness the statement names is unfolded — K6b's
`check_norm` shape above, and the closer BRIEF.md names for a Cases file
— and not `rfl`, which is what K6c's pattern uses for `check_mmap`.
`rfl` at the elaborator's default transparency dies of `maximum
recursion depth` on the closed `Int` terms the munmap gates form; the
minimal shape is `page_round_up_Z (bv_unsigned (0 : word)) = 0`, which
`rfl` refuses at every `maxRecDepth` tried up to 8192 and `decide` closes
at once — the mechanism `Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean`'s
header traces through `Int.subNatNat`, a `Nat.sub` recursing on the
literal.  `decide` alone is not available either: `Model` has no
`DecidableEq`, so a model equality is not a `Decidable` proposition, and
`sys_norm`'s ground pass is what reduces both sides to one constructor
tree.  The first cut of this section closed by a private two-pass
`simp +ground +decide only` over the checkers' equations — `sys_norm`'s
two passes re-implemented without the shared `sys_simp` set, and with a
flakiness its docstring could only describe; `sys_norm` closes every
pin of the section in the same wall time, so the shared closer is the one
used.

POLARITY.  A pin stated `= CheckReject` or `= CheckUnmodeled` is POSITIVE
to `tools/check_lean_pin_evidence.py` — its negative marker is the word
`Unmodeled` on its own, which `CheckUnmodeled` does not match — so it may
not cite the `reject --mutate` or `fail-closed` probe case that is its
evidence in the harness.  It cites the kernel function whose answer the
refused lie contradicts, or `model:` where the refusal is the run's own
budget; the probe case, where one exists, is named in prose.

WHY THESE PINS AT ALL, when the eight lemmas exist.  The lemmas prove the
checker and the spec say the same thing; they cannot notice both saying
the wrong thing.  A pin names a concrete answer from OUTSIDE — the errno
`do_vmi_munmap` returns, the unchanged break `brk` hands back — and
requires the executable side to produce it, or to refuse the lie a
mutated kernel would tell (`CheckReject`) or to decline where the ledger
cannot answer (`CheckUnmodeled`).  Every kernel claim below cites the
function and lines it was read from, at Linux v6.18.46. -/

/-- The closer: unfold whichever of the two checkers, the two witnesses
and `check_ret_only` the statement names, then `sys_norm`.  `try`, because
`unfold` of a name the goal does not contain is an error and a site names
one checker or one witness, never all.  `scoped`, for the reason
`check_norm` above gives. -/
scoped macro "brk_munmap_norm" : tactic =>
  `(tactic| ((try unfold check_brk); (try unfold check_munmap); (try unfold brk_witness);
             (try unfold munmap_witness); (try unfold check_ret_only); sys_norm))

/-! ### munmap: the gates

`do_vmi_munmap` (mm/vma.c:1604-1627, Linux v6.18.46) refuses an unaligned
start, a start past `TASK_SIZE` and a length past it (:1611-1612) and a
zero page-rounded length (:1614-1616) with -EINVAL; finds no VMA and
answers 0 (:1619-1623); or tears the range down (:1626). -/

/-- An unaligned address is -EINVAL and nothing changes (`offset_in_page(start)`,
mm/vma.c:1611-1612, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unaligned_einval :
    check_munmap 65537 4096 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] := by
  brk_munmap_norm

/-- A zero length is -EINVAL: `end == start` (mm/vma.c:1614-1616, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_len_zero_einval :
    check_munmap 65536 0 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] := by
  brk_munmap_norm

/-- A mapping the model holds just under `2^64` is refused with -EINVAL before
the ledger is read: `start > TASK_SIZE` (mm/vma.c:1611-1612, Linux v6.18.46);
and a kernel claiming to have unmapped it is refused.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_near_max_is_einval :
    check_munmap (Z_to_bv 64 (two_pow_64 - 8192)) 4096
        (mkEffect (errno_ret EINVAL) [] []) near_ceiling_sum_model
      = CheckOk near_ceiling_sum_model []
    ∧ check_munmap (Z_to_bv 64 (two_pow_64 - 8192)) 4096
        (SyscallEffect.mkEffectU 0 [] [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)] [] [])
        near_ceiling_sum_model
      = CheckReject := by
  constructor <;> brk_munmap_norm

/-- `start = 2^63`, `len = 2^63`: Linux's `start > TASK_SIZE` refuses it
before `end` is formed (mm/vma.c:1611-1612, Linux v6.18.46), and the model's
`Int` sum, `2^64`, sees the same; a 0 is refused.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_high_addr_sum_wraps_is_einval :
    check_munmap (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_munmap (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63))
        (mkEffect 0 [] []) one_map_model
      = CheckReject := by
  constructor <;> brk_munmap_norm

/-! ### munmap: the free range, the exact mapping and the partial one -/

/-- A range holding no mapped page is a no-op 0: `vma_find` finds nothing
(mm/vma.c:1619-1623, Linux v6.18.46), and the ledger is untouched.
probe: testing/syscall-check/tests/munmap_va_limit.c#conform -- highrepeat -/
theorem munmap_free_range_noop :
    check_munmap 131072 4096 (mkEffect 0 [] []) one_map_model
      = CheckOk one_map_model [] := by
  brk_munmap_norm

/-- The free-range arm's bound is this run's `alloc_top`, inclusive: a free
page ending exactly at it is the no-op 0 of `do_vmi_munmap` (mm/vma.c:1619-1623,
Linux v6.18.46).  The fixture's stack pointer is demo_sp, so its alloc_top is
demo_top.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_free_range_ending_at_alloc_top_is_noop :
    check_munmap (Z_to_bv 64 (demo_top - 4096)) 4096 (mkEffect 0 [] []) one_map_model
      = CheckOk one_map_model [] := by
  brk_munmap_norm

/-- …and the page above it is in the stack band the ledger does not describe,
so the checker declines: Linux answers 0 whether the page is free or the
stack's (mm/vma.c:1619-1626, Linux v6.18.46), and the model cannot tell which.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_free_range_in_the_stack_band_is_unmodeled :
    check_munmap (Z_to_bv 64 demo_top) 4096 (mkEffect 0 [] []) one_map_model
      = CheckUnmodeled := by
  brk_munmap_norm

/-- An exact mapping is torn down (`do_vmi_align_munmap`, mm/vma.c:1557, reached
from :1626, Linux v6.18.46): 0, the entry leaves the ledger, and the effect
declares the range.
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_ordinary_still_succeeds :
    check_munmap 65536 4096 (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckOk (with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) one_map_model) [] := by
  brk_munmap_norm

/-- A 0 that declares no unmap over a live page is refused: the VMA really
goes on Linux (mm/vma.c:1626, Linux v6.18.46), so the memory is inaccessible
afterwards and an effect that keeps it mapped is a lie.
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_without_unmap_rejected :
    check_munmap 65536 4096 (mkEffect 0 [] []) one_map_model = CheckReject := by
  brk_munmap_norm

/-- Unmapping an exact, wholly inaccessible mapping drops it from BOTH
ledgers; Linux tears a `PROT_NONE` VMA down like any other (mm/vma.c:1626,
Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_exact_noaccess_removes_both_ledgers :
    check_munmap 65536 12288 (SyscallEffect.mkEffectU 0 [] [] [(65536, 12288)] [] [])
        noaccess_three_pages
      = CheckOk (with_vmmaps (VmMaps.mkVmMapsFull [] [] [] 0 0 16384 0 demo_sp)
                   noaccess_three_pages) [] := by
  brk_munmap_norm

/-- Unmapping a lazily backed, touched mapping forgets its lazy provenance and
its materialized pages with the VMA (`do_vmi_align_munmap`, mm/vma.c:1557,
reached from :1626, Linux v6.18.46): the post-model is the bare ledger.
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_forgets_lazy_and_materialized_metadata :
    check_munmap 65536 8192 (SyscallEffect.mkEffectU 0 [] [] [(65536, 8192)] [] [])
        mmap_lazy_materialized
      = CheckOk (with_mmap_destroyed 65536 8192 (mkVmMaps [] [] 0 0 8192)
                   mmap_lazy_materialized) [] := by
  brk_munmap_norm

/-- A range covering one page of a two-page mapping is neither the exact
mapping nor free: Linux splits the mapping at `end` (`__split_vma` from
`vms_gather_munmap_vmas`, mm/vma.c:1421-1422, reached through
`do_vmi_align_munmap` :1569 from `do_vmi_munmap` :1626, Linux v6.18.46)
and unmaps the head; the model does not describe a split, so the checker
declines rather than guess.
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap,vms_gather_munmap_vmas@v6.18.46 -/
theorem munmap_partial_is_error :
    check_munmap 65536 4096 (mkEffect 0 [] []) two_page_map_model = CheckUnmodeled := by
  brk_munmap_norm

/-! ### brk: the query and the invalid request

`SYSCALL_DEFINE1(brk)` (mm/mmap.c:115-213, Linux v6.18.46) saves
`origbrk = mm->brk` (:128), reads `min_brk = mm->start_brk` (:130) and
takes `if (brk < min_brk) goto out;` (:140-141); `out:` restores
`mm->brk = origbrk` and returns it (:209-212). -/

/-- `brk(0)` on an established break returns the current break unchanged
(mm/mmap.c:140-141, :209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_zero_returns_current_break :
    check_brk 0 (mkEffect 65536 [] []) m_est = CheckOk m_est [] := by
  brk_munmap_norm

/-- …and a query does not return an arbitrary value: `out:` returns
`origbrk` and nothing else (mm/mmap.c:209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_zero_rejects_arbitrary :
    check_brk 0 (mkEffect 123456 [] []) m_est = CheckReject := by
  brk_munmap_norm

/-- A query leaves the no-access ledger alone: Linux's query path touches no
VMA (mm/mmap.c:140-141, :209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_query_preserves_noaccess :
    check_brk 0 (mkEffect 69632 [] []) noaccess_brk_model = CheckOk noaccess_brk_model [] := by
  brk_munmap_norm

/-- A request in the ASLR gap below `mm->start_brk` is `brk < min_brk`
(mm/mmap.c:130, :140-141, Linux v6.18.46): the break comes back unchanged.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_in_aslr_gap_returns_break :
    check_brk 16384 (mkEffect 65536 [] []) m_est = CheckOk m_est [] := by
  brk_munmap_norm

/-- …and a kernel that moved the break down into the gap is refused: below
`min_brk` the function has already left (mm/mmap.c:140-141, Linux v6.18.46).
Valid for this fixture's randomised base; on a `CONFIG_COMPAT_BRK` kernel
with randomisation off the floor is `end_data` (:131-139) and the same
answer comes from the shrink block's `!brkvma` (:163-166), since nothing
is mapped in `[16384, 65536)` (bugs/brk-min-brk-assumes-a-randomised-break.md).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_in_aslr_gap_rejects_moving :
    check_brk 16384 (mkEffect 16384 [] []) m_est = CheckReject := by
  brk_munmap_norm

/-! ### brk: grow -/

/-- A grow may fail with the break unchanged: every refusal on the grow path
is a `goto out` (mm/mmap.c:149-151, :180-181, :187-190, :194-195, Linux
v6.18.46) and
`out:` returns `origbrk` (:209-212).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_may_fail :
    check_brk 131072 (mkEffect 65536 [] []) m_est = CheckOk m_est [] := by
  brk_munmap_norm

/-- A grow whose new page would sit flush against a neighbour is refused when
the kernel claims to have granted it: `newbrk + PAGE_SIZE > vm_start_gap(next)`
takes `goto out` (mm/mmap.c:187-190, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_flush_against_neighbour_rejected :
    check_brk 69632 (mkEffect 69632 [] [(65536, 4096)]) m_neighbour_flush = CheckReject := by
  brk_munmap_norm

/-- …and the unchanged break is the answer there (mm/mmap.c:187-190,
:209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_flush_against_neighbour_returns_break :
    check_brk 69632 (mkEffect 65536 [] []) m_neighbour_flush
      = CheckOk m_neighbour_flush [] := by
  brk_munmap_norm

/-- One page below the neighbour the same grow is granted: for a neighbour
with neither `VM_GROWSDOWN` nor `VM_SHADOW_STACK`, `vm_start_gap(next)` is
its `vm_start` (include/linux/mm.h:3704-3725, Linux v6.18.46), so the test
at mm/mmap.c:189 refuses only a neighbour starting under `newbrk +
PAGE_SIZE`; against the stack's
`VM_GROWSDOWN` VMA the reach is `stack_guard_gap` more (mm/mmap.c:941,
bugs/brk-grow-ignores-stack-guard-gap.md), which this anonymous neighbour
is not.  The ledger gains the heap page and the effect zeroes it.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_one_page_below_neighbour_grants :
    check_brk 69632 (mkEffect 69632 [] [(65536, 4096)]) m_neighbour_gap
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 4096), (73728, 4096)]
                   65536 69632 demo_limit) m_neighbour_gap) [] := by
  brk_munmap_norm

/-- A one-page grow under a one-page budget fits and is granted
(`do_brk_flags`, mm/vma.c:2805, reached from mm/mmap.c:194-195, Linux v6.18.46).
probe: testing/syscall-check/tests/brk_budget.c#conform --alloc-limit 0x10000 -- exact -/
theorem brk_grow_within_budget_grants :
    check_brk 69632 (mkEffect 69632 [] [(65536, 4096)]) m_tight_brk
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 4096)] 65536 69632 4096)
                   m_tight_brk) [] := by
  brk_munmap_norm

/-- A two-page grant under a one-page budget is refused: the run declared the
budget, and a kernel exceeding it is not the kernel this run models.
model: `brk_budget_ok` under the fixture's declared `vm_limit`; the
refusal is the run's budget, not a line of Linux -/
theorem brk_grow_beyond_budget_rejects_moving :
    check_brk 73728 (mkEffect 73728 [] [(65536, 8192)]) m_tight_brk = CheckReject := by
  brk_munmap_norm

/-- …and the unchanged break is the answer the budget leaves: what Linux
gives to a grow it cannot back (mm/mmap.c:194-195, :209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_beyond_budget_returns_break :
    check_brk 73728 (mkEffect 65536 [] []) m_tight_brk = CheckOk m_tight_brk [] := by
  brk_munmap_norm

/-! ### brk: shrink and the page boundary -/

/-- A shrink drops the freed heap tail from the ledger and declares it
unmapped (`do_vmi_align_munmap(&vmi, brkvma, mm, newbrk, oldbrk, …)`,
mm/mmap.c:173-175, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_unmaps_freed_tail :
    check_brk 65536 (SyscallEffect.mkEffectU 65536 [] [] [(65536, 65536)] [] []) m_grown
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [] 65536 65536 demo_limit) m_grown) [] := by
  brk_munmap_norm

/-- …and a shrink declaring no unmap is refused: the pages really go
(mm/mmap.c:173-175, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_must_declare_unmaps :
    check_brk 65536 (mkEffect 65536 [] []) m_grown = CheckReject := by
  brk_munmap_norm

/-- A sub-page shrink frees nothing: `PAGE_ALIGN` makes `oldbrk == newbrk`
and the early exit moves `mm->brk` only (mm/mmap.c:153-158, Linux v6.18.46),
so the ledger entry shrinks and no unmap is declared.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_subpage_shrink_frees_nothing :
    check_brk 129024 (mkEffect 129024 [] []) m_grown
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 63488)] 65536 129024 demo_limit)
                   m_grown) [] := by
  brk_munmap_norm

/-- A four-byte shrink inside the guarded page truncates the grant and keeps
the guard: no page is freed (mm/mmap.c:153-158, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_shrink_preserves_noaccess :
    check_brk 69620 (mkEffect 69620 [] []) m_brk_same_page
      = CheckOk m_brk_same_page_shrunk [] := by
  brk_munmap_norm

/-- The four-byte regrow records a second logical piece and installs no page:
`oldbrk == newbrk` again (mm/mmap.c:153-158, Linux v6.18.46), the guard survives.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_regrow_preserves_noaccess :
    check_brk 69624 (mkEffect 69624 [] []) m_brk_same_page_shrunk
      = CheckOk (with_vmmaps (VmMaps.mkVmMapsFull brk_reserved [(69620, 4), (65536, 4084)]
                   [(65536, 4096)] 65536 69624 demo_limit 0 demo_sp) m_brk_same_page_shrunk) []
      := by
  brk_munmap_norm

/-- Crossing the page boundary is exact: an unaligned break grown sixteen
bytes maps and zeroes precisely the next page (`do_brk_flags(…, oldbrk,
newbrk - oldbrk, …)`, mm/mmap.c:153-154, :194-195, Linux v6.18.46), the
ledger records the sixteen bytes and the guard stays.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_unaligned_cross_page_zeros_exact_new_page :
    check_brk 69640 (mkEffect 69640 [] [(69632, 4096)]) m_brk_same_page
      = CheckOk (with_vmmaps (VmMaps.mkVmMapsFull brk_reserved [(69624, 16), (65536, 4088)]
                   [(65536, 4096)] 65536 69640 demo_limit 0 demo_sp) m_brk_same_page) [] := by
  brk_munmap_norm

/-- Shrinking the heap away frees the page (mm/mmap.c:173-175, Linux v6.18.46)
and with it both sparse ledgers: the post-model is `with_brk_next`'s.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_forgets_fixed_noreserve_touch :
    check_brk 65536 (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
        brk_sparse_touched
      = CheckOk (with_brk_next brk_sparse_touched 65536 65536) [] := by
  brk_munmap_norm

/-! ### brk: the run's top -/

/-- A grant across this run's `alloc_top` is refused under the low stack
pointer.  The refusal is the model's: `alloc_top` stands in for the
stack-guard test (mm/mmap.c:187-190, include/linux/mm.h:3704-3725, Linux
v6.18.46) against a stack VMA the ledger does not carry, and Linux gives
this grant while the stack VMA's `vm_start` lies at least `stack_guard_gap
+ PAGE_SIZE` above `newbrk` — a real trace the checker rejects, which
bugs/grants-into-the-stack-band.md records; bugs/brk-grow-ignores-stack-guard-gap.md
is the other direction, a grow the model admits and a grown stack refuses.
model: State.alloc_top, the band vm_init_sp - stack_max_size the ledger imposes (bugs/grants-into-the-stack-band.md) -/
theorem brk_grow_across_demo_top_rejected_under_low_sp :
    check_brk (Z_to_bv 64 (demo_top + 4096))
        (mkEffect (Z_to_bv 64 (demo_top + 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 8192)])
        brk_top_lo_model
      = CheckReject := by
  brk_munmap_norm

/-- Under the high stack pointer the same grow is granted (`do_brk_flags`, mm/vma.c:2805,
reached from mm/mmap.c:194-195, Linux v6.18.46): the top is the run's, not the
model's.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_across_demo_top_admitted_under_high_sp :
    check_brk (Z_to_bv 64 (demo_top + 4096))
        (mkEffect (Z_to_bv 64 (demo_top + 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 8192)])
        brk_top_hi_model
      = CheckOk (with_vmmaps (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] []
                   (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 (demo_top + 4096))
                   demo_limit (Z_to_bv 64 mmap_base_max) hi_sp) brk_top_hi_model) [] := by
  brk_munmap_norm

/-! ### The witnesses

The receptiveness witness names ONE admitted outcome per input.  brk's is
the unchanged break, the answer `out:` gives on every refusal path
(mm/mmap.c:209-212, Linux v6.18.46) and so admitted at every request;
munmap's follows the checker's own branches. -/

/-- The brk witness on a grow answers the unchanged break with no zeroes and
no unmap (mm/mmap.c:209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_witness_answers_the_break :
    brk_witness 131072 m_est = Ok (mkEffect 65536 [] []) m_est [] := by
  brk_munmap_norm

/-- The munmap witness on an exact mapping tears it down (mm/vma.c:1626,
Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_witness_unmaps_the_exact_mapping :
    munmap_witness 65536 4096 one_map_model
      = Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [])
           (with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) one_map_model) [] := by
  brk_munmap_norm

/-- …and declines in the stack band, where the checker declines too
(mm/vma.c:1619-1626, Linux v6.18.46: 0 either way, the model cannot say
which page it was).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_witness_declines_in_the_stack_band :
    munmap_witness (Z_to_bv 64 demo_top) 4096 one_map_model = Unmodeled := by
  brk_munmap_norm

/-! ### Beyond the Rocq twins

Pins with no Rocq checker example behind them, each named after the
spec-level pin of `Checks/Cases/Mm/Mmap.lean` whose answer it carries down
to the checker, or after nothing when there is none.  The first five are
about the SHAPE of the effect: a brk or munmap effect carrying a write, a
zero-fill in the wrong arm, or a return beside the right unmap, is refused
before any gate is compared, and no other pin at either level hands the
checker such an effect — so a `[]` in a checker's pattern turned into a
wildcard would have gone unnoticed. -/

/-- `brk` writes no user memory: the right answer beside a write is refused
(`SYSCALL_DEFINE1(brk)` copies nothing out, mm/mmap.c:115-213, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_effect_with_a_write_rejected :
    check_brk 0 (mkEffect 65536 [(65536, [0])] []) m_est = CheckReject := by
  brk_munmap_norm

/-- Nor does `munmap`: the exact unmap beside a write is refused
(`do_vmi_align_munmap` detaches and frees, mm/vma.c:1557, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem munmap_effect_with_a_write_rejected :
    check_munmap 65536 4096
        (SyscallEffect.mkEffectU 0 [(65536, [0])] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- …and the -EINVAL arm beside a write too: `do_vmi_munmap` returns before
anything is touched (mm/vma.c:1611-1612, Linux v6.18.46), and
`check_ret_only` admits a bare return and nothing else.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_einval_effect_with_a_write_rejected :
    check_munmap 65537 4096 (mkEffect (errno_ret EINVAL) [(0, [0])] []) one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- An unmap declares no zero-fill: the pages are gone, not zeroed
(`do_vmi_align_munmap`, mm/vma.c:1557, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem munmap_exact_unmap_with_zeros_rejected :
    check_munmap 65536 4096
        (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [] []) one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- A successful unmap returns 0 (`do_vmi_align_munmap`, mm/vma.c:1579, Linux
v6.18.46): a nonzero return beside the correct unmap is refused.
kernel: mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem munmap_exact_unmap_with_nonzero_return_rejected :
    check_munmap 65536 4096 (SyscallEffect.mkEffectU 1 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- A grant declaring no zero-fill is refused: `do_brk_flags` installs the
whole of `[oldbrk, newbrk)` fresh (mm/vma.c:2805, reached from
mm/mmap.c:194-195, Linux v6.18.46), and fresh anonymous memory reads as zero.
kernel: mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_grow_without_zeros_rejected :
    check_brk 131072 (mkEffect 131072 [] []) m_est = CheckReject := by
  brk_munmap_norm

/-- The length is page-rounded before the ledger is read: 4095 bytes over a
one-page mapping is that mapping's exact unmap (`end = start + PAGE_ALIGN(len)`,
mm/vma.c:1614, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_len_rounds_up_to_the_page :
    check_munmap 65536 4095 (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckOk (with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) one_map_model) [] := by
  brk_munmap_norm

/-- …so an effect unmapping the unrounded 4095 bytes is refused (mm/vma.c:1614,
Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unrounded_unmap_rejected :
    check_munmap 65536 4095 (SyscallEffect.mkEffectU 0 [] [] [(65536, 4095)] [] []) one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- The page under `TASK_SIZE` passes Linux's strict `start > TASK_SIZE`
(mm/vma.c:1611-1612, Linux v6.18.46) and lies in the stack band the ledger
does not carry, so the checker declines; the harness reads the same call as
the `fail-closed -- at` case of `testing/syscall-check/tests/munmap_va_limit.c`.
An inclusive bound would answer -EINVAL here; `munmap_near_max_is_einval`
above is where the bound does fire.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_last_page_under_task_size_is_unmodeled :
    check_munmap (Z_to_bv 64 (TASK_SIZE - 4096)) 4096 (mkEffect 0 [] []) one_map_model
      = CheckUnmodeled := by
  brk_munmap_norm

/-- `munmap_forgets_lazy_and_materialized_metadata` states its post-model
through `with_mmap_destroyed` itself, so it cannot see a wrong setter.  This
spells the fields out — the lazy and materialized ledgers are empty, the map
is gone, the limit stays — and asserts the same answer Linux gives: the VMA
torn down and 0 returned (`do_vmi_align_munmap`, mm/vma.c:1557, reached
from :1626, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_forgets_lazy_and_materialized_metadata_spelled_out :
    check_munmap 65536 8192 (SyscallEffect.mkEffectU 0 [] [] [(65536, 8192)] [] [])
        mmap_lazy_materialized
      = CheckOk (with_vm_backing [] []
                   (with_vmmaps (mkVmMaps [] [] 0 0 8192) mmap_lazy_materialized)) [] := by
  brk_munmap_norm

/-! ### Both sides of the decisions the twins reach from one side

Read against the checkers' `if`-chains decision by decision.  Each pin
below pairs the answer Linux gives with the lie the same arm refuses, or
states a boundary of an arm the twins above reach from one side only, so
that a decision's gate, bound or accepted shape cannot move with nothing
red here: the eight lemmas notice a checker moved alone, not a checker
and a spec moved together.  The set is what a pins-only pass left
standing — the checkers mutated with the eight lemmas deleted and only
the twins above in place — each survivor a decision the twins reach from
one side, given its other side here. -/

/-- The free-range no-op is 0 and only 0: `vma_find` finds nothing and
`do_vmi_munmap` returns 0 (mm/vma.c:1619-1623, Linux v6.18.46), so an errno
beside a free page under `alloc_top` is refused; the harness reads the same
lie as the `reject --mutate munmap#2:ret=-EINVAL -- highrepeat` case of
`testing/syscall-check/tests/munmap_va_limit.c`.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_free_range_einval_rejected :
    check_munmap 131072 4096 (mkEffect (errno_ret EINVAL) [] []) one_map_model = CheckReject := by
  brk_munmap_norm

/-- …and it declares nothing: there was no VMA to detach (mm/vma.c:1619-1623,
Linux v6.18.46), so a 0 beside an unmap of the free page is refused.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_free_range_unmap_rejected :
    check_munmap 131072 4096 (SyscallEffect.mkEffectU 0 [] [] [(131072, 4096)] [] []) one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- `brk` copies nothing between user ranges and reads none (`SYSCALL_DEFINE1(brk)`,
mm/mmap.c:115-213, Linux v6.18.46): the right answer beside a memory copy is
refused, as it is beside a write.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_effect_with_a_copy_rejected :
    check_brk 0 (SyscallEffect.mkEffectU 65536 [] [] [] [⟨65536, 69632, 8⟩] []) m_est = CheckReject := by
  brk_munmap_norm

/-- …and beside a copyin.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_effect_with_a_copyin_rejected :
    check_brk 0 (SyscallEffect.mkEffectU 65536 [] [] [] [] [(65536, 8)]) m_est = CheckReject := by
  brk_munmap_norm

/-- Nor does `munmap` copy or read user memory (`do_vmi_align_munmap` detaches
and frees, mm/vma.c:1557, Linux v6.18.46): the exact unmap beside a memory copy
is refused.
kernel: mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem munmap_exact_unmap_with_a_copy_rejected :
    check_munmap 65536 4096 (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [⟨65536, 69632, 8⟩] [])
        one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- …and beside a copyin.
kernel: mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem munmap_exact_unmap_with_a_copyin_rejected :
    check_munmap 65536 4096 (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [(65536, 8)])
        one_map_model
      = CheckReject := by
  brk_munmap_norm

/-- A shrink may fail with the break unchanged: the shrink block's refusals —
no VMA in `[newbrk, oldbrk)` (`!brkvma`, mm/mmap.c:163-166, Linux v6.18.46:
the lookup runs from `newbrk` up to `oldbrk`, so it is real once the program
has unmapped its own heap pages; not here, where the ledger holds the heap
grant `[65536, 131072)`, the VMA `vma_find(&vmi, oldbrk)` returns, so of
the two only the next is live on this fixture), a failing
`do_vmi_align_munmap` (:173-175; its two error exits, mm/vma.c:1570-1571
and :1574-1575, hand back what `vms_gather_munmap_vmas` or
`vma_iter_clear_gfp` failed with: -ENOMEM from `sysctl_max_map_count` (:1390-1391) or
an allocation — `__split_vma` at :1401-1403 and :1422-1424, `mas_store_gfp`
at :1428-1430, `vma_iter_clear_gfp` at include/linux/mm.h:1055-1056 — or
the -EPERM of a sealed VMA, :1396-1398 and :1416-1418, which no modeled run
holds: `mseal` (462) has no arm and the heap is no kernel-installed
mapping) — are `goto out`, and `out:` answers `origbrk` (:209-212) with
nothing unmapped.  Which errno the teardown produced is invisible: `brk`
discards it at :173 and never returns one.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap,vms_gather_munmap_vmas@v6.18.46 -/
theorem brk_shrink_may_fail :
    check_brk 65536 (mkEffect 131072 [] []) m_grown = CheckOk m_grown [] := by
  brk_munmap_norm

/-- …and answers the request or the old break, nothing between: `success:`
returns `brk` (mm/mmap.c:207, Linux v6.18.46) and `out:` returns `origbrk`
(:212).  A third value is refused even beside the unmap list that value would
imply, so the refusal is `brk_r_ok`'s and not the list comparison's.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_to_a_third_value_rejected :
    check_brk 65536 (SyscallEffect.mkEffectU 100000 [] [] [(102400, 28672)] [] []) m_grown
      = CheckReject := by
  brk_munmap_norm

/-- The same on a grow: a break neither requested nor old is refused beside
the zero-fill that break would imply (`do_brk_flags` installs `[oldbrk,
newbrk)` for the request, mm/mmap.c:194-195, Linux v6.18.46, and `out:` answers
`origbrk`); the harness reads such a lie as the `reject --mutate brk#2:ret=0
-- heap` case of `testing/syscall-check/tests/mined100_surface.c`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_to_a_third_value_rejected :
    check_brk 131072 (mkEffect 100000 [] [(65536, 36864)]) m_est = CheckReject := by
  brk_munmap_norm

/-- The request equal to the break — here `min_brk` itself — takes the
`oldbrk == newbrk` exit and answers it (mm/mmap.c:153-158, Linux v6.18.46):
no zero-fill, no unmap, the ledger unchanged.  The spec-level pin of the
same name is the claim on `brk_spec`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_at_min_brk_returns_it :
    check_brk 65536 (mkEffect 65536 [] []) m_est = CheckOk m_est [] := by
  brk_munmap_norm

/-- A range on the image's reservation is neither a ledger mapping nor free:
Linux unmaps the LOAD page like any other and answers 0 (mm/vma.c:1619-1626,
Linux v6.18.46), but the model does not describe an image page's removal,
so `munmap_free_ok`'s `vm_reserved` conjunct declines rather than answer a
no-op 0 that would leave the page readable.  Every other munmap fixture in
this section has an empty reservation; this is the pin that reaches that
conjunct.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_image_range_is_unmodeled :
    check_munmap 4096 4096 (mkEffect 0 [] []) m_est = CheckUnmodeled := by
  brk_munmap_norm

/-- Page 0 is an address like any other to `do_vmi_munmap`: `offset_in_page(0)`
is 0 and `0 > TASK_SIZE` is false (mm/vma.c:1611-1612, Linux v6.18.46), so a
free page there is the no-op 0 (:1619-1623); `mmap_min_addr` is consulted on
placement, not on the munmap path.  The checker has no `0 < addr` gate; the
MAP_FIXED arms of `check_mmap` above decline address 0, and a copy of that
gate here would answer wrongly — this pin is what would notice.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_page_zero_free_is_noop :
    check_munmap 0 4096 (mkEffect 0 [] []) one_map_model = CheckOk one_map_model [] := by
  brk_munmap_norm

/-- …and an errno there is refused.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_page_zero_einval_rejected :
    check_munmap 0 4096 (mkEffect (errno_ret EINVAL) [] []) one_map_model = CheckReject := by
  brk_munmap_norm

/-- A length whose page round-up leaves the word: `len > TASK_SIZE - start`
refuses it (mm/vma.c:1611-1612, Linux v6.18.46) before `PAGE_ALIGN(len)`, which
would wrap to 0, is formed; the model's `Int` round-up, `2^64`, sees the same
bound.  A word round-up would have answered the no-op 0 here, so the 0 is
refused.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_len_rounding_out_of_the_word_is_einval :
    check_munmap 0 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_munmap 0 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect 0 [] []) one_map_model = CheckReject := by
  constructor <;> brk_munmap_norm

/-- Linux's second disjunct alone: `start = TASK_SIZE` passes `start > TASK_SIZE`
and fails `len > TASK_SIZE - start` (mm/vma.c:1611-1612, Linux v6.18.46), so the
model's one sum refuses it with `start` itself inside the bound —
`munmap_near_max_is_einval` fires on the first disjunct.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_at_task_size_is_einval :
    check_munmap (Z_to_bv 64 TASK_SIZE) 4096 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_munmap (Z_to_bv 64 TASK_SIZE) 4096 (mkEffect 0 [] []) one_map_model = CheckReject := by
  constructor <;> brk_munmap_norm

/-- …and from the page below, a length one byte past the room:
`len > TASK_SIZE - start` reads the raw 4097 against the 4096 left
(mm/vma.c:1611-1612, Linux v6.18.46), before `end = start + PAGE_ALIGN(len)`
is formed (:1614); the model's `Int` gate refuses the same through the
round-up to two pages — on an aligned `start` the two coincide, the
argument on `munmap_spec`'s header — where 4096 passed
(`munmap_last_page_under_task_size_is_unmodeled`).  A 0 there is refused
beside it, as at the other gate pins.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_rounding_past_task_size_is_einval :
    check_munmap (Z_to_bv 64 (TASK_SIZE - 4096)) 4097 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_munmap (Z_to_bv 64 (TASK_SIZE - 4096)) 4097 (mkEffect 0 [] []) one_map_model
        = CheckReject := by
  constructor <;> brk_munmap_norm

/-- A range starting on the mapping and running past it into free space is
neither the exact mapping nor free: Linux detaches the page and answers 0
(mm/vma.c:1619-1626, Linux v6.18.46); the model declines, as it does for the
range inside the mapping (`munmap_partial_is_error`).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_spanning_past_the_mapping_is_unmodeled :
    check_munmap 65536 8192 (mkEffect 0 [] []) one_map_model = CheckUnmodeled := by
  brk_munmap_norm

/-- The grow ending exactly at `alloc_top` is granted: the bound is inclusive
on the grant's END, and the boundary grant is inside Linux's window on every
run the premise of bugs/brk-grow-ignores-stack-guard-gap.md covers: the test
at mm/mmap.c:187-190 (Linux v6.18.46) refuses only when the stack VMA's
`vm_start` less the 1 MiB `stack_guard_gap` (:941) is under `newbrk +
PAGE_SIZE`, and while the stack is far from its 8 MiB limit that point is
some 7 MiB above `alloc_top`.  `brk_grow_across_demo_top_rejected_under_low_sp`
is the page past it.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_ending_at_alloc_top_grants_under_low_sp :
    check_brk (Z_to_bv 64 demo_top)
        (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
        brk_top_lo_model
      = CheckOk (with_vmmaps (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] []
                   (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 demo_top)
                   demo_limit (Z_to_bv 64 mmap_base_max) demo_sp) brk_top_lo_model) [] := by
  brk_munmap_norm

/-- A request one below 2^64: Linux's `PAGE_ALIGN(brk)` wraps to 0
(mm/mmap.c:153, Linux v6.18.46; `__ALIGN_KERNEL` is `unsigned long`
arithmetic) and the break is unchanged — under `RLIM_INFINITY`
`check_data_rlimit` (:149-151) compares nothing, its guard
`rlim < RLIM_INFINITY` (include/linux/mm.h:3576) being false, and
`check_brk_limits` (:180-181,
:103-113) refuses the wrapped length through `__get_unmapped_area`'s
`len > TASK_SIZE` (mm/mmap.c:824-825); under a finite `RLIMIT_DATA` :149-151
may refuse first.  `out:` answers `origbrk` either way (:209-212).  The
model's `Int` round-up, `2^64`, fails `brk_grow_ok` on `hi ≤ alloc_top` and
on the budget both, and the offered zero-fill is the range a word round-up
would have zeroed had the gates passed: refused, and the old break is the
only answer admitted.
kernel: mm/mmap.c:brk,check_brk_limits,__get_unmapped_area@v6.18.46 -/
theorem brk_request_near_two_pow_64_returns_break :
    check_brk (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect 65536 [] []) m_est = CheckOk m_est []
    ∧ check_brk (Z_to_bv 64 (2 ^ 64 - 1))
        (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] [(65536, Z_to_bv 64 (2 ^ 64 - 65536))]) m_est
      = CheckReject := by
  constructor <;> brk_munmap_norm

/-- The munmap witness on an unaligned start answers -EINVAL and nothing else
(mm/vma.c:1611-1612, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_witness_answers_einval_on_an_unaligned_address :
    munmap_witness 65537 4096 one_map_model = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  brk_munmap_norm

/-- …and the range past `TASK_SIZE` the checker refuses (mm/vma.c:1611-1612,
Linux v6.18.46), from the address `TASK_SIZE` itself.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_witness_answers_einval_at_task_size :
    munmap_witness (Z_to_bv 64 TASK_SIZE) 4096 one_map_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  brk_munmap_norm

/-- …while the last page under it is inside Linux's bound (mm/vma.c:1611-1612,
Linux v6.18.46) and, above `alloc_top`, neither a mapping nor free to the
ledger: the witness declines, as `munmap_last_page_under_task_size_is_unmodeled`
says the checker does.  A `≤` in the witness's gate would answer -EINVAL here.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_witness_declines_on_the_last_page_under_task_size :
    munmap_witness (Z_to_bv 64 (TASK_SIZE - 4096)) 4096 one_map_model = Unmodeled := by
  brk_munmap_norm

/-- …and on a free range the no-op 0 (mm/vma.c:1619-1623, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_witness_answers_the_free_range_noop :
    munmap_witness 131072 4096 one_map_model = Ok (mkEffect 0 [] []) one_map_model [] := by
  brk_munmap_norm

/-- The brk witness on a shrink answers the unchanged break too — the shrink
that failed (mm/mmap.c:164-166, :173-175, :209-212, Linux v6.18.46) — with no
unmap.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_witness_answers_the_break_on_a_shrink :
    brk_witness 65536 m_grown = Ok (mkEffect 131072 [] []) m_grown [] := by
  brk_munmap_norm

/-! ### The lie at each gate, the lists entry by entry, and the neighbour that stays

A second pins-only pass — the checkers mutated with the lemmas deleted —
still reached these from one side: a 0 at either -EINVAL
gate of `check_munmap`, an errno on the exact mapping, a zero-fill or unmap
list that is present but wrong, an unmap list with the wrong base or a
second entry, an exact unmap on a ledger with a neighbour (every other
exact-arm pin empties a one-entry ledger, where dropping the ledger reads
the same), the witness's query answer, and the byte and page boundaries of
`brk` the spec-level file pins and this one did not. -/

/-- A 0 on an unaligned address is refused, alone or beside the unmap a
kernel that rounded the address down would declare: `offset_in_page(start)`
is -EINVAL before any lookup (mm/vma.c:1611-1612, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unaligned_success_rejected :
    check_munmap 65537 4096 (mkEffect 0 [] []) one_map_model = CheckReject
    ∧ check_munmap 65537 4096 (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [])
        one_map_model = CheckReject := by
  constructor <;> brk_munmap_norm

/-- A 0 on a zero length is refused: `end == start` is -EINVAL
(mm/vma.c:1614-1616, Linux v6.18.46), limit or no limit; the harness reads
the same lie as the `reject --mutate munmap#2:ret=0 -- zero` case of
`testing/syscall-check/tests/munmap_va_limit.c`.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_len_zero_success_rejected :
    check_munmap 65536 0 (mkEffect 0 [] []) one_map_model = CheckReject := by
  brk_munmap_norm

/-- -EINVAL on the exact mapping is refused: every -EINVAL of
`do_vmi_munmap` is an argument test this call passes (mm/vma.c:1611-1616,
Linux v6.18.46), and the teardown answers 0 (:1626, `do_vmi_align_munmap`
:1579).  The teardown's other returns — through its error exits at
:1570-1571 and :1574-1575: -ENOMEM from `sysctl_max_map_count` (:1390-1391) or an
allocation (`__split_vma` :1401-1403, :1422-1424; `mas_store_gfp`
:1428-1430; `vma_iter_clear_gfp`, include/linux/mm.h:1055-1056), and the
-EPERM of a sealed VMA (:1396-1398, :1416-1418) — the checker's `w_is0 r`
refuses too, and that refusal is the spec's, not a line of Linux:
`munmap_spec` answers 0 on the exact arm and nothing else.  The -EPERM half
rests on the argument the spanning `mmap` arm makes (`vma_is_sealed`'s
sentence on `mmap_spec`, `Sys/Mm/Mmap.lean`; in full on the Rocq arm):
`mseal` (462) has no arm, and the kernel-installed mappings
CONFIG_MSEAL_SYSTEM_MAPPINGS seals are never entries of `vm_maps`, which
this arm requires.  The -ENOMEM half is a narrowing the tree records
nowhere for `munmap` — not on `munmap_spec`, not in `bugs/` — a real return
rejected rather than declined, the shape
bugs/writev-heap-iovec-enomem-not-admitted.md records for `writev`; this
sentence is stale the day a `munmap` entry lands.
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap,vms_gather_munmap_vmas@v6.18.46 -/
theorem munmap_exact_grant_einval_rejected :
    check_munmap 65536 4096 (mkEffect (errno_ret EINVAL) [] []) one_map_model = CheckReject := by
  brk_munmap_norm

/-- The unmap list is compared entry by entry, not by count: the right
length at the wrong base, or the right entry beside a second, is refused.
`vms_gather_munmap_vmas` (mm/vma.c:1413, Linux v6.18.46) collects the VMAs
of `[start, end)` and no other, and it is what the teardown runs
(`do_vmi_align_munmap`, :1569), so nothing else goes.
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap,vms_gather_munmap_vmas@v6.18.46 -/
theorem munmap_shifted_or_doubled_unmap_rejected :
    check_munmap 65536 4096 (SyscallEffect.mkEffectU 0 [] [] [(69632, 4096)] [] []) one_map_model
        = CheckReject
    ∧ check_munmap 65536 4096
        (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096), (131072, 4096)] [] []) one_map_model
        = CheckReject := by
  constructor <;> brk_munmap_norm

/-- An exact unmap removes the entry it names and no other.  Whether the
neighbour at 69632 is its own VMA or merged with the unmapped page into
one, only `[start, end)` goes: an unmerged neighbour is outside what
`vms_gather_munmap_vmas` collects, a merged one is split off at `end` and
kept (mm/vma.c:1421-1422, Linux v6.18.46).  The other exact-arm pins empty
a one-entry ledger, where a post-model that dropped the whole ledger reads
the same.
kernel: mm/vma.c:do_vmi_munmap,vms_gather_munmap_vmas@v6.18.46 -/
theorem munmap_exact_keeps_the_neighbour :
    check_munmap 65536 4096 (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [])
        adjacent_maps_model
      = CheckOk (with_vmmaps (mkVmMaps [] [(69632, 4096)] 0 0 demo_limit) adjacent_maps_model) [] := by
  brk_munmap_norm

/-- Unmapping the heap record leaves the break: `do_vmi_munmap` never
writes `mm->brk` (mm/vma.c:1604-1627, Linux v6.18.46), so the image
reservation and both break fields ride into the post-model while the
record goes — the spec-level `munmap_heap_record_leaves_the_break` on the
checker, with the carried fields spelled out.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_heap_record_leaves_the_break :
    check_munmap 65536 65536 (SyscallEffect.mkEffectU 0 [] [] [(65536, 65536)] [] []) m_grown
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [] 65536 131072 demo_limit) m_grown) [] := by
  brk_munmap_norm

/-- The zero-fill is compared entry by entry: a grant zeroing only part of
the installed range is refused, since `do_brk_flags` is handed the whole of
`[oldbrk, newbrk)` (mm/mmap.c:194-195, Linux v6.18.46) — the spec-level
`brk_grow_partial_zeros_rejected` on the checker.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_partial_zeros_rejected :
    check_brk 131072 (mkEffect 131072 [] [(65536, 4096)]) m_est = CheckReject := by
  brk_munmap_norm

/-- …and the unmap list likewise: a shrink declaring more than it freed, or
the wrong range, is refused; Linux frees exactly `[newbrk, oldbrk)`
(mm/mmap.c:173-175, Linux v6.18.46) — the spec-level
`brk_shrink_over_declared_unmap_rejected` and `brk_shrink_shifted_unmap_rejected`
on the checker.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_wrong_unmap_list_rejected :
    check_brk 65536 (SyscallEffect.mkEffectU 65536 [] [] [(65536, 69632)] [] []) m_grown = CheckReject
    ∧ check_brk 65536 (SyscallEffect.mkEffectU 65536 [] [] [(69632, 65536)] [] []) m_grown
        = CheckReject := by
  constructor <;> brk_munmap_norm

/-- The witness on a query answers what Linux answers: `brk(0)` is under
`min_brk`, `goto out`, and `out:` returns `origbrk` (mm/mmap.c:140-141,
:209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_witness_answers_the_break_on_a_query :
    brk_witness 0 m_est = Ok (mkEffect 65536 [] []) m_est [] := by
  brk_munmap_norm

/-- One byte under the base is still under it: `brk < min_brk` is strict at
the byte (mm/mmap.c:140, Linux v6.18.46), so 65535 on a base of 65536
answers the break and never a shrink — the spec-level
`brk_one_below_min_brk_returns_break` on the checker, beside the shrink the
arm refuses (its lists are what a shrink to 65535 would carry, both empty,
so `brk_r_ok` alone refuses).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_one_below_min_brk_returns_break :
    check_brk 65535 (mkEffect 65536 [] []) m_est = CheckOk m_est []
    ∧ check_brk 65535 (mkEffect 65535 [] []) m_est = CheckReject := by
  constructor <;> brk_munmap_norm

/-- A grow of ONE BYTE past an aligned break installs a whole page:
`PAGE_ALIGN(65537)` is 69632 (mm/mmap.c:153-154, Linux v6.18.46), the exit
does not fire and `do_brk_flags` maps `[65536, 69632)` (:194-195) while
`mm->brk` becomes 65537 (:197) — the spec-level
`brk_one_byte_grow_installs_a_page` on the checker: the ledger owns the
byte, the zero-fill covers the page.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_one_byte_grow_installs_a_page :
    check_brk 65537 (mkEffect 65537 [] [(65536, 4096)]) m_est
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 1)] 65536 65537 demo_limit) m_est) [] := by
  brk_munmap_norm

/-- One page down, exactly: `[PAGE_ALIGN(126976), PAGE_ALIGN(131072))` is
the one page `[126976, 131072)`, and that is what goes (mm/mmap.c:173-175,
Linux v6.18.46) — the spec-level `brk_shrink_one_page_frees_that_page` on
the checker.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem brk_shrink_one_page_frees_that_page :
    check_brk 126976 (SyscallEffect.mkEffectU 126976 [] [] [(126976, 4096)] [] []) m_grown
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 61440)] 65536 126976 demo_limit) m_grown)
          [] := by
  brk_munmap_norm

/-- The budget is charged by the byte: 4097 bytes over a 4096-byte budget
is refused and the unchanged break is the one answer — the spec-level
`brk_grow_one_byte_over_budget_*` pair on the checker.  The refusal is the
run's declared budget, not a line of Linux, which grants this grow; the
harness reads it as `brk_budget.c`'s `reject --alloc-limit 0x10000 --
overbyte` case.
model: `brk_budget_ok` under the fixture's declared `vm_limit`, charged
`r - vm_brk` by the byte -/
theorem brk_grow_one_byte_over_budget :
    check_brk 69633 (mkEffect 65536 [] []) m_tight_brk = CheckOk m_tight_brk []
    ∧ check_brk 69633 (mkEffect 69633 [] [(65536, 8192)]) m_tight_brk = CheckReject := by
  constructor <;> brk_munmap_norm

/-! ### The image above the break, the list beside the unchanged answer, and the witness on a zero length

Three decisions no pin above reaches.  `brk_grow_ok` tests the page a grow
installs, and the one above it, against `vm_reserved ++ vm_maps`; the brk
fixtures above keep their reservation below `vm_start_brk`, so a spec that
dropped the image half of that test would have answered each of them the
same way — the two fixtures here put a LOAD page flush against the grow's
page, inside the `newbrk + PAGE_SIZE` reach of mm/mmap.c:189 (Linux
v6.18.46), and one page higher, out of it.  A zero-fill or unmap offered beside an answer that
installs or frees nothing — the request equal to the break, the sub-page
and same-page shrinks and the same-page regrow, the old break on a shrink
or grow that failed — passes `brk_r_ok` and is refused by the list
comparison, `listNN_eqb` against `brk_zeros` and `brk_unmaps`, which the
lemmas and the spec-level `iff` pins said and no pin on the checker did.
And the witness's `len = 0` disjunct
had no pin of its own; `tools/lean_mutate.py`'s `guard-drop` deletes a
conjunct of `&&`, never a disjunct of `||`, so no operator of that tool
reaches it either — the pin is the only thing that does. -/

/-- A LOAD page at 69632, flush against the page a one-page grow of the
break at 65536 installs — `m_neighbour_flush`'s shape with the neighbour in
the image ledger; nothing granted. -/
def m_image_flush : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096), (69632, 4096)] [] [] 65536 65536 demo_limit 0 demo_sp)

/-- The same LOAD page one page higher, at 73728. -/
def m_image_gap : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096), (73728, 4096)] [] [] 65536 65536 demo_limit 0 demo_sp)

/-- The neighbour a grow meets may be the image itself: `vma_find` from
`oldbrk` (mm/mmap.c:187-188, Linux v6.18.46; `mas_find(&vmi->mas, max - 1)`,
include/linux/mm.h:1024-1027) returns the lowest VMA meeting the range
whatever installed it — a LOAD segment `elf_map` mapped (fs/binfmt_elf.c:395,
:399, both calls of `vm_mmap`) as readily as an anonymous mapping — and
`newbrk + PAGE_SIZE > vm_start_gap(next)` takes `goto out` for either
(:189-190).  The model keeps the two in separate ledgers and `brk_grow_ok`
tests the new page and the one above it against both.  No admitted run
reaches the `vm_reserved` half: `Run.valid_brk` starts the break at or
above `reserved_top` and `brk_r_ok` never resolves below `min_brk`, so the
image lies wholly under every page a grow installs, and a hand-built ledger
is the only way to put a reservation in the window — which stops being true
if the loader admits the static-PIE arm (`State.v`'s brk-band note, where
the break is moved to `ELF_ET_DYN_BASE` and the image lands elsewhere).
kernel: mm/mmap.c:brk; fs/binfmt_elf.c:elf_map@v6.18.46 -/
theorem brk_grow_flush_against_the_image_rejected :
    check_brk 69632 (mkEffect 69632 [] [(65536, 4096)]) m_image_flush = CheckReject := by
  brk_munmap_norm

/-- …and the unchanged break is the answer there (mm/mmap.c:187-190,
:209-212, Linux v6.18.46) — admitted on every grow, since `brk_r_ok` lets
a grow fail for reasons the ledger does not carry (`brk_grow_may_fail`);
the `vm_reserved` half of the test is the pin above's.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_flush_against_the_image_returns_break :
    check_brk 69632 (mkEffect 65536 [] []) m_image_flush = CheckOk m_image_flush [] := by
  brk_munmap_norm

/-- One page below the image the same grow is granted: a LOAD segment,
mapped `MAP_PRIVATE` (fs/binfmt_elf.c:1055, Linux v6.18.46) with `MAP_FIXED`
after the first LOAD (:1064-1065) or `MAP_FIXED_NOREPLACE` on the first
(:1072, :1146, :1173) — `elf_flags` takes no other flag, so never
`MAP_GROWSDOWN` — has neither `VM_GROWSDOWN` nor `VM_SHADOW_STACK` (`VM_NONE`
on riscv, include/linux/mm.h:386-388), so `vm_start_gap(next)` is its
`vm_start` (include/linux/mm.h:3704-3725, Linux v6.18.46) and the test at
mm/mmap.c:189 refuses only a segment starting under `newbrk + PAGE_SIZE`;
`do_brk_flags` installs the page (:194-195) and the reservation stays where
it was.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_one_page_below_the_image_grants :
    check_brk 69632 (mkEffect 69632 [] [(65536, 4096)]) m_image_gap
      = CheckOk (fixture (VmMaps.mkVmMapsFull [(4096, 4096), (73728, 4096)] [(65536, 4096)] []
                   65536 69632 demo_limit 0 demo_sp)) [] := by
  brk_munmap_norm

/-- A zero-fill beside the request equal to the break is refused: the
`oldbrk == newbrk` exit (mm/mmap.c:155-158, Linux v6.18.46) is above
`do_brk_flags` (:194-195), so `brk(65536)` on a break of 65536 installs
nothing — `brk_at_min_brk_returns_it`'s other side.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_at_min_brk_smuggled_zeros_rejected :
    check_brk 65536 (mkEffect 65536 [] [(65536, 4096)]) m_est = CheckReject := by
  brk_munmap_norm

/-- The shrink that failed unmapped nothing: each `goto out` of the shrink
block (mm/mmap.c:164-166, :173-175, Linux v6.18.46) is taken before a page
goes — `do_vmi_align_munmap` tears down only past its point of no return
(mm/vma.c:1577-1579), and its error exits (:1581-1585) are reached only
from before it (:1570-1571, :1574-1575), `clear_tree_failed` reattaching
what the gather detached (:1582, `reattach_vmas` :1351-1360); a VMA
`__split_vma` already split stays split (:1449-1456), which unmaps no byte.
So the old break beside the unmap the shrink would have made is refused:
`brk_shrink_may_fail`'s other side, at its request.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem brk_failed_shrink_smuggled_unmap_rejected :
    check_brk 65536 (SyscallEffect.mkEffectU 131072 [] [] [(65536, 65536)] [] []) m_grown
      = CheckReject := by
  brk_munmap_norm

/-- A grow answered with the old break installed nothing: `out:` answers
`origbrk` (mm/mmap.c:209-212, Linux v6.18.46) and is reached on the grow
path from before `do_brk_flags` (:149-151, :180-181, :189-190) or from its
own failure (:194-195), and every error exit of `do_brk_flags` returns
before a VMA is stored (mm/vma.c:2816-2823, :2838-2839, :2846-2847,
:2854-2855, :2868-2872), so the old break beside the zero-fill the grant
would have carried is refused — the other side of the admission
`brk_grow_may_fail` states, at its request.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_refused_grow_smuggled_zeros_rejected :
    check_brk 131072 (mkEffect 65536 [] [(65536, 65536)]) m_est = CheckReject := by
  brk_munmap_norm

/-- The zero-fill of a grant starts at the old page-aligned break and
nowhere else: `do_brk_flags(oldbrk, newbrk - oldbrk)` (mm/mmap.c:194-195,
Linux v6.18.46) with `oldbrk = PAGE_ALIGN(mm->brk)` (:154).  The same page
count one page up is refused; `brk_r_ok` passes here — the page is free of
`vm_reserved ++ vm_maps` and under `alloc_top` — so the refusal is the
`brk_zeros` comparison's.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_zeros_shifted_a_page_rejected :
    check_brk 69632 (mkEffect 69632 [] [(69632, 4096)]) m_est = CheckReject := by
  brk_munmap_norm

/-- A sub-page shrink frees nothing, so an unmap beside it is refused:
`PAGE_ALIGN(129024)` and `PAGE_ALIGN(131072)` are both 131072 and the
`oldbrk == newbrk` exit fires (mm/mmap.c:155-158, Linux v6.18.46) — the
spec-level pin of the same name on the checker, beside
`brk_subpage_shrink_frees_nothing`; the harness reads the lie as
`brk_shrink_frees.c`'s `reject --mutate brk#5:smuggle-unmap:a0:4096` case.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_subpage_shrink_smuggled_unmap_rejected :
    check_brk 129024 (SyscallEffect.mkEffectU 129024 [] [] [(129024, 4096)] [] []) m_grown
      = CheckReject := by
  brk_munmap_norm

/-- The same on the guarded page: a four-byte shrink inside it frees nothing
(`PAGE_ALIGN(69620) = PAGE_ALIGN(69624) = 69632`, the same exit), so the
page's unmap beside it is refused — `brk_same_page_shrink_preserves_noaccess`'s
other side.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_shrink_smuggled_unmap_rejected :
    check_brk 69620 (SyscallEffect.mkEffectU 69620 [] [] [(65536, 4096)] [] []) m_brk_same_page
      = CheckReject := by
  brk_munmap_norm

/-- A regrow inside the page never released exposes no zeroes: the same exit
(mm/mmap.c:155-158, Linux v6.18.46), so the byte-granular zero-fill over the
regrown bytes is refused — the spec-level pin of the same name on the
checker, beside `brk_same_page_regrow_preserves_noaccess`; the harness reads
it as `brk_shrink_frees.c`'s `reject --mutate brk#6:smuggle-zeros:a0+-8:8`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_regrow_smuggled_zeros_rejected :
    check_brk 69624 (mkEffect 69624 [] [(69620, 4)]) m_brk_same_page_shrunk = CheckReject := by
  brk_munmap_norm

/-- A cross-page grow zeroes the page it installs, not the bytes it was
asked for: `do_brk_flags` maps `[PAGE_ALIGN(69624), PAGE_ALIGN(69640))`,
the page `[69632, 73728)` (mm/mmap.c:153-154, :194-195, Linux v6.18.46), so
the raw `[old, new)` zero effect is refused — the spec-level pin of the
same name on the checker, beside `brk_unaligned_cross_page_zeros_exact_new_page`;
the harness reads it as `brk_shrink_frees.c`'s `reject --mutate
brk#8:drop-zeros,smuggle-zeros:a0+-16:16`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_cross_page_grow_byte_zeros_rejected :
    check_brk 69640 (mkEffect 69640 [] [(69624, 16)]) m_brk_same_page = CheckReject := by
  brk_munmap_norm

/-- The munmap witness on a zero length answers -EINVAL and nothing else:
`end == start` (mm/vma.c:1614-1616, Linux v6.18.46).  The checker's gate is
pinned both ways above (`munmap_len_zero_einval`,
`munmap_len_zero_success_rejected`); this is the witness's own copy of the
disjunct.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_witness_answers_einval_on_a_zero_length :
    munmap_witness 65536 0 one_map_model = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  brk_munmap_norm

end C_Mm_Mmap_brk_munmap

-- lean-port sentinel: ticket V-pilot-Mm-Mmap appends below this line

section V_pilot_Mm_Mmap

/-! ## V-pilot-Mm-Mmap — `brk` and `munmap` over the real table

WHAT IS TWINNED HERE.  The section above states each Rocq brk and munmap
example on the checker itself, because `checked_table` carried no row for
214 or 215 when it was written, and its header leaves "the
dispatcher-level restatements of these twins" to the registration.  This
is the registration.  Every `= CheckReject` example
`theories/LinuxProcessSem/Checks/Cases/Mm/Mmap.v` states on brk or munmap
— nine, each stated there through `check_syscall` and closed by
`vm_compute` — is restated here through the Lean `check_syscall`, over
`checked_table` itself, at the Rocq input: `brk_in req`, the request in
`a0`, and `munmap_in addr len`, the two words of Rocq's `mkInput 215
[addr; len; …]` in `a0` and `a1`.  Each takes its Rocq name with
`_over_the_real_table` after it, K6b's convention for the pins at which
the real table first answers a call, and its evidence line is the
checker-level twin's.  What such a pin adds to the twin above it is the
ARM's claim, which the C section's header set aside for the
registration: that the lookup at 214 and 215 finds `arm_brk` and
`arm_munmap` rather than the dispatcher's own decline, and which register
each argument is read from — a claim the acceptances carry, since a
refusal at the wrong register can coincide with the refusal at the right
one (`brk_in 16384` read off `a1` is a query, and 16384 is refused as its
answer too), and an acceptance cannot.

POLARITY is the C section's: a pin stated `= CheckReject` or
`= CheckUnmodeled` is positive to `tools/check_lean_pin_evidence.py` and
cites the kernel function whose answer the refused lie contradicts, or
`model:` where the refusal is the run's own budget or band. -/

/-- A `munmap` input: `a7 = 215`, `addr` in `a0` and `len` in `a1`, the
order `SYSCALL_DEFINE2(munmap, unsigned long, addr, size_t, len)`
(mm/mmap.c, Linux v6.18.46) declares; no memory.  The brk input is
`Checks/Cases/Mm/Mmap.lean`'s `brk_in`.  The number is a numeral, which is
how `tools/check_lean_pin_evidence.py` reads a pin's syscall off its
input. -/
def munmap_in (addr len : word) : SyscallInput :=
  SyscallInput.mkInput 215 [addr, len, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

set_option maxRecDepth 4096 in
/-- The lookup the dispatcher performs on a `brk_in`, computed once:
`in_sysno` is `214` whatever `a0` holds.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_brk_in (req : word) :
    lookup_ca checked_table (bv_unsigned (brk_in req).in_sysno) = some arm_brk :=
  lookup_ca_checked_table_brk

set_option maxRecDepth 4096 in
/-- …and on a `munmap_in`, for every address and length.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_munmap_in (addr len : word) :
    lookup_ca checked_table (bv_unsigned (munmap_in addr len).in_sysno) = some arm_munmap :=
  lookup_ca_checked_table_munmap

/-- Read a concrete `check_syscall` at a `brk_in` off: the lookup, the
arm's `arm_unfold`, then the C section's `brk_munmap_norm`.  `scoped`,
for the reason `check_norm` gives. -/
scoped macro "brk_dispatch_norm" : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [lookup_brk_in];
             simp only [arm_unfold]; brk_munmap_norm))

/-- …and at a `munmap_in`. -/
scoped macro "munmap_dispatch_norm" : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [lookup_munmap_in];
             simp only [arm_unfold]; brk_munmap_norm))

/-- Read a concrete `syscall_spec_witness` at a `brk_in` off. -/
scoped macro "brk_dispatch_witness_norm" : tactic =>
  `(tactic| (unfold syscall_spec_witness table_witness; rw [lookup_brk_in];
             simp only [arm_unfold]; brk_munmap_norm))

/-- …and at a `munmap_in`. -/
scoped macro "munmap_dispatch_witness_norm" : tactic =>
  `(tactic| (unfold syscall_spec_witness table_witness; rw [lookup_munmap_in];
             simp only [arm_unfold]; brk_munmap_norm))

/-! ### The nine Rocq `= CheckReject` examples, through `check_syscall` -/

/-- `munmap_without_unmap_rejected` over the real table: a 0 that declares
no unmap over a live page is refused, since the VMA really goes on Linux
(mm/vma.c:1626, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_without_unmap_rejected_over_the_real_table :
    check_syscall (munmap_in 65536 4096) (mkEffect 0 [] []) one_map_model = CheckReject := by
  munmap_dispatch_norm

/-- `munmap_near_max_is_einval` over the real table, both halves: -EINVAL
before the ledger is read (`start > TASK_SIZE`, mm/vma.c:1611-1612, Linux
v6.18.46), and a kernel claiming to have unmapped the mapping is refused.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_near_max_is_einval_over_the_real_table :
    check_syscall (munmap_in (Z_to_bv 64 (two_pow_64 - 8192)) 4096)
        (mkEffect (errno_ret EINVAL) [] []) near_ceiling_sum_model
      = CheckOk near_ceiling_sum_model []
    ∧ check_syscall (munmap_in (Z_to_bv 64 (two_pow_64 - 8192)) 4096)
        (SyscallEffect.mkEffectU 0 [] [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)] [] [])
        near_ceiling_sum_model
      = CheckReject := by
  constructor <;> munmap_dispatch_norm

/-- `munmap_high_addr_sum_wraps_is_einval` over the real table, both
halves: `start = 2^63, len = 2^63` is `start > TASK_SIZE` before `end` is
formed (mm/vma.c:1611-1612, Linux v6.18.46), and a 0 is refused.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_high_addr_sum_wraps_is_einval_over_the_real_table :
    check_syscall (munmap_in (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)))
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_syscall (munmap_in (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)))
        (mkEffect 0 [] []) one_map_model
      = CheckReject := by
  constructor <;> munmap_dispatch_norm

/-- `brk_zero_rejects_arbitrary` over the real table: a query's `out:`
returns `origbrk` and nothing else (mm/mmap.c:209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_zero_rejects_arbitrary_over_the_real_table :
    check_syscall (brk_in 0) (mkEffect 123456 [] []) m_est = CheckReject := by
  brk_dispatch_norm

/-- `brk_in_aslr_gap_rejects_moving` over the real table: below `min_brk`
the function has already left (mm/mmap.c:140-141, Linux v6.18.46), so a
kernel that moved the break down into the gap is refused.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_in_aslr_gap_rejects_moving_over_the_real_table :
    check_syscall (brk_in 16384) (mkEffect 16384 [] []) m_est = CheckReject := by
  brk_dispatch_norm

/-- `brk_grow_flush_against_neighbour_rejected` over the real table:
`newbrk + PAGE_SIZE > vm_start_gap(next)` takes `goto out` (mm/mmap.c:187-190,
Linux v6.18.46), so a claimed grant is refused.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_flush_against_neighbour_rejected_over_the_real_table :
    check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)]) m_neighbour_flush
      = CheckReject := by
  brk_dispatch_norm

/-- `brk_shrink_must_declare_unmaps` over the real table: the pages really
go (mm/mmap.c:173-175, Linux v6.18.46), so a shrink declaring no unmap is
refused.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_must_declare_unmaps_over_the_real_table :
    check_syscall (brk_in 65536) (mkEffect 65536 [] []) m_grown = CheckReject := by
  brk_dispatch_norm

/-- `brk_grow_beyond_budget_rejects_moving` over the real table: a two-page
grant under a one-page budget is not the kernel this run models.
model: `brk_budget_ok` under the fixture's declared `vm_limit`; the
refusal is the run's budget, not a line of Linux -/
theorem brk_grow_beyond_budget_rejects_moving_over_the_real_table :
    check_syscall (brk_in 73728) (mkEffect 73728 [] [(65536, 8192)]) m_tight_brk
      = CheckReject := by
  brk_dispatch_norm

/-- `brk_grow_across_demo_top_rejected_under_low_sp` over the real table:
under the low stack pointer the grant crosses the band the ledger imposes.
model: State.alloc_top, the band vm_init_sp - stack_max_size the ledger imposes (bugs/grants-into-the-stack-band.md) -/
theorem brk_grow_across_demo_top_rejected_under_low_sp_over_the_real_table :
    check_syscall (brk_in (Z_to_bv 64 (demo_top + 4096)))
        (mkEffect (Z_to_bv 64 (demo_top + 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 8192)])
        brk_top_lo_model
      = CheckReject := by
  brk_dispatch_norm

/-! ### The acceptances the same route carries, and the registers -/

/-- `brk_zero_returns_current_break` over the real table: the lookup finds
`arm_brk`, and the answer is `check_brk`'s (mm/mmap.c:140-141, :209-212,
Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_zero_returns_current_break_over_the_real_table :
    check_syscall (brk_in 0) (mkEffect 65536 [] []) m_est = CheckOk m_est [] := by
  brk_dispatch_norm

/-- `brk_grow_within_budget_grants` over the real table.  This is the pin
that reads the register: `brk_in 69632` holds the request in `a0` and 0 in
every other register, and an arm reading `a1` would see a query, whose
only answer is the unchanged 65536 — so the grant to 69632 is admitted
exactly when `a0` is the register read, as `SYSCALL_DEFINE1(brk, unsigned
long, brk)` (mm/mmap.c, Linux v6.18.46) reads it.
probe: testing/syscall-check/tests/brk_budget.c#conform --alloc-limit 0x10000 -- exact -/
theorem brk_grow_within_budget_grants_over_the_real_table :
    check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)]) m_tight_brk
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 4096)] 65536 69632 4096)
                   m_tight_brk) [] := by
  brk_dispatch_norm

/-- `brk_shrink_unmaps_freed_tail` over the real table
(`do_vmi_align_munmap(&vmi, brkvma, mm, newbrk, oldbrk, …)`,
mm/mmap.c:173-175, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_unmaps_freed_tail_over_the_real_table :
    check_syscall (brk_in 65536) (SyscallEffect.mkEffectU 65536 [] [] [(65536, 65536)] [] [])
        m_grown
      = CheckOk (with_vmmaps (mkVmMaps brk_reserved [] 65536 65536 demo_limit) m_grown) [] := by
  brk_dispatch_norm

/-- `munmap_len_zero_einval` over the real table: `end == start`
(mm/vma.c:1614-1616, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_len_zero_einval_over_the_real_table :
    check_syscall (munmap_in 65536 0) (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] := by
  munmap_dispatch_norm

/-- `munmap_ordinary_still_succeeds` over the real table: the exact mapping
is torn down and leaves the ledger (`do_vmi_align_munmap`, mm/vma.c:1557,
reached from :1626, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_ordinary_still_succeeds_over_the_real_table :
    check_syscall (munmap_in 65536 4096) (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [])
        one_map_model
      = CheckOk (with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) one_map_model) [] := by
  munmap_dispatch_norm

/-- …and with the two registers exchanged the same call is another call:
`munmap_in 4096 65536` asks for `[4096, 69632)`, which starts on free
space and runs across the mapping, the partial teardown the model declines
whatever the kernel answered (`munmap_partial_is_error` and
`munmap_spanning_past_the_mapping_is_unmodeled`, above).  So `a0` is
`addr` and `a1` is `len`, as `SYSCALL_DEFINE2(munmap, unsigned long,
addr, size_t, len)` (mm/mmap.c, Linux v6.18.46) declares them; an arm
reading them the other way round would accept the teardown the pin above
accepts here.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; mm/mmap.c:munmap@v6.18.46 -/
theorem munmap_registers_are_addr_then_len (eff : SyscallEffect) :
    check_syscall (munmap_in 4096 65536) eff one_map_model = CheckUnmodeled := by
  munmap_dispatch_norm

/-! ### The witnesses over the real table -/

/-- The tree's witness at a brk grow is `brk_witness`'s: the unchanged
break, no zeroes, no unmap (mm/mmap.c:209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem the_trees_witness_at_brk_is_the_break :
    syscall_spec_witness (brk_in 131072) m_est = Ok (mkEffect 65536 [] []) m_est [] := by
  brk_dispatch_witness_norm

/-- The tree's witness at an exact munmap is `munmap_witness`'s teardown
(mm/vma.c:1626, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem the_trees_witness_at_munmap_is_the_teardown :
    syscall_spec_witness (munmap_in 65536 4096) one_map_model
      = Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [])
           (with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) one_map_model) [] := by
  munmap_dispatch_witness_norm

/-- …and in the stack band it is the decline, the arm's own
(mm/vma.c:1619-1626, Linux v6.18.46: 0 either way, and the model cannot
say which page it was).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem the_trees_witness_at_munmap_in_the_stack_band_is_the_decline :
    syscall_spec_witness (munmap_in (Z_to_bv 64 demo_top) 4096) one_map_model = Unmodeled := by
  munmap_dispatch_witness_norm

/-! ### The table after this registration -/

/-- The two numbers sit in the table once each and in order.  Stated as a
FILTER of the table's numbers, as `checked_table_carries_222_once` is, so
that the pin survives the next registration.
kernel: include/uapi/asm-generic/unistd.h:__NR_brk,__NR_munmap@v6.18.46 -/
theorem checked_table_carries_214_then_215_once :
    (checked_table.map ca_no).filter (fun n => n == 214 || n == 215) = [214, 215] := by
  decide

end V_pilot_Mm_Mmap

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_misaligned_wrap_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 3 50 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_error_band_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4095)) 4096 3 50 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_exact_end_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) 4096 3 50 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_rounded_length_wrap_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 3 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_aligned_over_end_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 3 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_misaligned_wrap_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 0 50 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_error_band_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4095)) 4096 0 50 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_exact_end_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) 4096 0 50 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_rounded_length_wrap_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_aligned_over_end_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 0 50 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_misaligned_wrap_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 3 1048610 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_error_band_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4095)) 4096 3 1048610 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_exact_end_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) 4096 3 1048610 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_rounded_length_wrap_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 3 1048610 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_aligned_over_end_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 3 1048610 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_misaligned_wrap_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 8191)) 8192 0 1048610 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_error_band_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4095)) 4096 0 1048610 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- The spec declines this input before it inspects an effect.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_exact_end_any_effect_t206 (m : Model) (eff : SyscallEffect) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) 4096 0 1048610 mmap_fd_none 0 eff m = CheckUnmodeled := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_rounded_length_wrap_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 1048610 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm

/-- Both implementations reject this range with ENOMEM.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_aligned_over_end_t206 (m : Model) :
    check_mmap (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 0 1048610 mmap_fd_none 0
        (mkEffect (errno_ret ENOMEM) [] []) m = CheckOk m [] := by
  check_norm


end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mmap
