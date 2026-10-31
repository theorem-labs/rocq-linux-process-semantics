import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Mm.Mmap — what `brk`, `mmap` and `munmap` allow, read off against Linux

Worked examples over `Sys.Mm.Mmap`'s three specs, `brk_spec`, `mmap_spec`
and `munmap_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Mm/Mmap.v`.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ, and
every claim in it is a claim about what the kernel does, with the citation
beside it.

HOW THESE ARE STATED.  The Lean tree has no executable checker yet, so a
check is stated on the relation itself.  The strongest shape, used wherever
the admitted set is finite, is an `iff` over EVERY outcome `o`:

    mmap_spec … i m o ↔ o = A ∨ o = B ∨ o = C

which pins the positive half (A, B and C are admitted) and the negative half
(nothing else is — not another errno, not a wider unmap, not `Unmodeled`)
in one statement.  Where the arm chooses a placement the admitted set is
infinite, and the `iff` names the placement conditions explicitly — the
four the spec header of `Sys/Mm/Mmap.lean` lists (the Rocq PLACEMENT
section counts three, folding nonzero into its address-space bullet beside
the `alloc_top` bound), all of them
`get_unmapped_area` promises — and the concrete admissions and refusals
follow from it.  Not
exactly all of them, in two known directions.  The ceiling is this run's
`alloc_top`, where the kernel's search stops at `mmap_base` and its
argument check at `TASK_SIZE - len`: a honoured hint inside the stack
band, or a very large `argv` that lifts `mmap_base` above `alloc_top`, is
refused here rather than declined (`bugs/grants-into-the-stack-band.md`
records both).  The floor is `0 <`, which with the alignment conjunct is
4096: the kernel's is `mmap_min_addr`, which is exactly that on the
pinned guest (`testing/vm/kernel.fragment` builds no LSM, so
`CONFIG_DEFAULT_MMAP_MIN_ADDR=4096` is the whole floor) and 65536 on a
SELinux kernel, where `CONFIG_LSM_MMAP_MIN_ADDR` raises it
(`security/min_addr.c:update_mmap_min_addr`, `security/Kconfig`, Linux
v6.18.46); between the two bounds the placement is otherwise
unconstrained (`bugs/mmap-null-hint-placement-unconstrained.md`), and a
grant below a raised `mmap_min_addr` is admitted
(`bugs/mmap-null-hint-floor-is-the-first-page.md`;
`rw_grant_at_4096_admitted` pins the floor's value under the premise that
entry names).  A check closes by `Checks/Cases/Tactic.lean`'s `sys_norm`,
or `sys_refute` for a refutation: one simp set reads the spec off its
monad primitives, decides the closed gates and evaluates each post-state
and the `fixture` a check names to one constructor tree, and that file
says what the normal form is and why it takes two passes; a check whose
residue is arithmetic rather than a decided gate says so on its own
proof.  The mmap half registers three lemmas of its own in `sys_simp`
(`region_free_one`, `bvZ_4096`, `bvZ_8192`, in the section below): every
model this file defines is closed, and the second pass evaluates it along
with the values the ledger computations take (`maps_subtract` over a
literal, a page rounding, `lazy_interior`), but a grant's disjointness
from a one-entry ledger is `region_free` applied to a VARIABLE address,
which no evaluation closes, and `region_free_one` is what turns it into
the two-sided arithmetic the placement pins state;
`Checks/Cases/Prelude.lean`'s header says which fixtures the register does
have to unfold, and why.  The brk and munmap halves register their specs
and, for `brk`, one resolution lemma per fixture and request; their
section says why a `choose` over the resolved break needs one.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  A twin of
`Checks/ExecutableSpecs.v` would prove that a checker and this spec agree;
what these pins prove is that this spec and a named line of Linux agree,
which is the half a checker/spec agreement cannot supply. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The flags words these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- The plain anonymous word.
kernel: include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS@v6.18.46 -/
example : MAP_PRIVATE + MAP_ANONYMOUS = 34 := by decide
/-- …with `MAP_FIXED`.
kernel: include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS,MAP_FIXED@v6.18.46 -/
example : MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED = 50 := by decide
/-- …with `MAP_NORESERVE`.
kernel: include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS; include/uapi/asm-generic/mman.h:MAP_NORESERVE@v6.18.46 -/
example : MAP_PRIVATE + MAP_ANONYMOUS + MAP_NORESERVE = 16418 := by decide
/-- …with both.
kernel: include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS,MAP_FIXED; include/uapi/asm-generic/mman.h:MAP_NORESERVE@v6.18.46 -/
example : MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED + MAP_NORESERVE = 16434 := by decide
/-- …with `MAP_HUGETLB`.
kernel: include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS,MAP_HUGETLB@v6.18.46 -/
example : MAP_PRIVATE + MAP_ANONYMOUS + MAP_HUGETLB = 262178 := by decide
/-- The rw prot word.
kernel: include/uapi/asm-generic/mman-common.h:PROT_READ,PROT_WRITE@v6.18.46 -/
example : PROT_READ + PROT_WRITE = 3 := by decide
/-- The one errno the environment may answer on a modeled shape.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
example : mmap_errnos = [ENOMEM] := by decide

/-! ## The ledger arithmetic the placement pins spell out

A preference-free grant is disjoint from the one live page of
`one_map_model`, at 65536.  The placement `iff`s below state that
disjointness as the interval arithmetic it is -- the grant ends at or
before 65536, or starts at or after 69632 -- and not as
`region_free [(65536, 4096)] a n = true`, which is the spec's own decision
procedure restated on the side of the `iff` that is meant to be the
kernel's answer (tools/check_lean_pins.py, PIN-6).  The lemma here is how
the normal form reaches that spelling: `sys_norm` unfolds the spec to
`region_free` on the fixture's one-entry ledger, and this rewrite, in the
`sys_simp` set, opens it to its two inequalities, which the ground pass
then evaluates at the ledger's literals. -/

/-- `region_free` on a one-entry ledger `[(b, s)]` IS the disjointness of
`[a, a + n)` from `[b, b + s)`.  Stated over variables, not the fixture's
literals: the second `sys_norm` pass renders a literal as `65536#64`, and
a rewrite keyed on `(65536 : word)` would not match it.
model: `region_free` on a one-entry ledger unfolded to the interval test it decides; ledger arithmetic, not a kernel claim. -/
theorem region_free_one (b s a n : word) :
    region_free [(b, s)] a n = true
      ↔ (bv_unsigned a + bv_unsigned n ≤ bv_unsigned b
          ∨ bv_unsigned b + bv_unsigned s ≤ bv_unsigned a) := by
  simp only [region_free, iv_overlap, Bool.and_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_lt]
  omega

/-- A page length, as the integer the inequalities compare.
model: a `bv_unsigned` round-trip at a numeral, a rewrite for the placement pins. -/
theorem bvZ_4096 : bv_unsigned (4096 : word) = 4096 := by decide
/-- Two pages, likewise.
model: a `bv_unsigned` round-trip at a numeral, a rewrite for the placement pins. -/
theorem bvZ_8192 : bv_unsigned (8192 : word) = 8192 := by decide

attribute [sys_simp] region_free_one bvZ_4096 bvZ_8192

/-! ## Before any shape: the offset, the file, the length

`riscv_sys_mmap` (arch/riscv/kernel/sys_riscv.c, Linux v6.18.46) rejects a
misaligned `offset` with -EINVAL before calling into generic mm; then
`ksys_mmap_pgoff` (mm/mmap.c) resolves the fd when `MAP_ANONYMOUS` is clear;
then `do_mmap` answers `if (!len) return -EINVAL`.  Order is behaviour, and
each pin below fixes one pair of neighbours in that order. -/

/-- A misaligned offset is -EINVAL whatever the rest of the call says on
Linux (qemu-user reads the flags word first, and
bugs/mmap-shared-validate-refuses-qemu-user-eopnotsupp.md records the words
it answers otherwise): here a FILE-BACKED request naming a closed fd, which
would be -EBADF one step later.  The `iff` refuses that -EBADF and every
other answer.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem misaligned_offset_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 1 2 999 1 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and the anonymous spelling agrees, so a misaligned offset never reaches
a shape. 
probe: testing/syscall-check/tests/mmap_file_backed.c#conform -- anon-misaligned -/
theorem anonymous_misaligned_offset_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 34 mmap_fd_none 1 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The one misaligned-offset call that is DECLINED rather than answered: a
`len` whose page rounding wraps.  The pinned kernel still says -EINVAL, but
qemu-user's `target_mmap` (linux-user/mmap.c, QEMU 11.1.1) tests the length
first and says -ENOMEM; the intersection is empty, so `Unmodeled` is the only sound
answer (`mmap_pglen_ok_b`). 
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:do_mmap@v6.18.46 -/
theorem misaligned_offset_wrapping_len_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 (Z_to_bv 64 (-1)) 3 34 mmap_fd_none 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A file-backed mapping (`MAP_ANONYMOUS` clear) is `Unmodeled` at every
prot: the machine model has no readable-but-not-writable page and cannot
tie a mapping to its file (`mmap_spec`'s docstring).  Pinned at PROT_READ,
at rw, and at a closed fd, where Linux's own answer is `fget`'s -EBADF
(`ksys_mmap_pgoff`, mm/mmap.c, Linux v6.18.46) — deliberately NOT given,
because qemu-user never resolves the fd. 
probe: testing/syscall-check/tests/mmap_file_backed.c#fail-closed -- live-read -/
theorem file_backed_read_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 1 2 3 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …the rw spelling of the same file-backed request.
probe: testing/syscall-check/tests/mmap_file_backed.c#fail-closed -- live-rw -/
theorem file_backed_rw_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 2 3 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …and a closed fd, where Linux's own answer is `fget`'s -EBADF, is declined rather than answered.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem file_backed_closed_fd_is_unmodeled_not_ebadf (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 2 999 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The file gate precedes the length gate: with `MAP_ANONYMOUS` clear
`ksys_mmap_pgoff` `fget`s before anything reads `len` (mm/mmap.c:573-577,
Linux v6.18.46) — -EBADF here, fd 999 being closed — while a LIVE
non-hugetlb fd falls through to `do_mmap`'s same -EINVAL (:347-348) on the
pinned configuration: `vm_mmap_pgoff` runs the LSM and fsnotify permission
hooks between the two (mm/util.c:575-577), both 0 there — `security_mmap_file`
is the `CONFIG_SECURITY`-less stub (include/linux/security.h:1173-1177) and
`fsnotify_mmap_perm` is the `CONFIG_FANOTIFY_ACCESS_PERMISSIONS`-less stub
(include/linux/fsnotify.h:221-225; the real body, :174-184, returns 0 for a
file with no HSM watcher) — and an LSM variant may answer first.  The
arm reads no fd table, so it cannot tell the two answers apart and
declines rather than guess (`mmap_plain_anon_b`).
kernel: mm/mmap.c:ksys_mmap_pgoff,do_mmap@v6.18.46 -/
theorem zero_len_file_backed_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 0 1 2 999 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- With flags 0 the huge-page conjunct holds, but the anonymous-bit
conjunct makes `mmap_plain_anon_b` false. This pins the helper before the
arm's `mmap_anon_b` gate: `ksys_mmap_pgoff` distinguishes the file-backed
path by the same bit (mm/mmap.c:573-577, Linux v6.18.46).
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem mmap_plain_anon_without_anonymous_bit_is_false :
    mmap_plain_anon_b 0 = false := by decide

/-- A zero-length plain anonymous mapping is -EINVAL (`do_mmap`,
mm/mmap.c:347-348, Linux v6.18.46), and the `iff` refuses the placement,
the smuggled zero-fill and the -ENOMEM a lying kernel might offer instead:
the length gate PRECEDES `errno_from`. 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem zero_len_anonymous_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 0 3 34 mmap_fd_none 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Inside the plain anonymous shape the -EINVAL holds whatever `prot` says
(here PROT_EXEC too, a prot the shapes below decline): nothing between
`ksys_mmap_pgoff`'s fall-through and mm/mmap.c:347 reads `prot`. 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem zero_len_precedes_prot (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 0 7 34 mmap_fd_none 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and whatever `addr` and `MAP_FIXED` say: a zero-length MAP_FIXED over a
live page is -EINVAL and unmaps NOTHING. 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem zero_len_fixed_is_einval_and_unmaps_nothing (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 0 0 50 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- With `MAP_HUGETLB` set the flags are read first — `ksys_mmap_pgoff`
(mm/mmap.c:584-601, Linux v6.18.46) answers from `hstate_sizelog` and
`hugetlb_file_setup` before the length is examined — and the model has no
huge pages, so it declines. 
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem zero_len_hugetlb_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 0 3 262178 mmap_fd_none 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A recorded wrong answer.  0x100023 is a MAP_SHARED_VALIDATE word with
MAP_ANONYMOUS and MAP_FIXED_NOREPLACE, and at zero length Linux answers
`do_mmap`'s -EINVAL (mm/mmap.c:347-348, Linux v6.18.46), since it reads an
anonymous word's type only at :539-540.  qemu-user reads the type first and
answers -EOPNOTSUPP for a bit outside its legacy set, MAP_FIXED_NOREPLACE
among them (linux-user/syscall.c:6171-6178, QEMU 11.1.1).  This gate proves
the -EINVAL alone, and bugs/mmap-shared-validate-refuses-qemu-user-eopnotsupp.md
records it; the fix flips this pin.
no-row: no recorded run passes a MAP_SHARED_VALIDATE word, and the harness never runs qemu-user.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem shared_validate_noreplace_zero_len_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 0 3 1048611 mmap_fd_none 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and the same word at a misaligned offset, where Linux answers
`riscv_sys_mmap`'s -EINVAL (arch/riscv/kernel/sys_riscv.c:16-17, Linux
v6.18.46) and qemu-user the same -EOPNOTSUPP.  The fix flips this pin too.
no-row: no recorded run passes a MAP_SHARED_VALIDATE word, and the harness never runs qemu-user.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem shared_validate_noreplace_misaligned_offset_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 1048611 mmap_fd_none 1 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The boundary: 0x80023 swaps MAP_FIXED_NOREPLACE for MAP_SYNC, which is
inside qemu-user's set (linux-user/syscall.c:6176, QEMU 11.1.1), so qemu
goes on to `target_mmap`, whose zero-length test answers -EINVAL
(linux-user/mmap.c:972-975, QEMU 11.1.1).  This -EINVAL is both
implementations' answer, and the fix keeps it.
no-row: no recorded run passes a MAP_SHARED_VALIDATE word.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem shared_validate_sync_zero_len_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 0 3 524323 mmap_fd_none 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and at a misaligned offset, where `target_mmap` answers -EINVAL at
its offset test (linux-user/mmap.c:990-993, QEMU 11.1.1), as Linux does.
no-row: no recorded run passes a MAP_SHARED_VALIDATE word.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem shared_validate_sync_misaligned_offset_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 524323 mmap_fd_none 1 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-! ## The fresh rw grant

`mmap(NULL, 4096, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)`
on a ledger holding one live page at 65536. -/

/-- THE PLACEMENT CONDITIONS, and nothing else.  Either the environment
refuses (-ENOMEM, the one errno `mmap_errnos` carries), or the kernel
grants a page that is page-aligned, nonzero, ending at or below this run's
`alloc_top` — the MODEL's ceiling, its stand-in for the stack band
(`bugs/grants-into-the-stack-band.md`); the kernel's own is `TASK_SIZE`,
mm/mmap.c:857 in `__get_unmapped_area` — and disjoint from every recorded
mapping, which is all `get_unmapped_area` promises for a preference-free
request (both generic searches ask `vm_unmapped_area` for a gap,
`generic_get_unmapped_area` at mm/mmap.c:712-718 and
`generic_get_unmapped_area_topdown` at :763-770, Linux v6.18.46) —
zero-filled, and recorded so later grants cannot alias it.  No search rule: placement is randomized per exec (`arch_mmap_rnd`,
mm/util.c:399-411), so the admissible SET is what is true of every run. 
kernel: mm/mmap.c:do_mmap,__get_unmapped_area,generic_get_unmapped_area,generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area,unmapped_area_topdown; mm/util.c:arch_mmap_rnd@v6.18.46 -/
theorem rw_grant_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ ∃ a : word,
           o = Ok (mkEffect a [] [(a, 4096)])
                  (fixture (VmMaps.mkVmMapsFull [] [(a, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []
           ∧ bv_unsigned a % page_size = 0 ∧ 0 < bv_unsigned a
           ∧ bv_unsigned a + 4096 ≤ demo_top
           ∧ (bv_unsigned a + 4096 ≤ 65536 ∨ 69632 ≤ bv_unsigned a)) := by
  sys_norm

/-- A placement at 0x40000000 is admitted: the page arrives zero-filled and
the ledger records it. 
trace: mmap_null_hint/001 -/
theorem rw_grant_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- …and so is the environment's -ENOMEM, with nothing changed. 
trace: errno_mmap/001 -/
theorem rw_grant_enomem_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []) := by
  sys_norm

/-- The grant may end exactly AT the run's grant top (the bound is
inclusive)… 
trace: mmap_null_hint/005 -/
theorem rw_grant_ending_at_alloc_top_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096), (65536, 4096)] []
                      0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- …but not start there: one page higher is inside the stack band
`[alloc_top, sp)` that no grant may reach (`State.alloc_top`).
`mmap_base` is the top-down layout's half of that band; under the legacy bottom-up layout only the stack guard gap bounds a grant, and the band is the model's own bound (`State.alloc_top`) — not Linux's: `bugs/grants-into-the-stack-band.md` records the pinned kernel honouring a HINT inside it.  What is refused here is a NULL-hint placement: the top-down search's `high_limit` is the `mmap_base` that `mmap_base` in mm/util.c set (`generic_get_unmapped_area_topdown`, mm/mmap.c:766), while the legacy search (:713-714) and the top-down fallback (:778-783) run bottom-up from their own floors to `mmap_end`, so only a full address space puts one this high.
kernel: mm/util.c:mmap_base@v6.18.46 -/
theorem rw_grant_above_alloc_top_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) m' evs) := by
  sys_refute

/-- Address 0 is refused: a NULL-hint search cannot yield it — `unmapped_area`
clamps `low_limit` to `mmap_min_addr` (mm/vma.c:2898-2899, Linux v6.18.46)
and so does `unmapped_area_topdown` (:2955-2956); the top-down search itself
starts at `PAGE_SIZE` (mm/mmap.c:765), its bottom-up fallback at
`TASK_UNMAPPED_BASE` (:781) and the legacy search at `mmap_base` (:713) — and `cap_mmap_addr` (security/commoncap.c:1459-1471)
would answer -EPERM for the address if one were returned, so a kernel
reporting a grant at 0 is lying either way.  The -EPERM itself is the
MAP_FIXED story (`fixed_rw_at_zero_is_unmodeled`).
kernel: mm/vma.c:unmapped_area,unmapped_area_topdown; mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem rw_grant_at_zero_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0 [] [(0, 4096)]) m' evs) := by
  sys_refute

/-- …and the first page is admitted: the model's floor is `0 <` under page
alignment, so 4096, and on the pinned guest it is the kernel's: a NULL-hint
search runs from `mmap_min_addr` — the `low_limit` clamp of
`unmapped_area_topdown` over the top-down search's own `PAGE_SIZE` — and
`testing/vm/kernel.fragment` pins that at 4096 (`CONFIG_DEFAULT_MMAP_MIN_ADDR`,
no LSM to raise it).
Premise: `mmap_min_addr` is 4096.  A kernel whose floor is raised — the
riscv defconfig's 65536 under `CONFIG_LSM_MMAP_MIN_ADDR`, or a raised
`vm.mmap_min_addr` — never makes this placement, and the model admits it
all the same (`bugs/mmap-null-hint-floor-is-the-first-page.md`).
kernel: mm/vma.c:unmapped_area_topdown; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_at_4096_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect 4096 [] [(4096, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(4096, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- A placement must be page-aligned. 
trace: mmap_null_hint/002 -/
theorem rw_grant_unaligned_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 1 [] [(1, 4096)]) m' evs) := by
  sys_refute

/-- A grant may not land on a page the process already owns: a gap is by
construction free of every VMA in the searched interval (mm/vma.c:2885-2930). 
kernel: mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_on_owned_page_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 65536 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- A fresh rw grant EXPOSES ZEROES: an effect that places the page but
fills nothing is refused (the bytes would be unreadable where Linux serves
zeros), and so is one that zero-fills the wrong range. 
kernel: mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem rw_grant_without_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] []) m' evs) := by
  sys_refute

/-- …and so is one that zero-fills the wrong range.
kernel: mm/memory.c:do_anonymous_page@v6.18.46 -/
theorem rw_grant_shifted_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40001000, 4096)]) m' evs) := by
  sys_refute

/-- The errno set is -ENOMEM and nothing else: -EBADF (no fd is involved)
and -EACCES (real for `openat`, not for mmap) are lies. 
trace: errno_mmap/002 -/
theorem rw_grant_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and -EACCES, real for `openat`, is not mmap's.
trace: errno_mmap/003 -/
theorem rw_grant_eacces_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EACCES) [] []) m' evs) := by
  sys_refute

/-- The modeled shape never declines: `Unmodeled` is not an admitted outcome
of this call. 
trace: mmap_null_hint/001 -/
theorem rw_grant_never_unmodeled (i : SyscallInput) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model Unmodeled := by
  sys_refute

/-- `fd` is not read under `MAP_ANONYMOUS` — `ksys_mmap_pgoff` never
mentions it on that arm (mm/mmap.c, Linux v6.18.46) — so a live-looking
`fd` of 3 changes nothing. 
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem rw_grant_fd_ignored (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 34 3 0 i one_map_model o ↔
      mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model o := by
  sys_norm

/-- Without `MAP_FIXED` a non-NULL `addr` is a HINT the kernel may honor or
ignore: the same admitted set as the NULL-hint call. 
kernel: mm/mmap.c:generic_get_unmapped_area,generic_get_unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_hint_is_only_a_hint (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x50000000 4096 3 34 mmap_fd_none 0 i one_map_model o ↔
      mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model o := by
  sys_norm

/-- A `len` within a page of `2^64` rounds to ZERO in the kernel's machine
arithmetic and `do_mmap` answers -ENOMEM (`len = PAGE_ALIGN(len); if (!len)
return -ENOMEM`, mm/mmap.c).  In the model the `alt` collapses onto -ENOMEM
because the success arm's guard is unsatisfiable — twice over for the rw
shape: the budget conjunct asks for `2^64` bytes of backing (what the proof
below decides), and the placement conjunct `a + PAGE_ALIGN(len) ≤ alloc_top`
has no solution either, which is the half the PROT_NONE twin below pins,
that shape having no budget conjunct to fall back on. 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_wrapping_len_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 (Z_to_bv 64 (-1)) 3 34 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model [] := by
  sys_norm

/-- The PROT_NONE twin: no budget conjunct, so the placement bound alone
forces -ENOMEM.  This proof goes on past `sys_norm`: the placement conjunct
is refuted by ARITHMETIC rather than decided — a length that rounds to
`2^64` cannot fit under `demo_top`, which `omega` gets from
`bv_unsigned ≥ 0` and no simp set decides.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noaccess_grant_wrapping_len_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 (Z_to_bv 64 (-1)) 0 34 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model [] := by
  sys_norm
  constructor
  -- The normal form distributes the disjointness disjunction
  -- (`region_free_one`) over the existential, so the grant arrives as two
  -- cases; the placement bound `htop` refutes both the same way.
  · rintro (h | ⟨a, -, -, -, htop, -⟩ | ⟨a, -, -, -, htop, -⟩)
    · exact h
    all_goals
      exfalso
      unfold bv_unsigned at htop
      omega
  · intro h; exact Or.inl h

/-! ## The backing budget

Ordinary rw grants are charged eagerly against `vm_limit`, page-rounded.
The gate sits INSIDE the success resolution, so over budget the model MUST
answer -ENOMEM rather than decline (the forced out-of-memory point of
issue #131). -/

/-- One live page under a 4 KiB budget: spent. -/
def spent_budget_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 4096 0 demo_sp)

/-- One live page under an 8 KiB budget: one page left. -/
def one_page_left_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 0 demo_sp)

/-- A spent budget forces -ENOMEM: no placement is admissible. 
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem rw_grant_over_budget_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i spent_budget_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) spent_budget_model [] := by
  sys_norm

/-- `len = 1` is metered page-rounded: it costs the whole page the budget
no longer has. 
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem rw_grant_len1_charges_a_page (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 1 3 34 mmap_fd_none 0 i spent_budget_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) spent_budget_model [] := by
  sys_norm

/-- `len = 4097` charges TWO pages: with one page left it is forced -ENOMEM… 
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem rw_grant_len4097_charges_two_pages (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4097 3 34 mmap_fd_none 0 i one_page_left_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_page_left_model [] := by
  sys_norm

/-- …while `len = 4096` fits it to the byte and is granted. 
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem rw_grant_fits_budget_exactly (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_page_left_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-! ## MAP_NORESERVE

`MAP_NORESERVE` (include/uapi/asm-generic/mman.h:11, Linux v6.18.46) changes
only the
commit accounting: the model records the mapping as LAZY and charges each
page on first touch, so the grant itself is free.  It masks no other bit. -/

/-- A NORESERVE grant on a spent budget is admitted, with lazy backing for
exactly the granted interior.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noreserve_grant_ignores_budget (i : SyscallInput) :
    mmap_spec 0 4096 3 16418 mmap_fd_none 0 i spent_budget_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (with_vm_backing [(0x40000000, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 4096 0 demo_sp))) []) := by
  sys_norm

/-- `MAP_NORESERVE` masks no other flag bit: with `MAP_POPULATE` (0x8000)
beside it the call leaves the modeled surface. 
kernel: mm/mmap.c:do_mmap; mm/util.c:vm_mmap_pgoff@v6.18.46 -/
theorem noreserve_populate_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 49186 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `MAP_POPULATE` alone declines the same way.
kernel: mm/mmap.c:do_mmap; mm/util.c:vm_mmap_pgoff@v6.18.46 -/
theorem populate_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 32802 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## The fresh PROT_NONE reservation -/

/-- The same placement conditions as the rw grant, with no budget conjunct;
the reservation lands in BOTH ledgers and the effect is an unmap — an
inaccessible range must erase any stale overlay bytes and exposes none. 
kernel: mm/mmap.c:do_mmap,__get_unmapped_area,generic_get_unmapped_area,generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem noaccess_grant_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 0 34 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ ∃ a : word,
           o = Ok (SyscallEffect.mkEffectU a [] [] [(a, 4096)] [] [])
                  (fixture (VmMaps.mkVmMapsFull [] [(a, 4096), (65536, 4096)] [(a, 4096)] 0 0 demo_limit 0 demo_sp)) []
           ∧ bv_unsigned a % page_size = 0 ∧ 0 < bv_unsigned a
           ∧ bv_unsigned a + 4096 ≤ demo_top
           ∧ (bv_unsigned a + 4096 ≤ 65536 ∨ 69632 ≤ bv_unsigned a)) := by
  sys_norm

/-- A PROT_NONE reservation at 0x40000000 is admitted: both ledgers record it and the unmap is emitted.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noaccess_grant_admitted (i : SyscallInput) :
    mmap_spec 0 4096 0 34 mmap_fd_none 0 i one_map_model
      (Ok (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [(0x40000000, 4096)]
                      0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- An inaccessible grant exposes NO bytes: a zero-fill in its place is
refused…
`calc_vm_prot_bits` gives a PROT_NONE request neither `VM_READ` nor `VM_WRITE`.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noaccess_grant_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 0 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)]) m' evs) := by
  sys_refute

/-- …and so is one that leaves the range's stale mutable bytes readable. 
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noaccess_grant_without_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 0 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] []) m' evs) := by
  sys_refute

/-- A PROT_NONE reservation consumes no backed budget: granted under a
budget of ZERO, where the rw spelling is forced to -ENOMEM. -/
def zero_budget_model : Model := fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 0 0 demo_sp)

/-- Granted under a budget of zero.
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noaccess_grant_ignores_budget (i : SyscallInput) :
    mmap_spec 0 4096 0 34 mmap_fd_none 0 i zero_budget_model
      (Ok (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096)] [(0x40000000, 4096)] 0 0 0 0 demo_sp)) []) := by
  sys_norm

/-- …where the rw spelling is forced to -ENOMEM.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem rw_grant_under_zero_budget_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i zero_budget_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) zero_budget_model [] := by
  sys_norm

/-! ## The MAP_FIXED argument gate

Shared by both MAP_FIXED shapes, in Linux's order (Linux v6.18.46):
`do_mmap`'s length bounds (mm/mmap.c:368-370, :377-378, -ENOMEM), then
`__get_unmapped_area`'s bounds (:824-825, :857-858, -ENOMEM), then the
alignment test (:859-860, -EINVAL), then `security_mmap_addr` (:862-863,
-EPERM at address 0).  None of the four reads `prot`. -/

/-- An `addr + PAGE_ALIGN(len)` reaching `2^64` is -ENOMEM — and it is
decided BEFORE the alignment test, so this unaligned address does not get
its -EINVAL.  Pinned for both prots: the gate does not branch on `prot`. 
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_overflowing_len_is_enomem (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0x1001 (Z_to_bv 64 (-1)) 0 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The rw spelling of the same overflow.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_overflowing_len_is_enomem (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0x1001 (Z_to_bv 64 (-1)) 3 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_sum_exactly_two_pow_64_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)) 3 50 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- below
the grant top, an unaligned MAP_FIXED address is -EINVAL and NOTHING ELSE
(`generic_get_unmapped_area` hands a MAP_FIXED `addr` back unrounded,
mm/mmap.c:700-701, so :859 sees the caller's address).  That is one errno
short of Linux: `do_mmap` tests `mm->map_count > sysctl_max_map_count`
(:377-378, -ENOMEM) before `__get_unmapped_area` reaches the alignment test
(:859-860), so a guest at its map-count ceiling answers -ENOMEM here and
this arm, answering -EINVAL ahead of its `alt`, refuses it -- the false
reject the entry records, inherited from Rocq.  The iff is the model's
answer today; the negative twin `fixed_unaligned_enomem_rejected` is the
kernel's answer stated as the refutation it gets. 
kernel: mm/mmap.c:generic_get_unmapped_area,__get_unmapped_area@v6.18.46 -/
theorem fixed_unaligned_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x1001 4096 0 50 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- the
-ENOMEM a guest at its map-count ceiling answers is REFUSED.  Linux tests
the map count in `do_mmap` (mm/mmap.c:377-378, Linux v6.18.46) before the
alignment test in `__get_unmapped_area` (:859-860), so on such a guest an
unaligned MAP_FIXED address is -ENOMEM and not -EINVAL; the arm answers
-EINVAL ahead of its `alt` and allows nothing else.  Stated as the
refutation the model gives today; an arm that put the alignment test
behind the errno alternative flips this to an admission and the header
line of `Sys/Mm/Mmap.lean` to `fixed:`.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_unaligned_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x1001 4096 0 50 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- Above the grant top the -ENOMEM of :857 (`addr > TASK_SIZE - len`) may
still fire before the alignment test, and the model does not know
`TASK_SIZE` on this arm, so it declines instead of committing to -EINVAL. 
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_unaligned_above_alloc_top_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top + 1)) 4096 0 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- The rw spelling declines the same way: on both MAP_FIXED arms the
`alloc_top` test precedes the alignment test, as :857 precedes :859, so an
arm that answered -EINVAL here would have swapped the two.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_unaligned_above_alloc_top_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top + 1)) 4096 3 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- Address 0 is DECLINED for both MAP_FIXED shapes: Linux answers -EPERM
there (`cap_mmap_addr`, security/commoncap.c:1459-1471, Linux v6.18.46,
below `dac_mmap_min_addr`, 4096 by DEFAULT) and the model does not carry
-EPERM, so neither a success nor an -EINVAL nor an -ENOMEM is admitted.
The bound is a policy, not a constant — `CONFIG_DEFAULT_MMAP_MIN_ADDR`,
the `vm.mmap_min_addr` sysctl (unbounded above; 65536 in Debian's shipped
config), and under SELinux a separate -EACCES below
`CONFIG_LSM_MMAP_MIN_ADDR` (`selinux_mmap_addr`, security/selinux/hooks.c:4006-4017) — and the arms answer from 4096 up, so
`fixed_rw_clear_of_the_image_is_modeled` below holds on the default policy
alone: `bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`.
kernel: security/commoncap.c:cap_mmap_addr; security/selinux/hooks.c:selinux_mmap_addr@v6.18.46 -/
theorem fixed_noaccess_at_zero_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 0 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- The rw spelling declines the same way.
kernel: security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem fixed_rw_at_zero_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and neither is a COMMIT at 0, over a ledger that OWNS the page (Rocq
`mmap_fixed_rw_commit_at_zero_is_unmodeled`).  Linux's -EPERM comes from
`security_mmap_addr` on the address it is about to return
(`__get_unmapped_area`, mm/mmap.c:862-863, Linux v6.18.46), which never
consults the VMA tree, so a MAP_FIXED at 0 over a live range is refused
exactly as one over free space is.  That is why the gate sits above the
containment test: were it inside the fresh sub-case, this ledger would let
the model answer a success no kernel produces — and the two pins above, both
on a ledger where 0 is free, could not tell.
kernel: mm/mmap.c:__get_unmapped_area; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem fixed_rw_commit_at_zero_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 50 mmap_fd_none 0 i
        (fixture (VmMaps.mkVmMapsFull [] [(0, 8192)] [] 0 0 8192 0 demo_sp)) o ↔ o = Unmodeled := by
  sys_norm

/-! ### The rw shape is exactly PROT_READ|PROT_WRITE at offset 0

`mmap_fixed_rw_b` asks for `prot == PROT_READ + PROT_WRITE` and for
`off == 0`, and each conjunct is a decision: without the first, a MAP_FIXED
private anonymous request carrying any prot but PROT_NONE (which
`mmap_fixed_noaccess_b` takes first) would take the rw commit; without the
second, one carrying a page-aligned offset would.  The pins below refuse
both on the middle page of `noaccess_three_pages`, the spot where
`fixed_rw_commit_iff` admits the commit for the rw spelling, so a spec that
dropped either conjunct could not close them.  Both were owed since the
mmap port (allowlisted as "no pin"); the 2026-09-18 mutation sweep re-found
them.  The non-FIXED shapes that leave the surface the same way are under
"Shapes that leave the modeled surface" below. -/

/-- PROT_READ on the commit spot is DECLINED, not committed.  Linux maps
it: `do_mmap` (mm/mmap.c:400-401, Linux v6.18.46) turns prot into vm_flags
through `calc_vm_prot_bits` (include/linux/mman.h:140-147, Linux
v6.18.46), which sets VM_READ and not VM_WRITE, and a store to the page
then faults: `access_error` (arch/riscv/mm/fault.c:249-272, Linux
v6.18.46) refuses an EXC_STORE_PAGE_FAULT on a VMA without VM_WRITE.  The
model's commit hands back WRITABLE zeroes (`RiscvSemantics.ms_mem` has no
readable-but-not-writable page: the arm's header), so letting it through
here would model a store that Linux kills with SIGSEGV.  The request
satisfies no shape predicate, so it never enters the rw arm and falls
through `mmap_spec`'s whole dispatch to its own final `unmodeled`.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits; arch/riscv/mm/fault.c:access_error@v6.18.46 -/
theorem fixed_read_only_commit_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 1 50 mmap_fd_none 0 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-- PROT_READ|PROT_EXEC declines the same way: VM_EXEC changes nothing
about the missing VM_WRITE.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_rx_commit_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 5 50 mmap_fd_none 0 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-- PROT_READ|PROT_WRITE|PROT_EXEC declines too.  Linux ordinarily grants
it, writable and executable at once, though not in every process:
`mmap_region` (mm/vma.c:2767, Linux v6.18.46) answers -EACCES when
`map_deny_write_exec` (include/linux/mman.h:201-219) sees VM_WRITE|VM_EXEC
in a process under `prctl(PR_SET_MDWE)`, and `vm_mmap_pgoff` (mm/util.c:575)
consults the LSM hook first, where an enforcing SELinux policy can refuse
anonymous PROT_EXEC as execmem (`__file_map_prot_check`,
security/selinux/hooks.c:3968).  Either way the rw commit describes a readable-writable page and says
nothing about execution, and the arm carries no rwx shape; the request
leaves the modeled surface rather than being folded into the rw commit.
kernel: mm/mmap.c:do_mmap; mm/vma.c:mmap_region; include/linux/mman.h:map_deny_write_exec@v6.18.46 -/
theorem fixed_rwx_commit_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 7 50 mmap_fd_none 0 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-- The same PROT_READ request over a LIVE rw page is declined as well.
Linux replaces the page with fresh read-only zeroes: `__mmap_prepare`
(mm/vma.c:2386-2444, Linux v6.18.46) gathers the old VMA and clears its
PTEs at :2441 before `__mmap_new_vma` installs the VM_READ-only one.  The
model's rw commit over the same fixture (`fixed_rw_contained_iff`)
re-zeroes the page too, but leaves one every store may touch, which is not
the page Linux leaves.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_read_only_over_live_page_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 1 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- A page-aligned NONZERO offset on the rw spelling is declined.  Linux
discards the offset of a private anonymous request, but reads it first:
`riscv_sys_mmap` (arch/riscv/kernel/sys_riscv.c:16-17, Linux v6.18.46)
refuses a misaligned one with -EINVAL, `do_mmap` refuses one whose page
number plus the length in pages wraps with -EOVERFLOW (mm/mmap.c:373-374),
and only then (:533-538) overwrites pgoff with `addr >> PAGE_SHIFT`.  For
the one-page offset here the kernel's answer is therefore the one
`fixed_rw_commit_iff` pins for offset 0.  The model has not taken that
reading: `mmap_fixed_rw_b` asks `w_is0 off`, and the arm declines rather
than grants, a fail-closed bound on the modeled surface and not a claim
that the kernel refuses.
kernel: mm/mmap.c:do_mmap; arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem fixed_rw_commit_at_page_offset_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 3 50 mmap_fd_none 4096 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-! ## MAP_FIXED wholly inside one live mapping: THREE resolutions

Linux produces three answers (Linux v6.18.46).  `__mmap_prepare`
(mm/vma.c:2386-2444) tears the old range down at :2441, through
`vms_clean_up_area` (mm/vma.c:1281-1293), BEFORE `__mmap_new_vma`
(mm/vma.c:2506-2508, :2515-2518, Linux v6.18.46) can fail in
`vm_area_alloc` (mm/vma_init.c:28, Linux v6.18.46) or `vma_iter_prealloc`
(mm/vma.h:508, Linux v6.18.46); a failure there sends `__mmap_region` to
`abort_munmap:` (mm/vma.c:2729-2730, Linux v6.18.46) with `clear_ptes`
false and `vms_abort_munmap_vmas` (mm/vma.c:2349-2369, Linux v6.18.46)
leaves a GAP (:2360-2366).  Before :2441 a failure — `max_map_count` in
`vms_gather_munmap_vmas` (mm/vma.c:1389-1393, Linux v6.18.46), or for rw
the commit charge in `__mmap_prepare` (mm/vma.c:2422-2429, Linux v6.18.46)
— leaves the range intact.  So: an errno with the range preserved, the success, and
an errno with the range DESTROYED. -/

/-- PROT_NONE over the live page: the success installs the guard page
(both ledgers) and emits the exact unmap; the destructive failure removes
the page from both ledgers and emits the same unmap. 
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_contained_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 demo_limit 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The three, one by one, as a reader would list them. 
kernel: mm/vma.c:vms_gather_munmap_vmas,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_contained_errno_preserves (i : SyscallInput) :
    mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []) := by
  sys_norm

/-- The success.
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_noaccess_contained_succeeds (i : SyscallInput) :
    mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model
      (Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The destructive failure.
kernel: mm/vma.c:__mmap_new_vma,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_contained_errno_may_destroy (i : SyscallInput) :
    mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model
      (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- What the three exclude: -EINVAL (the address is aligned), a destructive
failure that unmaps MORE than the request, one that destroys the range yet
reports success-shaped zeros, and `Unmodeled`. 
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_contained_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A destructive failure unmaps exactly `[vms->start, vms->end)`, never more.
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_destructive_unmap_must_be_the_request (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] []) m' evs) := by
  sys_refute

/-- A PROT_NONE result exposes no zeros.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem fixed_noaccess_contained_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 65536 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- The replacement is an ordinary path: the shape never declines.
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_noaccess_contained_never_unmodeled (i : SyscallInput) :
    ¬ mmap_spec 65536 4096 0 50 mmap_fd_none 0 i one_map_model Unmodeled := by
  sys_refute

/-- The rw COMMIT of the middle page of a three-page PROT_NONE reservation:
the success exposes zeroes over exactly that page and splits the no-access
interval into two remnants (`maps_subtract` is `__split_vma` on the model's
intervals); the destructive failure cuts the page out of both ledgers and
leaves the remnants. 
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_commit_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 3 50 mmap_fd_none 0 i noaccess_three_pages o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages []
       ∨ o = Ok (mkEffect 69632 [] [(69632, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
                          0 0 16384 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (73728, 4096)] [(65536, 4096), (73728, 4096)]
                          0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- The commit's success is budget-gated: committing a reserved slice costs
its page.  Under a budget of zero only the two errno resolutions remain.
On Linux the refused charge (`__mmap_prepare`, mm/vma.c:2422-2429, Linux
v6.18.46) is
decided BEFORE the teardown and is the non-destructive errno; the
destructive resolution the model keeps admitting is its budget-independent
over-approximation of the allocations past the teardown, as in Rocq. -/
def three_pages_zero_budget : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 12288)] 0 0 0 0 demo_sp)

/-- Under a budget of zero only the two errno resolutions remain (`three_pages_zero_budget`'s docstring says which is which on Linux).
The destructive disjunct is that declared over-approximation, not a reading: the refused charge returns from `__mmap_prepare` before `vms_clean_up_area`, so `vms_abort_munmap_vmas` reattaches and Linux leaves the range intact.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_commit_over_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 3 50 mmap_fd_none 0 i three_pages_zero_budget o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) three_pages_zero_budget []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (73728, 4096)] [(65536, 4096), (73728, 4096)]
                          0 0 0 0 demo_sp)) []) := by
  sys_norm

/-- Replacing an already-accessible slice costs NOTHING: the delta Linux
charges (`pglen - vms.nr_accounted`) is zero, so an rw MAP_FIXED over the
live rw page succeeds even at an exactly-spent budget, and re-zeroes the
page. 
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_over_live_rezeroes_at_spent_budget (i : SyscallInput) :
    mmap_spec 65536 4096 3 50 mmap_fd_none 0 i spent_budget_model
      (Ok (mkEffect 65536 [] [(65536, 4096)]) spent_budget_model []) := by
  sys_norm

/-- A NORESERVE commit is lazy: admitted under a budget of zero, with the
committed page recorded as lazily backed rather than charged.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem fixed_rw_noreserve_commit_ignores_budget (i : SyscallInput) :
    mmap_spec 69632 4096 3 16434 mmap_fd_none 0 i three_pages_zero_budget
      (Ok (mkEffect 69632 [] [(69632, 4096)])
          (with_vm_backing [(69632, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
                        0 0 0 0 demo_sp))) []) := by
  sys_norm

/-! ## MAP_FIXED meeting nothing: TWO resolutions

With `vms.nr_pages` zero there is nothing to tear down and
`vms_abort_munmap_vmas` returns at its first test (mm/vma.c:2354-2355,
Linux v6.18.46), so the destructive resolution cannot arise.  The request
is an ordinary grant naming its own address — the same guards as the
hint-placed arm, conjunct for conjunct — and it hands back exactly the
address it was given. -/

/-- The rw MAP_FIXED over a free range: the environment's -ENOMEM, or the grant at its own address.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_fresh_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The PROT_NONE spelling.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_fresh_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 0 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [(0x40000000, 4096)]
                          0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- MAP_FIXED hands back the address it was given: a placement elsewhere,
and a 0 return, are refused. 
kernel: mm/mmap.c:generic_get_unmapped_area,__get_unmapped_area@v6.18.46 -/
theorem fixed_fresh_returns_its_address (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x50000000 [] [(0x50000000, 4096)]) m' evs) := by
  sys_refute

/-- …nor 0.
kernel: mm/mmap.c:generic_get_unmapped_area,__get_unmapped_area@v6.18.46 -/
theorem fixed_fresh_zero_return_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0 [] [(0x40000000, 4096)]) m' evs) := by
  sys_refute

/-- No destructive resolution over a free range: an errno that unmaps the
(never-mapped) request is refused. 
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_fresh_has_no_destructive_failure (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(0x40000000, 4096)] [] []) m' evs) := by
  sys_refute

/-- The PROT_NONE spelling: no destructive resolution over a free range either.
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_fresh_has_no_destructive_failure (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 0 50 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(0x40000000, 4096)] [] []) m' evs) := by
  sys_refute

/-! ## MAP_FIXED that SPANS: three resolutions and re-cut remnants

`vms_gather_munmap_vmas` (mm/vma.c:1372, Linux v6.18.46) splits the first
VMA at `addr` (:1401) and the last at the end (:1422), detaches everything
between, and `__mmap_region` installs one mapping over the request.  The
parts of each entry OUTSIDE the request survive both the success and the
destructive failure (`vms_abort_munmap_vmas` writes NULL over exactly
`[vms->start, vms->end)`, mm/vma.c:2365-2366, Linux v6.18.46). -/

/-- Two live pages with a free page between them. -/
def two_maps_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (73728, 4096)] [] 0 0 demo_limit 0 demo_sp)

/-- Over two live pages and the free page between them: three resolutions, the request replaced whole.
kernel: mm/vma.c:vms_gather_munmap_vmas,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_span_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 12288 3 50 mmap_fd_none 0 i two_maps_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) two_maps_model []
       ∨ o = Ok (mkEffect 65536 [] [(65536, 12288)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 demo_limit 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 12288)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- A partial overlap keeps the REMNANT: the request covers the second page
of a two-page mapping and one free page past it; the first page survives
in both the success and the destructive failure. -/
def two_page_map_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp)

/-- The remnant survives every resolution (`two_page_map_model`'s docstring).
kernel: mm/vma.c:vms_gather_munmap_vmas,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_partial_overlap_keeps_the_remnant (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 8192 3 50 mmap_fd_none 0 i two_page_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) two_page_map_model []
       ∨ o = Ok (mkEffect 69632 [] [(69632, 8192)])
              (fixture (VmMaps.mkVmMapsFull [] [(69632, 8192), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 8192)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- A destructive span failure must not take the remnant with it. 
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_span_errno_unmapping_the_remnant_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 69632 8192 3 50 mmap_fd_none 0 i two_page_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 12288)] [] []) m' evs) := by
  sys_refute

/-- THE PROT_NONE TWIN of the partial overlap (Rocq
`mmap_fixed_noaccess_span_reserves_the_request` and
`mmap_fixed_noaccess_span_errno_destroys_only_the_request`): the request is
owned and inaccessible, the remnant survives, and the effect is an unmap
rather than a zero-fill.  No budget gate, because the request lands in
`vm_noaccess` whole and backed accounting can only fall
(`mmap_fixed_noaccess_span_next`), as Linux charges nothing for it:
`accountable_mapping` wants `VM_WRITE` (mm/vma.c:2326-2336, Linux v6.18.46,
the return at :2335; the call at :2422).
kernel: mm/vma.c:vms_gather_munmap_vmas,__mmap_prepare,accountable_mapping,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_partial_overlap_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 8192 0 50 mmap_fd_none 0 i two_page_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) two_page_map_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 69632 [] [] [(69632, 8192)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(69632, 8192), (65536, 4096)] [(69632, 8192)]
                          0 0 demo_limit 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 8192)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- Ownership GROWS by the page that met nothing and backing FALLS by the
page that was accessible (Rocq `mmap_fixed_noaccess_span_owns_more_and_backs_less`).
model: the two ledgers of `fixed_noaccess_partial_overlap_iff`'s pre- and
success post-state, read through `vm_live_bytes` and `vm_backed_bytes`. -/
theorem fixed_noaccess_span_owns_more_and_backs_less :
    vm_live_bytes (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp) = 8192
    ∧ vm_live_bytes (VmMaps.mkVmMapsFull [] [(69632, 8192), (65536, 4096)] [(69632, 8192)]
                      0 0 demo_limit 0 demo_sp) = 12288
    ∧ vm_backed_bytes (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp) = 8192
    ∧ vm_backed_bytes (VmMaps.mkVmMapsFull [] [(69632, 8192), (65536, 4096)] [(69632, 8192)]
                        0 0 demo_limit 0 demo_sp) = 4096 := by
  decide

/-- The PROT_NONE abort is all-or-nothing too: a failure that unmaps only
part of the request is refused (Rocq
`mmap_fixed_noaccess_span_errno_partial_unmap_rejected`); the rw half is
the negative side of `fixed_rw_partial_overlap_keeps_the_remnant`'s `iff`…
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_span_errno_partial_unmap_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 69632 8192 0 50 mmap_fd_none 0 i two_page_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] []) m' evs) := by
  sys_refute

/-- …and one that takes the remnant with it is refused as for rw.
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_span_errno_unmapping_the_remnant_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 69632 8192 0 50 mmap_fd_none 0 i two_page_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 12288)] [] []) m' evs) := by
  sys_refute

/-- A PROT_NONE span that ZERO-FILLS is refused (Rocq
`mmap_fixed_noaccess_span_success_with_zeros_rejected`): nothing becomes
readable — `do_mmap` (mm/mmap.c:400, Linux v6.18.46) folds `prot` through
include/linux/mman.h's `calc_vm_prot_bits`, which gives PROT_NONE neither
`VM_READ` nor `VM_WRITE` — so the effect is an unmap and never `eff_zeros`.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem fixed_noaccess_span_zero_fill_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 69632 8192 0 50 mmap_fd_none 0 i two_page_map_model
        (Ok (mkEffect 69632 [] [(69632, 8192)]) m' evs) := by
  sys_refute

/-- A request covered by two ADJACENT entries is spanning, not contained:
`map_contains` asks whether ONE entry covers the range.  It is still
replaced whole. -/
def adjacent_maps_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 0 0 demo_limit 0 demo_sp)

/-- Two adjacent entries replaced whole.
kernel: mm/vma.c:vms_gather_munmap_vmas,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_over_adjacent_entries_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 8192 3 50 mmap_fd_none 0 i adjacent_maps_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) adjacent_maps_model []
       ∨ o = Ok (mkEffect 65536 [] [(65536, 8192)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- A contained-style success that left the two entries in place would
misdescribe the ledger Linux leaves (one VMA over the request). 
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_rw_over_adjacent_entries_unmerged_ledger_rejected (i : SyscallInput) :
    ¬ mmap_spec 65536 8192 3 50 mmap_fd_none 0 i adjacent_maps_model
        (Ok (mkEffect 65536 [] [(65536, 8192)]) adjacent_maps_model []) := by
  sys_refute

/-! ### …and the PROT_NONE replacement that spans

The same three resolutions, for the same reasons (the section header
above), with one difference that is the arm's whole point: the success is
NOT budget-gated.  `__mmap_prepare` (mm/vma.c:2422-2429, Linux v6.18.46)
charges a mapping only when `accountable_mapping` (mm/vma.c:2326-2336)
holds, and that is `(vm_flags & (VM_NORESERVE | VM_SHARED | VM_WRITE)) ==
VM_WRITE`, false for PROT_NONE; `fixed_noaccess_span_ignores_budget` pins
it against a budget the rw span of the same request does not fit.  Before
these pins nothing in the Lean tree exercised the spanning PROT_NONE arm of
`mmap_spec` -- Rocq's `Checks/Cases/Mm/Mmap.v` has pinned it since #483
(`mmap_fixed_noaccess_span_reserves_the_request` and the four examples after
it), and #718 ported the rw span's pins without them: docs/lean-port/REDTEAM.md
replaced the arm with `Unmodeled` and every check stayed green.
`fixed_noaccess_span_never_unmodeled` is that hack, as a negative test. -/

/-- PROT_NONE over two live pages and the free page between them: the
success installs one inaccessible entry over the request in both ledgers,
the destructive failure removes every entry it met, and both emit the
exact unmap; the non-destructive -ENOMEM leaves the ledger as it was.
Which failure is which on Linux: the non-destructive one is the RLIMIT_AS
refusal of `__mmap_prepare` (mm/vma.c:2418-2419, Linux v6.18.46), raised
while the old entries are only gathered, so the abort reattaches them; the
destructive one is `__mmap_new_vma` (mm/vma.c:2506-2508) failing to
allocate the replacement after `__mmap_prepare` (mm/vma.c:2441) has already
cleared the range, so the abort stores NULL over it.
kernel: mm/vma.c:vms_gather_munmap_vmas,__mmap_prepare,accountable_mapping,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_span_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 12288 0 50 mmap_fd_none 0 i two_maps_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) two_maps_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 12288)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 12288)] 0 0 demo_limit 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 12288)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The arm answers: replacing it with `Unmodeled` falsifies this.
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_noaccess_span_never_unmodeled (i : SyscallInput) :
    ¬ mmap_spec 65536 12288 0 50 mmap_fd_none 0 i two_maps_model Unmodeled := by
  sys_refute

/-- A PROT_NONE success exposes no zeroes: the rw-shaped success is refused.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem fixed_noaccess_span_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 12288 0 50 mmap_fd_none 0 i two_maps_model
        (Ok (mkEffect 65536 [] [(65536, 12288)]) m' evs) := by
  sys_refute

/-- One live page under an 8 KiB budget, the Lean `span_tight_model` of
Rocq's `Checks/Cases/Mm/Mmap.v`: an rw replacement over it and the two
free pages past it would back 12288 bytes, more than the budget holds. -/
def span_tight_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 0 demo_sp)

/-- The PROT_NONE span is not charged: the same request the rw span cannot
fit is admitted whole, owned and inaccessible, under the same budget.
`accountable_mapping` is false for a mapping without VM_WRITE, so
`__mmap_prepare` charges nothing; a budget gate copied from the rw span onto
this arm falsifies this.
kernel: mm/vma.c:accountable_mapping,__mmap_prepare@v6.18.46 -/
theorem fixed_noaccess_span_ignores_budget (i : SyscallInput) :
    mmap_spec 65536 12288 0 50 mmap_fd_none 0 i span_tight_model
      (Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 12288)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 12288)] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-- ...where the rw span of the same request is charged for the pages it
newly backs (`map->charged = map->pglen - vms->nr_accounted`, then
`security_vm_enough_memory_mm`) and keeps only its two errno resolutions:
the budget is what separates the two arms, and this is the half that shows
the budget bites.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_span_over_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 12288 3 50 mmap_fd_none 0 i span_tight_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) span_tight_model []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 12288)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-! ## MAP_FIXED over the image: the one shape that still declines

The image's LOAD reservations are `State.Image` segments, not entries of
this ledger, so a replacement there has no representation; Linux would
replace them like any pages.  Both prots decline; one page clear of the
image is an ordinary free-range MAP_FIXED. -/

/-- Linux would replace the image pages like any others; the ledger cannot represent it.
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_rw_over_the_image_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 4096 4096 3 50 mmap_fd_none 0 i image_at_4096 o ↔ o = Unmodeled := by
  sys_norm

/-- The PROT_NONE spelling.
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_noaccess_over_the_image_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 4096 4096 0 50 mmap_fd_none 0 i image_at_4096 o ↔ o = Unmodeled := by
  sys_norm

/-- One page clear of the image is an ordinary free-range MAP_FIXED.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_clear_of_the_image_is_modeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 8192 4096 3 50 mmap_fd_none 0 i image_at_4096 o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) image_at_4096 []
       ∨ o = Ok (mkEffect 8192 [] [(8192, 4096)])
              (fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(8192, 4096)] [] 0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- The image reached only AFTER the free-range test fails: a request
meeting the image AND a live page still declines, for both prots — the
`vm_reserved` gate is the last one, and it is on the ledger, not on `prot`. -/
def image_span_model : Model :=
  fixture (VmMaps.mkVmMapsFull [(65536, 4096)] [(69632, 4096)] [] 0 0 16384 0 demo_sp)

/-- Meeting the image AND a live page still declines.
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_rw_spanning_the_image_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 8192 3 50 mmap_fd_none 0 i image_span_model o ↔ o = Unmodeled := by
  sys_norm

/-- …for PROT_NONE too.
kernel: mm/vma.c:__mmap_region@v6.18.46 -/
theorem fixed_noaccess_spanning_the_image_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 8192 0 50 mmap_fd_none 0 i image_span_model o ↔ o = Unmodeled := by
  sys_norm

/-- A preference-free grant may not be placed ON the image either. 
kernel: mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_on_the_image_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i image_at_4096
        (Ok (mkEffect 4096 [] [(4096, 4096)]) m' evs) := by
  sys_refute

section A18

/-! ## MAP_FIXED_NOREPLACE: placed exactly, refused rather than replaced

The two NOREPLACE shapes take the MAP_FIXED argument gate and split once
on the ledger (`Sys/Mm/Mmap.lean`'s section of the same name carries the
reading): a range `vm_reserved ++ vm_maps` leaves free is the free-range
MAP_FIXED sub-case again, and a range meeting anything — the image
included — is -EEXIST with nothing changed, beside the -ENOMEM every arm
admits.  The flag words are the bit alone (1048610, 0x100022), with
MAP_FIXED beside it (1048626, 0x100032) and with MAP_NORESERVE beside it
(1064994, 0x104022). -/

/-- Over a free range the bit is the ordinary grant naming its own address,
exactly as `fixed_rw_fresh_iff` above.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_free_range_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The PROT_NONE spelling reserves, as `fixed_noaccess_fresh_iff` does.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_noaccess_free_range_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 0 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [(0x40000000, 4096)]
                          0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- On a free range -EEXIST is not an answer: nothing the ledger records
meets the request, so `find_vma_intersection` finds nothing and `do_mmap`
goes on to grant.  (What the ledger does not record — the vdso/vvar pair,
qemu-user's own guest vdso, the host mappings qemu-user keeps for itself,
such as its heap, which without `-R` its host `mmap` answers EEXIST over
(`mmap_h_eq_g`, linux-user/mmap.c:612-625, QEMU 11.1.1, on a 4 KiB host;
`mmap_frag` or `mmap_h_gt_g`'s middle mapping, :372-386 and :884-898,
QEMU 11.1.1, on a 16 or 64 KiB host), qemu-user's
reservation of the gaps between LOAD segments, and the stack qemu-user
maps whole under `-s` or `QEMU_STACK_SIZE` above 8 MiB — is the residual
of bugs/mmap-placement-admits-unreachable-addresses.md, which names the
first three, of bugs/mmap-noreplace-refuses-qemu-user-eexist-in-a-load-gap.md
and of bugs/mmap-noreplace-refuses-qemu-user-eexist-on-a-large-stack.md.)
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_free_range_eexist_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EEXIST) [] []) m' evs) := by
  sys_refute

/-- …for the PROT_NONE spelling too.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_noaccess_free_range_eexist_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 0 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EEXIST) [] []) m' evs) := by
  sys_refute

/-- The free-range grant hands back the address it was given.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:generic_get_unmapped_area,__get_unmapped_area@v6.18.46 -/
theorem noreplace_free_range_returns_its_address (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x50000000 [] [(0x50000000, 4096)]) m' evs) := by
  sys_refute

/-- The rw grant is charged like any: over a spent budget only the -ENOMEM
remains.
no-row: stated over a hand-built ledger at fixture addresses; the budget-refusal row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem noreplace_over_budget_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1048610 mmap_fd_none 0 i spent_budget_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) spent_budget_model [] := by
  sys_norm

/-- …while the MAP_NORESERVE spelling a sanitizer runtime issues is lazy:
granted on the spent budget, the page recorded as lazily backed.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noreplace_noreserve_ignores_budget (i : SyscallInput) :
    mmap_spec 0x40000000 4096 3 1064994 mmap_fd_none 0 i spent_budget_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (with_vm_backing [(0x40000000, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] []
                        0 0 4096 0 demo_sp))) []) := by
  sys_norm

/-- Over a live page: -EEXIST with the ledger unchanged, beside the
environment's -ENOMEM (`do_mmap` tests `mm->map_count >
sysctl_max_map_count`, mm/mmap.c:377-378, Linux v6.18.46, before the
intersection, and the model counts no maps).
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_live_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) one_map_model []) := by
  sys_norm

/-- The PROT_NONE spelling is refused the same way.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_noaccess_over_live_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 0 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) one_map_model []) := by
  sys_norm

/-- The replacement MAP_FIXED would perform over the live page
(`fixed_rw_commit_iff` above) is refused with the bit: this is the lie the
bit exists to refuse.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_live_replacement_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 65536 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- -EEXIST is the errno, not just an errno: the alignment -EINVAL a model
running the refusal first could confuse it with is refused on an aligned
request.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_over_live_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A refusal changes nothing, so an -EEXIST that also claims a zero-fill
is refused.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_eexist_with_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EEXIST) [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- ANY mapped page refuses the request: a two-page request whose second
page is the live one is -EEXIST, although its first page is free
(`find_vma_intersection` is `mt_find` over the whole range).
Premise: `dac_mmap_min_addr` is its default 4096 (under qemu-user, the
host's, and no host page this request maps through starts below it), and
no enforcing SELinux policy denies the caller `memprotect:mmap_zero` below
`CONFIG_LSM_MMAP_MIN_ADDR`
(`bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`).
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_partial_overlap_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 61440 8192 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) one_map_model []) := by
  sys_norm

/-- MAP_FIXED | MAP_FIXED_NOREPLACE is MAP_FIXED_NOREPLACE: `do_mmap` folds
the NOREPLACE bit into MAP_FIXED (mm/mmap.c:361-362, Linux v6.18.46) and
tests the NOREPLACE bit alone (:410), so the combined word is -EEXIST over
the live page where MAP_FIXED alone replaces it (`fixed_rw_commit_iff`).
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_with_fixed_over_live_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 3 1048626 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) one_map_model []) := by
  sys_norm

/-- A kernel letting MAP_FIXED win the combined word is the wrong kernel.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_with_fixed_replacement_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 65536 4096 3 1048626 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 65536 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- …and over a free range the combined word grants, as the bit alone does.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_with_fixed_free_range_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1048626 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- Over the image's LOAD reservation the MAP_FIXED spelling declines
(`fixed_rw_over_the_image_is_unmodeled` above), having no way to replace
it; the NOREPLACE spelling replaces nothing, and those pages are VMAs
`load_elf_binary` installed, so the answer is -EEXIST.
Premise: `dac_mmap_min_addr` is its default 4096 (under qemu-user, the
host's, and no host page this request maps through starts below it), and
no enforcing SELinux policy denies the caller `memprotect:mmap_zero` below
`CONFIG_LSM_MMAP_MIN_ADDR`
(`bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`).
no-row: stated over a hand-built ledger at fixture addresses; the row over a probe's own image is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_the_image_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 4096 4096 3 1048610 mmap_fd_none 0 i image_at_4096 o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) image_at_4096 []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) image_at_4096 []) := by
  sys_norm

/-- …and so is a request meeting the image AND a live page, which the
MAP_FIXED spelling declines too (`fixed_rw_spanning_the_image_is_unmodeled`).
no-row: stated over a hand-built ledger at fixture addresses; the row over a probe's own image is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_spanning_the_image_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 8192 0 1048610 mmap_fd_none 0 i image_span_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) image_span_model []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) image_span_model []) := by
  sys_norm

/-- A forged success over the image is refused.
no-row: stated over a hand-built ledger at fixture addresses; the row over a probe's own image is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_the_image_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 4096 4096 3 1048610 mmap_fd_none 0 i image_at_4096
        (Ok (mkEffect 4096 [] [(4096, 4096)]) m' evs) := by
  sys_refute

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- order
is behavior: the alignment -EINVAL of `__get_unmapped_area` is decided
before the intersection test, so an unaligned address INSIDE the live page
is -EINVAL and not -EEXIST.  It is -EINVAL alone, one errno short of Linux
as `fixed_unaligned_over_live_is_einval` is: `do_mmap` tests the map count
(mm/mmap.c:377-378, Linux v6.18.46) before `__get_unmapped_area` reaches
the alignment test (:859-860), and the gate this arm shares with MAP_FIXED
answers ahead of its `alt`.
no-row: stated over a hand-built ledger at fixture addresses; the unaligned-address row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_unaligned_inside_live_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65537 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- …so -EEXIST there is refused.
no-row: stated over a hand-built ledger at fixture addresses; the unaligned-address row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_unaligned_inside_live_eexist_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 65537 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EEXIST) [] []) m' evs) := by
  sys_refute

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- the
-ENOMEM a guest at its map-count ceiling answers there (mm/mmap.c:377-378
before :859-860, Linux v6.18.46) is refused, for the reason
`fixed_unaligned_over_live_enomem_rejected` gives.
no-row: stated over a hand-built ledger at fixture addresses; the unaligned-address row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_unaligned_inside_live_enomem_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 65537 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- the
PROT_NONE spelling takes the same gate: -EINVAL inside the live page, and
one errno short of Linux in the same way.
no-row: stated over a hand-built ledger at fixture addresses; the unaligned-address row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_unaligned_inside_live_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 65537 4096 0 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- the
gate answers -EINVAL alone here, one errno short twice over.  At the
map-count ceiling `do_mmap`'s -ENOMEM (mm/mmap.c:377-378, Linux v6.18.46)
comes before `__get_unmapped_area` tests the alignment (:859-860), as for
`noreplace_unaligned_inside_live_enomem_rejected`.  And
bugs/mmap-fixed-misaligned-refuses-older-riscv-enomem.md records the
second: where riscv64's `arch_get_mmap_end` ended a nonzero address's
search at `VA_USER_SV39` (v6.6-rc1 to v6.6.110, v6.7.y and v6.8.y), a
misaligned request whose page-rounded length exceeds
`2^38 - mmap_min_addr` (for a floor at most `2^38`) is -ENOMEM wherever
below `2^47` it starts, and this one starts above `2^38`, at
0x4000000001.  Either fix restates this
pin.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_misaligned_past_the_sv39_end_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 274877906945 274877906944 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- below
the floor the gate answers -EINVAL alone too, and is one errno short in
both ways.  At the map-count ceiling `do_mmap`'s -ENOMEM (mm/mmap.c:377-378,
Linux v6.18.46) comes first, as above.  And where `arch_get_mmap_end` was
`addr + len` (v6.9.y and v6.10 to v6.10.9), a misaligned request starting
below `mmap_min_addr` and ending at or above it is -ENOMEM, at address 1
under the 4096 default among them.  Either fix restates this pin.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_misaligned_below_the_floor_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 1 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- under
a raised floor the -ENOMEM is every kernel's on Sv48 but form 1's: with
`mmap_min_addr` at `2^46`, which the unbounded sysctl allows, both address
searches answer -ENOMEM for `len > mmap_end - mmap_min_addr`
(`generic_get_unmapped_area`, mm/mmap.c:697-698, and its top-down twin at
:747-748, Linux v6.18.46) before `__get_unmapped_area` tests the alignment
(:859-860), so this `2^46 + 4096`-byte request at address 1 is -ENOMEM
there, and at the map-count ceiling `do_mmap`'s -ENOMEM (:377-378) comes
first under any floor.  Form 1 of
bugs/mmap-fixed-misaligned-refuses-older-riscv-enomem.md (v6.6-rc1 to
v6.6.110, v6.7.y and v6.8.y) ends this address's search at
`VA_USER_SV39`, where this floor wraps the unsigned
`2^38 - mmap_min_addr`, so the test never fires and the misaligned
address gets the gate's -EINVAL.  The gate answers the default floor's
-EINVAL alone, the refusal
bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md records,
and the -ENOMEM that bugs/mmap-fixed-misaligned-refuses-older-riscv-enomem.md
asks of the misaligned branch restates this pin.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,generic_get_unmapped_area,__get_unmapped_area@v6.18.46 -/
theorem noreplace_misaligned_past_a_raised_floor_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 1 70368744181760 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- The rest of the MAP_FIXED gate, word for word: a page-rounded end
reaching `2^64` is -ENOMEM at every ledger, decided before the alignment.
no-row: quantified over every ledger, at a range reaching `2^64` that no recorded run requests yet; the row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_overflowing_len_is_enomem (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0x1001 (Z_to_bv 64 (-1)) 3 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- …for PROT_NONE too: the length wraps to 0 under `PAGE_ALIGN` and
`do_mmap` answers -ENOMEM (mm/mmap.c:368-370, Linux v6.18.46) before it
reads the address.
no-row: quantified over every ledger, at a range reaching `2^64` that no recorded run requests yet; the row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_noaccess_overflowing_len_is_enomem (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0x1001 (Z_to_bv 64 (-1)) 0 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- …and at address 0 too: the wrap gate is read before the address-0
decline, so the length wins there as it does under MAP_FIXED
(`fixed_at_zero_wrapping_len_is_enomem`).  Linux answers the wrapped
`PAGE_ALIGN` at mm/mmap.c:368-370 (v6.18.46), before its address search
runs, and qemu-user's `target_mmap` answers the same -ENOMEM before it
reads the address (linux-user/mmap.c:983-988, QEMU 11.1.1), so arms that
read the address first would decline an answer both give.
no-row: quantified over every ledger, at a range reaching `2^64` that no recorded run requests yet; the row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_at_zero_wrapping_len_is_enomem (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 (Z_to_bv 64 (-1)) 3 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- …on the PROT_NONE arm as on the rw one.
no-row: quantified over every ledger, at a range reaching `2^64` that no recorded run requests yet; the row is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_noaccess_at_zero_wrapping_len_is_enomem (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 (Z_to_bv 64 (-1)) 0 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_ending_at_two_pow_64_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 3 1048610 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_ending_at_two_pow_64_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 0 1048610 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- Address 0 declines, for the policy reason the MAP_FIXED arms give
(`fixed_rw_at_zero_is_unmodeled` above).
kernel: mm/mmap.c:__get_unmapped_area; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem noreplace_at_zero_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …both prots.
kernel: mm/mmap.c:__get_unmapped_area; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem noreplace_noaccess_at_zero_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 0 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- A range starting AT `alloc_top` declines, as under MAP_FIXED
(`fixed_rw_starting_at_alloc_top_is_unmodeled` above): the band above it
may be the stack, and :857's `TASK_SIZE` bound is not consulted.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_above_alloc_top_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 demo_top) 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …both prots.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_above_alloc_top_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 demo_top) 4096 0 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Unmodeled := by
  sys_norm

/-- The `alloc_top` test precedes the alignment test, as :857 precedes
:859: an unaligned address above the grant top declines rather than
answer -EINVAL, for the reason `fixed_unaligned_above_alloc_top_is_unmodeled`
gives — the -ENOMEM of :857 may still fire against a `TASK_SIZE` the arm
does not consult.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_unaligned_above_alloc_top_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top + 1)) 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …both prots.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_unaligned_above_alloc_top_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top + 1)) 4096 0 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Unmodeled := by
  sys_norm

/-- The bit is matched, not stripped, so every other declined shape stays
declined with it: an extra flag bit (MAP_POPULATE)…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_populate_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1081378 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …MAP_SHARED…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_shared_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1048609 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …an executable prot…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_exec_prot_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 7 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and a page-aligned nonzero offset.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_nonzero_offset_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1048610 mmap_fd_none 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- The PROT_NONE shape holds `off` to 0 on its own conjunct, so the same
offset declines there too.  Linux answers both: `__get_unmapped_area`
treats the page offset of anonymous memory as zero (mm/mmap.c:838-840,
Linux v6.18.46), so this is the narrowing the spec's shapes section
names, not a refusal.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_nonzero_offset_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 0 1048610 mmap_fd_none 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-! ### The refusal at its edges -/

/-- The destructive failure MAP_FIXED admits over a live page (an errno
with the range gone, `fixed_rw_commit_iff` above) is no NOREPLACE answer:
the refusal returns at :410-413, before `mmap_region` unmaps anything.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_live_destroyed_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- …nor for the PROT_NONE spelling.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_noaccess_over_live_destroyed_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 65536 4096 0 1048610 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- A request ending exactly where the live page begins meets nothing:
`find_vma_intersection` searches `[addr, addr + len - 1]`, so the range
touching from below is free and grants.
Premise: `dac_mmap_min_addr` is its default 4096 (under qemu-user, the
host's, and no host page this request maps through starts below it), and
no enforcing SELinux policy denies the caller `memprotect:mmap_zero` below
`CONFIG_LSM_MMAP_MIN_ADDR`
(`bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`).
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_touching_from_below_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 61440 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 61440 [] [(61440, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(61440, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- …and so does the range touching from above.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_touching_from_above_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 69632 [] [(69632, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(69632, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- A PROT_NONE mapping is a VMA like any other, so it refuses the request:
-EEXIST on the middle of three inaccessible pages, for the rw spelling
that MAP_FIXED would have committed there.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_noaccess_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 3 1048610 mmap_fd_none 0 i noaccess_three_pages o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) noaccess_three_pages []) := by
  sys_norm

/-- The refusal is charged nothing: over a live page on a spent budget the
answer is still -EEXIST beside the -ENOMEM, where the free range on the
same budget is -ENOMEM alone (`noreplace_over_budget_is_enomem` above).
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_over_live_on_a_spent_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 3 1048610 mmap_fd_none 0 i spent_budget_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) spent_budget_model []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) spent_budget_model []) := by
  sys_norm

/-- A PROT_NONE reservation is free of charge under the bit as without it:
`accountable_mapping` wants `VM_WRITE`, so the spent budget still grants.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noreplace_noaccess_on_a_spent_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 0 1048610 mmap_fd_none 0 i spent_budget_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) spent_budget_model []
       ∨ o = Ok (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [(0x40000000, 4096)]
                          0 0 4096 0 demo_sp)) []) := by
  sys_norm

/-- The PROT_NONE grant makes its range unreadable, so a success reported
as a zero-fill in place of the unmap is refused.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_noaccess_grant_as_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 0 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)]) m' evs) := by
  sys_refute

/-- `do_mmap` rounds the length up to a page before anything is placed
(`len = PAGE_ALIGN(len)`, mm/mmap.c:368, Linux v6.18.46); only its zero
test at :347-348 reads the length unrounded, and it answers -EINVAL first.
So a 4097-byte request grants and zero-fills two pages.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_rounded_len_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4097 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 0x40000000 [] [(0x40000000, 8192)])
              (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 8192), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- …so a zero-fill of the unrounded 4097 bytes is refused.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_unrounded_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4097 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 4097)]) m' evs) := by
  sys_refute

/-- The grant-top bound is inclusive under the bit as under MAP_FIXED
(`fixed_rw_ending_at_alloc_top_iff` above): a request ending exactly at
`alloc_top` grants.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_ending_at_alloc_top_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 3 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096), (65536, 4096)] []
                          0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- …and so is the PROT_NONE spelling's, which reserves the last page
(`fixed_noaccess_ending_at_alloc_top_iff` above).
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_ending_at_alloc_top_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 0 1048610 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] []
                  [(Z_to_bv 64 (demo_top - 4096), 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096), (65536, 4096)]
                          [(Z_to_bv 64 (demo_top - 4096), 4096)] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- MAP_FIXED | MAP_FIXED_NOREPLACE on the PROT_NONE spelling is refused
over the live page as well, where MAP_FIXED alone reserves over it.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_with_fixed_noaccess_over_live_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 0 1048626 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) one_map_model []) := by
  sys_norm

/-! ### Operands the spec and the checker share

The `vm_reserved` half of the PROT_NONE shape's `region_free`, the exact
`prot` the rw shape matches and the flag bits `mmap_flags_core` keeps are
read by `mmap_spec` and `check_mmap` through the same definitions, so an
edit to one of them moves both sides at once and every proof between them
still closes.  Only a pin naming a concrete answer sees such an edit; each
pin below names one. -/

/-- The PROT_NONE spelling reads the image's LOAD reservation as the rw
spelling does (`noreplace_over_the_image_iff` above): over `vm_reserved`
alone, with no live page in the range, the answer is -EEXIST.
Premise: `dac_mmap_min_addr` is its default 4096 (under qemu-user, the
host's, and no host page this request maps through starts below it), and
no enforcing SELinux policy denies the caller `memprotect:mmap_zero` below
`CONFIG_LSM_MMAP_MIN_ADDR`
(`bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`).
no-row: stated over a hand-built ledger at fixture addresses; the row over a probe's own image is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_noaccess_over_the_image_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 4096 4096 0 1048610 mmap_fd_none 0 i image_at_4096 o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) image_at_4096 []
       ∨ o = Ok (mkEffect (errno_ret EEXIST) [] []) image_at_4096 []) := by
  sys_norm

/-- …so the reservation a ledger reading `vm_maps` alone would make over
the image is refused.
no-row: stated over a hand-built ledger at fixture addresses; the row over a probe's own image is owed (the A18 header of `Checks/Cases/Checks/Sys/Mm/Mmap.lean` names it).
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_noaccess_over_the_image_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 4096 4096 0 1048610 mmap_fd_none 0 i image_at_4096
        (Ok (SyscallEffect.mkEffectU 4096 [] [] [(4096, 4096)] [] []) m' evs) := by
  sys_refute

/-- The rw shape is PROT_READ|PROT_WRITE exactly.  A PROT_READ mapping is
VM_READ alone (`calc_vm_prot_bits`, include/linux/mman.h:141-147, Linux
v6.18.46), so a store to it faults, and the model's only rw answer is a
writable zero-fill: PROT_READ under the bit declines…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_read_only_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 1 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …with MAP_FIXED beside the bit too…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_with_fixed_read_only_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 1 1048626 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the writable grant is refused for it…
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_read_only_grant_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 1 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)]) m' evs) := by
  sys_refute

/-- …and PROT_WRITE alone declines…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_write_only_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 2 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …as does each prot holding PROT_EXEC short of all three bits
(`noreplace_exec_prot_is_unmodeled` above is 7): PROT_EXEC alone…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_exec_only_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 4 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …PROT_READ|PROT_EXEC…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_read_exec_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 5 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and PROT_WRITE|PROT_EXEC.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_write_exec_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 6 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- Both shapes compare the WHOLE prot word, so a bit outside the three
declines too.  For bits 4 to 31 declining is one sound choice: Linux
grants and qemu-user refuses, and an arm could allow both; the decline
costs coverage alone, as for PROT_SEM and bits 32 to 63 below.  Linux reads
nothing of the word but PROT_READ, PROT_WRITE and PROT_EXEC
(`calc_vm_prot_bits`, include/linux/mman.h:140-147, Linux v6.18.46,
riscv64 taking :91-92's 0 for `arch_calc_vm_prot_bits`) and the two tests
at mm/mmap.c:356 and :390, so it treats 0x13 as the rw shape and grants
it; qemu-user's `validate_prot_to_pageflags` refuses any bit outside those
three and PROT_SEM (linux-user/mmap.c:121-151, QEMU 11.1.1), and
`target_mmap` answers that -EINVAL (:977-981) before it reads the
address.  PROT_SEM (0x8), which qemu-user accepts and drops (:123-124, and
`target_to_host_prot` at :163-167), and bits 32 to 63, which it never
sees since it takes `prot` as an `int` (QEMU 11.1.1,
linux-user/syscall.c:6137-6138 and linux-user/mmap.c:964), grant on both.
No answer to this request, 0x13 at an aligned address, is both
implementations', so it declines…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_high_prot_bit_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 19 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the grant Linux gives it, which qemu-user never does, is refused…
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_high_prot_bit_grant_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 19 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)]) m' evs) := by
  sys_refute

/-- …as does bit 31, which the `int` qemu-user reads the word into still
carries (`do_mmap`, linux-user/syscall.c:6137-6138, QEMU 11.1.1)…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_prot_bit_31_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 2147483651 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …and the same bit beside PROT_NONE, which Linux maps inaccessible.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_noaccess_high_prot_bit_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 16 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- PROT_SEM beside rw declines as well, though both implementations grant
it: Linux reads the three bits alone (`calc_vm_prot_bits`,
include/linux/mman.h:140-147, Linux v6.18.46), and qemu-user accepts
PROT_SEM and drops it
(linux-user/mmap.c:123-124 and :163-167, QEMU 11.1.1).  So the decline
costs coverage and nothing else…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_prot_sem_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 11 1048610 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and -EINVAL, which neither gives it, is refused…
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_prot_sem_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 11 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …as bit 32 beside rw, which both grant too, declines: Linux reads the
three bits alone, and qemu-user never sees bit 32, taking `prot` as an
`int` (`do_mmap`, linux-user/syscall.c:6137-6138, QEMU 11.1.1)…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_prot_bit_32_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 4294967299 1048610 mmap_fd_none 0 i one_map_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …with no -EINVAL admitted there either.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem noreplace_prot_bit_32_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0x40000000 4096 4294967299 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- MAP_LOCKED beside the bit declines on a free range.  `do_mmap` makes it
VM_LOCKED (`calc_vm_flag_bits`, include/linux/mman.h:153-162, Linux
v6.18.46), then answers -EPERM without `can_do_mlock()` (mm/mmap.c:415-417)
or -EAGAIN past `mlock_future_ok` (:419-420), the answers of an mlock limit
the model does not carry, and populates whatever it grants…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_flag_bits@v6.18.46 -/
theorem noreplace_locked_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1056802 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and over a live page, where Linux's -EEXIST (mm/mmap.c:410-413, Linux
v6.18.46) comes before both: a coverage cost there, not a wrong answer…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_flag_bits@v6.18.46 -/
theorem noreplace_locked_over_live_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 3 1056802 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …for the PROT_NONE spelling on a free range…
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_flag_bits@v6.18.46 -/
theorem noreplace_noaccess_locked_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 0 1056802 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and over a live page.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_flag_bits@v6.18.46 -/
theorem noreplace_noaccess_locked_over_live_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 0 1056802 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- MAP_GROWSDOWN beside the bit declines.  It becomes VM_GROWSDOWN
(include/linux/mman.h:155, Linux v6.18.46), so a fault just below the
mapping grows it instead of failing (`lock_mm_and_find_vma`,
mm/mmap_lock.c:424-477, Linux v6.18.46), and `stack_guard_start_gap`
(include/linux/mm.h:3704-3714, Linux v6.18.46) keeps later placements a
guard gap below it.  The ledger holds neither.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_flag_bits@v6.18.46 -/
theorem noreplace_growsdown_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1048866 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- MAP_STACK beside the bit declines as well.  It becomes VM_NOHUGEPAGE
under `CONFIG_TRANSPARENT_HUGEPAGE` (include/linux/mman.h:159, Linux
v6.18.46), which changes no answer the model gives, so this decline is
coverage the shape gives up rather than a refusal Linux forces.  The pin
holds `mmap_flags_core` to keeping the bit until the shape is widened on
purpose.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_flag_bits@v6.18.46 -/
theorem noreplace_stack_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 1179682 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- MAP_FIXED | MAP_FIXED_NOREPLACE | MAP_NORESERVE (1065010) is the
MAP_NORESERVE spelling with MAP_FIXED beside it: granted on the spent
budget and recorded as lazily backed, as `noreplace_noreserve_ignores_budget`
is.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noreplace_with_fixed_noreserve_ignores_budget (i : SyscallInput) :
    mmap_spec 0x40000000 4096 3 1065010 mmap_fd_none 0 i spent_budget_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (with_vm_backing [(0x40000000, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] []
                        0 0 4096 0 demo_sp))) []) := by
  sys_norm

/-- PROT_NONE | MAP_NORESERVE under the bit reserves the range and records
it as lazily backed, as `noaccess_noreserve_grant_records_lazy` does
without the bit.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noreplace_noaccess_noreserve_records_lazy (i : SyscallInput) :
    mmap_spec 0x40000000 4096 0 1064994 mmap_fd_none 0 i one_map_model
      (Ok (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [])
          (with_vm_backing [(0x40000000, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [(0x40000000, 4096)]
                        0 0 demo_limit 0 demo_sp))) []) := by
  sys_norm

/-! ### A recorded wrong answer: the vvar the ledger does not hold -/

/-- inherited-divergence: bugs/mmap-placement-admits-unreachable-addresses.md --
the ledger carries no entry for the vvar/vdso pair the kernel installs at
exec, and on the top-down layout the page directly above a program's first
NULL-hint grant is the vvar's first page
(bugs/mmap-fixed-and-munmap-over-the-vdso-pair-assert-success.md reads
that placement).  Take `one_map_model`'s live page for that grant: growing
it in place with the bit is -EEXIST on Linux, `find_vma_intersection`
meeting the vvar VMA (mm/mmap.c:410-413, Linux v6.18.46), and the model,
whose ledger calls the page free, refuses it.  This pin states that wrong
answer over a literal ledger whose `vm_reserved` is empty, so no fix flips
it: once the pair enters the ledger a run starts with, the fix restates this
pin and its PROT_NONE twin over a ledger carrying the pair, where -EEXIST is
admitted.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_grow_in_place_onto_the_vvar_eexist_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 69632 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EEXIST) [] []) m' evs) := by
  sys_refute

/-- inherited-divergence: bugs/mmap-placement-admits-unreachable-addresses.md --
the same wrong answer for the PROT_NONE spelling.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem noreplace_noaccess_grow_in_place_onto_the_vvar_eexist_rejected (i : SyscallInput)
    (m' : Model) (evs : List event) :
    ¬ mmap_spec 69632 4096 0 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EEXIST) [] []) m' evs) := by
  sys_refute

/-! ### A recorded wrong answer: qemu-user's -EPERM at the host's floor -/

/-- Recorded in
bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md, an
entry no Rocq file cites, so it is named here in prose and not on an
`inherited-divergence:` line, which BUGS-1 of `check_lean_spec_parity.py`
takes only for an entry the Rocq twin cites.
qemu-user run without `-R` on a 16 or 64 KiB host maps a request through
the host page it starts in, and with `guest_base` 0 a request at 4096
starts in host page 0: `mmap_h_gt_g` rounds the start down to it
(linux-user/mmap.c:839, QEMU 11.1.1), and `mmap_frag`, finding no other
valid guest page there, calls the host's `mmap` at address 0 with the
bit kept and hands back its errno (:361 and :372-387, QEMU 11.1.1).  The
host's `cap_mmap_addr` answers a caller without `CAP_SYS_RAWIO` -EPERM
there at the default floor (security/commoncap.c:1459-1471, Linux
v6.18.46).  The arm's gate reads the default floor alone, so the model
refuses that -EPERM; that entry's fix restates this pin where -EPERM is
admitted.  The checker's twin is
`mmap_noreplace_first_host_page_eperm_rejected` in
`Checks/Cases/Checks/Sys/Mm/Mmap.lean`.
no-row: stated over a hand-built ledger at fixture addresses, and no recorded run makes this call.
kernel: security/commoncap.c:cap_mmap_addr; mm/mmap.c:do_mmap@v6.18.46 -/
theorem noreplace_first_host_page_eperm_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 4096 4096 3 1048610 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

end A18

/-! ## More of the gate order, at the boundaries -/

/-- MAP_FIXED at address 0 with a wrapping length: the overflow gate
(mm/mmap.c:368-370) runs before any address is read, so -ENOMEM wins over
the address-0 decline. 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_at_zero_wrapping_len_is_enomem (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 (Z_to_bv 64 (-1)) 3 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- Linux rejects a wrapped page rounding before it reads the address.
no-row: no recorded run makes this call.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem fixed_noaccess_at_zero_wrapping_len_is_enomem (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec 0 (Z_to_bv 64 (-1)) 0 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_ending_at_two_pow_64_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 3 50 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/--
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_ending_at_two_pow_64_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 0 50 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The grant-top bound is inclusive for MAP_FIXED as for the hint-placed
grant: a request ending exactly at `alloc_top` takes the two ordinary
resolutions.  Linux has no bound there — `addr > TASK_SIZE - len` (:857) is
the only one — so the band above is the MODEL's
(`bugs/grants-into-the-stack-band.md`), and the pin below says the arm
declines rather than answers once the request STARTS in it.
kernel: mm/mmap.c:__get_unmapped_area; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_ending_at_alloc_top_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 3 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096), (65536, 4096)] []
                          0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The PROT_NONE spelling.
kernel: mm/mmap.c:__get_unmapped_area; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_noaccess_ending_at_alloc_top_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 0 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] []
                  [(Z_to_bv 64 (demo_top - 4096), 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096), (65536, 4096)]
                          [(Z_to_bv 64 (demo_top - 4096), 4096)] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- One page higher the request starts AT `alloc_top`: declined, both prots.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_starting_at_alloc_top_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 demo_top) 4096 3 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_starting_at_alloc_top_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 demo_top) 4096 0 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and one page lower it is below `2^64` yet above the grant top, where
:857 may still fire against a `TASK_SIZE` this arm does not consult: the
model declines rather than pick -ENOMEM or -EINVAL. 
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_just_below_two_pow_64_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 3 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- an
unaligned MAP_FIXED address OVER a live range is -EINVAL and nothing else:
`offset_in_page(addr)` (:859-860) precedes any ledger read, so no
destructive resolution exists here.  Both prots.  As for
`fixed_unaligned_is_einval`, the map-count -ENOMEM of mm/mmap.c:377 that
Linux tests first is refused (`fixed_unaligned_over_live_enomem_rejected`). 
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_unaligned_over_live_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65537 4096 3 50 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- the rw
spelling over a live page: the -ENOMEM of a guest at its map-count ceiling
(mm/mmap.c:377-378 before :859-860, Linux v6.18.46) refused for the same
reason as `fixed_unaligned_enomem_rejected`.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_unaligned_over_live_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65537 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- the
PROT_NONE spelling, one errno short of Linux in the same way.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_unaligned_over_live_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65537 4096 0 50 mmap_fd_none 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- inherited-divergence: bugs/vm-limit-environment-obligation.md -- …and
over the IMAGE too: alignment precedes the reservation gate, so this is
-EINVAL where the aligned request one byte lower declines; and, as above,
-EINVAL alone where Linux tests the map count first. 
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_unaligned_over_image_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 4097 4096 3 50 mmap_fd_none 0 i image_at_4096 o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) image_at_4096 [] := by
  sys_norm

/-- The length gate beats the address-0 decline and the MAP_SHARED decline:
`do_mmap`'s `!len` (mm/mmap.c:347-348) precedes `security_mmap_addr`
and the `MAP_TYPE` validation (:539-540). 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem zero_len_fixed_at_zero_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 0 0 50 mmap_fd_none 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and the MAP_SHARED spelling.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem zero_len_shared_anonymous_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec 0 0 3 33 mmap_fd_none 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-! ## Hints, rounding and abutment on the fresh grant -/

/-- An UNALIGNED hint without MAP_FIXED is still an ordinary grant.  For
hint 1 the deciding step is in `do_mmap` (mm/mmap.c:364-365, Linux
v6.18.46), which calls `round_hint_to_min` (mm/mmap.c:219-226): its
`hint &= PAGE_MASK` makes the hint 0, so this is a NULL-hint call and
`generic_get_unmapped_area`'s `if (addr)` (:703; the top-down search's twin
is :754) is never entered — and since `round_hint_to_min` hands back a
page-aligned value for every non-MAP_FIXED hint, the masked hint or
`PAGE_ALIGN(mmap_min_addr)` when the masked hint is nonzero and below it
(:222-224), the `PAGE_ALIGN` there (:704, :755) receives an aligned address
on this path and changes nothing.
Only a MAP_FIXED `addr` reaches `__get_unmapped_area`'s `offset_in_page`
test (:859).  So is a hint above the grant top.
kernel: mm/mmap.c:do_mmap,round_hint_to_min,generic_get_unmapped_area,__get_unmapped_area@v6.18.46 -/
theorem rw_grant_unaligned_hint_is_only_a_hint (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 1 4096 3 34 mmap_fd_none 0 i one_map_model o ↔
      mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model o := by
  sys_norm

/-- A hint above the grant top is still only a hint — this one because
`mmap_end - len >= addr` fails for it (mm/mmap.c:757-758, Linux v6.18.46)
and the search runs instead (the legacy search's twin test is :706-708).  A
hint whose request ENDS in `(alloc_top, TASK_SIZE]` and meets no VMA the
pinned kernel HONOURS, and the arm's `alloc_top` conjunct refuses:
`bugs/grants-into-the-stack-band.md`.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,__get_unmapped_area@v6.18.46 -/
theorem rw_grant_high_hint_is_only_a_hint (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 3 34 mmap_fd_none 0 i one_map_model o ↔
      mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model o := by
  sys_norm

/-- The environment's -ENOMEM leaves NOTHING behind: no zero-fill rides on
it. 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_enomem_with_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] [(0x40000000, 4096)]) m' evs) := by
  sys_refute

/-- `len = 4097` rounds to two pages in the EFFECT and the LEDGER, not only
in the budget: the grant zero-fills 8192 bytes and records 8192. 
kernel: mm/mmap.c:do_mmap,__get_unmapped_area,generic_get_unmapped_area,generic_get_unmapped_area_topdown; mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_len4097_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4097 3 34 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ ∃ a : word,
           o = Ok (mkEffect a [] [(a, 8192)])
                  (fixture (VmMaps.mkVmMapsFull [] [(a, 8192), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []
           ∧ bv_unsigned a % page_size = 0 ∧ 0 < bv_unsigned a
           ∧ bv_unsigned a + 8192 ≤ demo_top
           ∧ (bv_unsigned a + 8192 ≤ 65536 ∨ 69632 ≤ bv_unsigned a)) := by
  sys_norm

/-- The rounded grant at 0x40000000.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_len4097_zero_fills_two_pages (i : SyscallInput) :
    mmap_spec 0 4097 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 8192)])
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 8192), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- A zero-fill of the unrounded 4097 bytes is refused.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_len4097_unrounded_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4097 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 4097)]) m' evs) := by
  sys_refute

/-- The one-page twin of `rw_grant_len4097_iff`, where the rounding of a
SUB-page length is visible: `do_mmap` rounds before anything is placed
(`len = PAGE_ALIGN(len)`, mm/mmap.c, Linux v6.18.46), so `len = 1` is a
whole page in the effect, in the ledger and in the placement bound, and
nothing else is admitted.  `rw_grant_len1_charges_a_page` above cannot say
this — under a budget with nothing left, every positive rounding of 1 is
refused alike, so that pin fixes only that the charge is positive.  Here
the budget has room.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_len1_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 1 3 34 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ ∃ a : word,
           o = Ok (mkEffect a [] [(a, 4096)])
                  (fixture (VmMaps.mkVmMapsFull [] [(a, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []
           ∧ bv_unsigned a % page_size = 0 ∧ 0 < bv_unsigned a
           ∧ bv_unsigned a + 4096 ≤ demo_top
           ∧ (bv_unsigned a + 4096 ≤ 65536 ∨ 69632 ≤ bv_unsigned a)) := by
  sys_norm

/-- The rounded grant at 0x40000000: zero-filled and recorded as 4096.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_len1_zero_fills_a_page (i : SyscallInput) :
    mmap_spec 0 1 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- A zero-fill of the single byte asked for is refused…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_len1_unrounded_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 1 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 1)]) m' evs) := by
  sys_refute

/-- …and so is a second page: a rounding of 1 to 8192 is the lie a budget
with nothing left could not tell from the right one.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem rw_grant_len1_two_pages_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 1 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 8192)]) m' evs) := by
  sys_refute

/-- Disjointness is strict on both ends: a grant may end exactly where the
live page begins, or begin exactly where it ends. 
kernel: mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_abutting_below_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect 61440 [] [(61440, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(61440, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- …and begin exactly where the live page ends.
kernel: mm/vma.c:unmapped_area,unmapped_area_topdown@v6.18.46 -/
theorem rw_grant_abutting_above_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i one_map_model
      (Ok (mkEffect 69632 [] [(69632, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(69632, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- PROT_NONE | MAP_NORESERVE: the same reservation, and the bit still
selects the lazy ledger — the post-model records the interior as lazy even
though a PROT_NONE range is never charged.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem noaccess_noreserve_grant_records_lazy (i : SyscallInput) :
    mmap_spec 0 4096 0 16418 mmap_fd_none 0 i one_map_model
      (Ok (SyscallEffect.mkEffectU 0x40000000 [] [] [(0x40000000, 4096)] [] [])
          (with_vm_backing [(0x40000000, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [(0x40000000, 4096)]
                        0 0 demo_limit 0 demo_sp))) []) := by
  sys_norm

/-! ## Lazy and materialized backing under a replacement

A replacement forgets every lazy or materialized entry in its range
(`vm_forget_range`) and then records the NEW call's backing: eager unless
THIS call says `MAP_NORESERVE` — `accountable_mapping` (mm/vma.c:2326-2336,
Linux v6.18.46) is decided by the flags of the call that installs the
mapping. -/

/-- A lazily reserved page, PROT_NONE, under a zero budget. -/
def lazy_reserved_model : Model :=
  with_vm_backing [(0x40000000, 4096)] []
    (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096)] [(0x40000000, 4096)] 0 0 0 0 demo_sp))

/-- Committing it WITHOUT `MAP_NORESERVE` charges eagerly: the lazy entry
is forgotten, nothing lazy replaces it, and under a zero budget only the
two errno resolutions remain.
The destructive disjunct is the model's declared over-approximation (`three_pages_zero_budget`): on Linux the refused charge returns before the teardown.
kernel: mm/vma.c:accountable_mapping,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_commit_of_lazy_reservation_charges_eagerly (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 50 mmap_fd_none 0 i lazy_reserved_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) lazy_reserved_model []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(0x40000000, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 0 0 demo_sp)) []) := by
  sys_norm

/-- …while the `MAP_NORESERVE` spelling of the same commit stays lazy and
succeeds under that budget.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem fixed_rw_noreserve_commit_of_lazy_reservation_stays_lazy (i : SyscallInput) :
    mmap_spec 0x40000000 4096 3 16434 mmap_fd_none 0 i lazy_reserved_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (with_vm_backing [(0x40000000, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096)] [] 0 0 0 0 demo_sp))) []) := by
  sys_norm

/-- A materialized page under an exactly-spent budget. -/
def materialized_model : Model :=
  with_vm_backing [(65536, 4096)] [65536]
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 4096 0 demo_sp))

/-- An rw MAP_FIXED over a materialized lazy page forgets both its lazy
entry and its materialization, and charges the page eagerly instead —
exactly the budget the materialization was holding, so the success fits. 
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_over_materialized_page_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 3 50 mmap_fd_none 0 i materialized_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) materialized_model []
       ∨ o = Ok (mkEffect 65536 [] [(65536, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 4096 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 4096 0 demo_sp)) []) := by
  sys_norm

/-- Keeping the materialization would double-charge the page: a success
that leaves the model as it was is refused. 
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_rw_over_materialized_page_keeping_it_rejected (i : SyscallInput) :
    ¬ mmap_spec 65536 4096 3 50 mmap_fd_none 0 i materialized_model
        (Ok (mkEffect 65536 [] [(65536, 4096)]) materialized_model []) := by
  sys_refute

/-! ## More MAP_FIXED ledger shapes -/

/-- The rw replacement of the live page itself, on the demo budget: three
resolutions, and the two errnos are told apart by their ledgers. 
kernel: mm/vma.c:__mmap_prepare,__mmap_new_vma,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_contained_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 4096 3 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 65536 [] [(65536, 4096)]) one_map_model []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- Effect and ledger move TOGETHER on the errno arms: a destructive failure
that also exposes zeroes, an errno that unmaps yet leaves the ledger
intact, and a destructive -EINVAL are each refused. 
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_destructive_failure_with_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [(65536, 4096)] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- An errno that unmaps yet leaves the ledger intact.
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_errno_unmap_with_intact_ledger_rejected (i : SyscallInput) :
    ¬ mmap_spec 65536 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) one_map_model []) := by
  sys_refute

/-- A destructive -EINVAL: the alignment errno precedes every ledger read.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_destructive_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 65536 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- A PROT_NONE guard punched into the MIDDLE of a three-page reservation
keeps the owner WHOLE — the contained arm does not re-cut `vm_maps` — and
records the guard beside the split no-access remnants.
Linux itself splits the owner three ways (`__split_vma` from `vms_gather_munmap_vmas`); one owner entry with the guard recorded beside the no-access remnants is the ledger's representation of that, not a reading.
kernel: mm/vma.c:vms_gather_munmap_vmas@v6.18.46 -/
theorem fixed_noaccess_middle_page_keeps_owner_whole (i : SyscallInput) :
    mmap_spec 69632 4096 0 50 mmap_fd_none 0 i noaccess_three_pages
      (Ok (SyscallEffect.mkEffectU 69632 [] [] [(69632, 4096)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(69632, 4096), (65536, 4096), (73728, 4096)]
                      0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- Spanning over one whole entry plus free space: the entry is replaced by
the request, and the newly owned page is charged. 
kernel: mm/vma.c:vms_gather_munmap_vmas,__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_past_end_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 8192 3 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 65536 [] [(65536, 8192)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 demo_limit 0 demo_sp)) []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- …and under a spent budget that newly owned page cannot be charged:
the success disappears and the two errnos remain (mm/vma.c:2422-2429).
The destructive disjunct is the model's declared over-approximation (`three_pages_zero_budget`): on Linux the refused charge returns before the teardown.
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_past_end_over_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 65536 8192 3 50 mmap_fd_none 0 i spent_budget_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) spent_budget_model []
       ∨ o = Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] [])
              (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 4096 0 demo_sp)) []) := by
  sys_norm

/-- A free-range MAP_FIXED ABUTTING the live page is a grant, not a
replacement: two resolutions (nothing to tear down: `vms_abort_munmap_vmas`
returns at its first test, mm/vma.c:2354-2355), and the destructive one is
refused. 
kernel: mm/vma.c:__mmap_prepare,vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_abutting_free_range_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 69632 4096 3 50 mmap_fd_none 0 i one_map_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model []
       ∨ o = Ok (mkEffect 69632 [] [(69632, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(69632, 4096), (65536, 4096)] [] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The destructive resolution over a free range is refused.
kernel: mm/vma.c:vms_abort_munmap_vmas@v6.18.46 -/
theorem fixed_rw_abutting_destructive_failure_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 69632 4096 3 50 mmap_fd_none 0 i one_map_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] []) m' evs) := by
  sys_refute

/-- A free-range `MAP_FIXED | MAP_NORESERVE` grant ignores the budget and
records lazily; the plain spelling under the same zero budget is forced to
-ENOMEM.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem fixed_noreserve_fresh_ignores_budget (i : SyscallInput) :
    mmap_spec 0x40000000 4096 3 16434 mmap_fd_none 0 i zero_budget_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (with_vm_backing [(0x40000000, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096)] [] 0 0 0 0 demo_sp))) []) := by
  sys_norm

/-- The plain spelling under the same zero budget.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem fixed_fresh_under_zero_budget_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 50 mmap_fd_none 0 i zero_budget_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) zero_budget_model [] := by
  sys_norm

/-! ## Shapes that leave the modeled surface

Each of these is a real call Linux answers, and each is `Unmodeled` here
for a stated reason: the machine model has no read-only page and no
executable-permission ledger, no shared memory, and pins `off` to 0. -/

/-- `MAP_SHARED|MAP_ANONYMOUS` is shmem-backed on Linux (`do_mmap`'s `MAP_SHARED` arm): no shared memory here.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_new_vma@v6.18.46 -/
theorem shared_anonymous_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 33 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `PROT_EXEC`: the machine model has no executable-permission ledger.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem exec_prot_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 7 34 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `PROT_READ` alone: no readable-but-not-writable page.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem read_only_anonymous_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 1 34 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- Flag bits Linux IGNORES or honours must still fail closed rather than
become -EINVAL or a grant: `MAP_STACK | MAP_GROWSDOWN` (the pthread-stack
spelling) and `MAP_HUGETLB` with a real length.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem stack_growsdown_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 131362 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `MAP_HUGETLB` with a real length: `ksys_mmap_pgoff` sets the huge file up before `do_mmap`.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem hugetlb_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 262178 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `PROT_WRITE` alone is a real request Linux grants; the model's shapes
spell only rw and PROT_NONE, so it fails closed. 
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem write_only_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 2 34 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- A page-ALIGNED nonzero offset is an ordinary success on Linux for an
anonymous mapping (`__get_unmapped_area` zeroes the page offset,
mm/mmap.c:838-840, Linux v6.18.46) — and `Unmodeled` here: a narrowing,
declared. 
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem page_aligned_nonzero_offset_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 34 mmap_fd_none 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- The same offset on the other three shapes — PROT_NONE, and both MAP_FIXED
spellings — declines the same way: each shape's `w_is0 off` conjunct is
load-bearing, not only the rw grant's.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem noaccess_page_aligned_nonzero_offset_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 0 34 mmap_fd_none 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_page_aligned_nonzero_offset_is_unmodeled (i : SyscallInput)
    (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 0 50 mmap_fd_none 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_page_aligned_nonzero_offset_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 3 50 mmap_fd_none 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `MAP_SHARED|MAP_ANONYMOUS|MAP_FIXED` with PROT_NONE is shmem-backed on
Linux like its rw spelling, and declines like the hint-placed `MAP_SHARED`
shape (`shared_anonymous_is_unmodeled`): the MAP_FIXED PROT_NONE shape's
flags conjunct is load-bearing.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_new_vma@v6.18.46 -/
theorem fixed_shared_noaccess_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 0 49 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `PROT_READ` alone with MAP_FIXED: no readable-but-not-writable page at a
named address either — the MAP_FIXED rw shape's `prot` conjunct is
load-bearing.  What Linux would grant is a `VM_READ`-only VMA — `do_mmap`
(mm/mmap.c:400, Linux v6.18.46) folds `prot` through include/linux/mman.h's
`calc_vm_prot_bits` — a page kind the model does not carry.
kernel: mm/mmap.c:do_mmap; include/linux/mman.h:calc_vm_prot_bits@v6.18.46 -/
theorem fixed_read_only_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0x40000000 4096 1 50 mmap_fd_none 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## The grant top is read from the ledger

Rocq's `grant_at_demo_top_*` pins (`Checks/Cases/Mm/Mmap.v`, #550): the same
request on two models that differ ONLY in `vm_init_sp` asks for opposite
verdicts, which a constant bound could not give.  `demo_sp` is the bottom of
the SP window, so its top is `demo_top`; the high model's stack pointer is
256 MiB above it.  A grant AT `demo_top` is exactly the lie a run started at
`demo_sp` must refuse and a run started higher must allow.  No probe can
reach this (reason 3 of Rocq's `Checks/Examples.v`: the stack pointer is
model-internal state the harness seeds), so the claim lives here. -/

/-- The empty ledger under the low stack pointer is `Prelude`'s
`ceiling_room_model`, the fixture Rocq's ceiling pins run on; the one 256 MiB
higher is new. -/
def top_hi_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 (Z_to_bv 64 (sp_window_lo + 0x10000000)))

/-- Refused under the low stack pointer: `demo_top` is `alloc_top` there,
and the band above it is the top-down layout's `mmap_base` gap
(mm/util.c:mmap_base, Linux v6.18.46), read off `vm_init_sp` and not a constant.
kernel: mm/util.c:mmap_base@v6.18.46 -/
theorem rw_grant_at_demo_top_rejected_under_low_sp (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i ceiling_room_model
        (Ok (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) m' evs) := by
  sys_refute

/-- …and admitted, the same effect, once `vm_init_sp` is 256 MiB higher and
`demo_top` is an ordinary gap address.
kernel: mm/util.c:mmap_base@v6.18.46 -/
theorem rw_grant_at_demo_top_admitted_under_high_sp (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i top_hi_model
      (Ok (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)] [] 0 0 demo_limit 0
                      (Z_to_bv 64 (sp_window_lo + 0x10000000)))) []) := by
  sys_norm

/-- The PROT_NONE arm reads the same field.
kernel: mm/util.c:mmap_base@v6.18.46 -/
theorem noaccess_grant_at_demo_top_rejected_under_low_sp (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ mmap_spec 0 4096 0 34 mmap_fd_none 0 i ceiling_room_model
        (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 demo_top) [] [] [(Z_to_bv 64 demo_top, 4096)] [] [])
            m' evs) := by
  sys_refute

/-- The PROT_NONE twin of `rw_grant_at_demo_top_admitted_under_high_sp`.
kernel: mm/util.c:mmap_base@v6.18.46 -/
theorem noaccess_grant_at_demo_top_admitted_under_high_sp (i : SyscallInput) :
    mmap_spec 0 4096 0 34 mmap_fd_none 0 i top_hi_model
      (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 demo_top) [] [] [(Z_to_bv 64 demo_top, 4096)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)] [(Z_to_bv 64 demo_top, 4096)]
                      0 0 demo_limit 0 (Z_to_bv 64 (sp_window_lo + 0x10000000)))) []) := by
  sys_norm

/-! ## brk (214) and munmap (215): how their pins are read

Like the mmap half above, the brk and munmap halves close by `sys_norm`
and `sys_refute` (`Checks/Cases/Tactic.lean`).  Unlike it, they REGISTER:
the two specs and the post-state builders enter the `sys_simp` set here,
at the priority that file gives every unfolding (the gates `brk_r_ok`,
`brk_grow_ok`, `brk_budget_ok`, `brk_is_grow` and `munmap_free_ok` are
decided, never unfolded), and so do the resolution lemmas the next
paragraph describes.  Every model these halves state a pin on is a NAMED
closed definition, never an inline `fixture …`: the register unfolds
`fixture` in the first pass, and a resolution lemma stated on the unfolded
tree would never be tried.

`brk_spec` chooses its resolution under `brk_r_ok m req r = true`, a
predicate on the symbolic resolution that no closed-gate decision removes.
So for each fixture and request a pin uses, the allowed resolution set is
read off ONCE, as a lemma `brk_r_ok m req r = true ↔ (r = a ∨ r = b)`:
`brk_r_ok_resolutions` says every allowed `r` is the request or the
tracked break, and `decide` settles each of those two candidates.
Registered in `sys_simp`, the lemma turns the `choose` into the
disjunction the `iff` states — the moved break first, the unchanged one
second, which is the order the pins spell.  The lemma is a reading
device; the kernel claim is the pin that uses it. -/

attribute [sys_simp low]
  brk_spec.eq_1 with_brk_next.eq_1 brk_model_next.eq_1 forget_vm_ranges.eq_1
  forget_vm_ranges.eq_2 munmap_spec.eq_1

/-- Every allowed resolution is the request or the tracked break: each of
`brk_r_ok`'s three arms tests `bv_eqb r req` or `bv_eqb r b` before
anything else.
The shape of `brk_r_ok`, read off once so that each resolution lemma below
needs only `decide` on two candidates; it is also what `SYSCALL_DEFINE1(brk)`
returns on every path, the request (mm/mmap.c:207, Linux v6.18.46) or
`origbrk` (:212).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_resolutions {m : Model} {req r : word} (h : brk_r_ok m req r = true) :
    r = req ∨ r = (m_vmmaps m).vm_brk := by
  simp only [brk_r_ok] at h
  split at h
  · exact Or.inr ((bv_eqb_eq _ _).mp h)
  · split at h
    · simp only [Bool.or_eq_true, bv_eqb_eq] at h
      exact h
    · simp only [Bool.and_eq_true, Bool.or_eq_true, bv_eqb_eq] at h
      exact h.1

/-! ## The brk fixtures

A concrete process, the Rocq file's: the image occupies `[4096, 8192)` and
the break base sits ASLR-plausibly at 0x10000 = 65536 (`vm_start_brk` =
`vm_brk` at execve), so `min_brk` = 65536 and the ASLR gap `[8192, 65536)`
between image and base is invalid territory, as on Linux.  The break base
is ASLR-placed, so a probe cannot name it in a literal expected return;
that is what puts the rejecting cases and the blocked-grow branch here
rather than in `testing/syscall-check/tests/brk_paths.c`. -/

/-- The image's one LOAD page. -/
def brk_reserved : List (word × word) := [(4096, 4096)]

/-- The process at execve: break established at 65536, nothing granted. -/
def m_est : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 demo_limit 0 demo_sp)

/-- A live page flush against the page a one-page grow would install:
the neighbour at 69632. -/
def m_neighbour_flush : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(69632, 4096)] [] 65536 65536 demo_limit 0 demo_sp)

/-- The same neighbour one page higher, at 73728. -/
def m_neighbour_gap : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(73728, 4096)] [] 65536 65536 demo_limit 0 demo_sp)

/-- A live page over the break itself, at 65536: what a `munmap` of the
heap followed by a `MAP_FIXED` there leaves. -/
def m_heap_covered : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4096)] [] 65536 65536 demo_limit 0 demo_sp)

/-- A grown process: break 0x20000 = 131072, the heap grant
`[65536, 131072)` recorded. -/
def m_grown : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 65536)] [] 65536 131072 demo_limit 0 demo_sp)

/-- A break eight bytes below the end of a guarded page: the heap grant
is `[65536, 69624)` and the whole page `[65536, 69632)` is inaccessible. -/
def m_brk_same_page : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4088)] [(65536, 4096)] 65536 69624 demo_limit 0 demo_sp)

/-- …shrunk four bytes: the grant truncated to `[65536, 69620)`, the guard
untouched. -/
def m_brk_same_page_shrunk : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4084)] [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)

/-- A one-page heap grant, wholly inaccessible, under a break at 69632. -/
def noaccess_brk_model : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(65536, 4096)] [(65536, 4096)] 65536 69632 demo_limit 0 demo_sp)

/-- A fresh process under a ONE-PAGE budget. -/
def m_tight_brk : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 4096 0 demo_sp)

/-- The brk input: `a0` is the request and nothing else is read
(`SYSCALL_DEFINE1(brk, unsigned long, brk)`, mm/mmap.c:115, Linux
v6.18.46).  Its consumer is `Checks/Cases/Run.lean`'s dispatch pins. -/
def brk_in (req : word) : SyscallInput :=
  SyscallInput.mkInput 214 [req, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-! ## brk: the query and the invalid request

`SYSCALL_DEFINE1(brk)` (mm/mmap.c:115-213, Linux v6.18.46) reads
`min_brk = mm->start_brk` (:130) and takes `if (brk < min_brk) goto out;`
(:140-141): `out:` restores `mm->brk = origbrk` and returns it (:209-212).
`brk(0)` is that path — 0 is always below the heap — and is how libc
queries the break (`sbrk(0)`). -/

/-- `brk(0)` on `m_est`: the one allowed resolution is the break itself.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_zero_returns_current_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_query (r : word) : brk_r_ok m_est 0 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

/-- `brk(16384)`, inside the ASLR gap: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_in_aslr_gap_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_gap (r : word) : brk_r_ok m_est 16384 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

/-- `brk(65535)`, one byte under `min_brk`: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_one_below_min_brk_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_below (r : word) : brk_r_ok m_est 65535 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

/-- `brk(65536)`, the base itself: the request and the break coincide.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_at_min_brk_returns_it`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_at_min (r : word) : brk_r_ok m_est 65536 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · rfl
    · decide
  · subst h; decide

/-- `brk(0)` on the guarded heap: the break itself, 69632.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_query_preserves_noaccess`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_noaccess_query (r : word) : brk_r_ok noaccess_brk_model 0 r = true ↔ r = 69632 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

attribute [sys_simp] brk_r_ok_est_query brk_r_ok_est_gap brk_r_ok_est_below brk_r_ok_est_at_min
  brk_r_ok_noaccess_query

/-- `brk(0)` on an ESTABLISHED break returns the CURRENT break UNCHANGED,
with no state change, no zeroes and no unmap — Linux's `brk < min_brk`
path (mm/mmap.c:140-141, Linux v6.18.46), which returns `origbrk`
(:209-212) — and no other value: the `iff` refuses every other return, an
errno, and a decline.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_zero_returns_current_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 0 i m_est o ↔ o = Ok (mkEffect 65536 [] []) m_est [] := by
  sys_norm

/-- A zero request makes `brk_is_grow` false even with a positive old break
below the proposed resolution: the request conjunct decides this helper
input. No run reaches this input through `brk_spec`, since `brk_r_ok`
resolves a query to `r = old`; Linux's query path returns `origbrk`
(mm/mmap.c:140-141, :209-212, Linux v6.18.46). The pin fixes the helper,
not a reachable kernel answer.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_is_grow_query_with_larger_resolution_is_false :
    brk_is_grow 0 69632 65536 = false := by decide

/-- …and does NOT return an arbitrary value: the old model accepted every
value below `2^64` here.  Linux's query path returns `origbrk` and nothing
else (mm/mmap.c:140-141, :209-212, Linux v6.18.46); no recorded case
mutates a query's return, so the kernel reading is the evidence.
kernel: mm/mmap.c:brk@v6.18.46
rocq-twin: brk_zero_rejects_arbitrary -/
theorem brk_zero_rejects_arbitrary (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 0 i m_est (Ok (mkEffect 123456 [] []) m' evs) := by
  sys_refute

/-- `brk` never answers `-errno`: every failure path is `goto out`, which
returns `origbrk` (mm/mmap.c:209-212, Linux v6.18.46), and the one errno
in the function, `mmap_write_lock_killable`'s -EINTR (:125-126), reaches
only a task a fatal signal is already killing.  A kernel reporting -ENOMEM
for the query is lying.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_zero_errno_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 0 i m_est (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- A request in the ASLR GAP between the image top (8192) and the base
(65536) is invalid — Linux's `min_brk` is `mm->start_brk`, the base itself
(mm/mmap.c:130, Linux v6.18.46), NOT the image top — so it returns the
break unchanged (:140-141) and cannot move it.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_in_aslr_gap_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 16384 i m_est o ↔ o = Ok (mkEffect 65536 [] []) m_est [] := by
  sys_norm

/-- …and a kernel that moved the break down into the gap is refused: below
`min_brk` the function has already left (mm/mmap.c:140-141, Linux v6.18.46).
Valid for this fixture's randomised base; on a `CONFIG_COMPAT_BRK` kernel
with randomisation off the floor is lower
(bugs/brk-min-brk-assumes-a-randomised-break.md).
kernel: mm/mmap.c:brk@v6.18.46
rocq-twin: brk_in_aslr_gap_rejects_moving -/
theorem brk_in_aslr_gap_rejects_moving (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 16384 i m_est (Ok (mkEffect 16384 [] []) m' evs) := by
  sys_refute

/-- The floor is strict at the byte: `brk < min_brk` (mm/mmap.c:140,
Linux v6.18.46), so one byte under the base is still invalid and answers
the unchanged break, never a shrink.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_one_below_min_brk_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 65535 i m_est o ↔ o = Ok (mkEffect 65536 [] []) m_est [] := by
  sys_norm

/-- …and the base itself is legal: `65536 < 65536` is false, both breaks
round to the same page and `mm->brk = brk; goto success` returns the
request (mm/mmap.c:155-158, :207, Linux v6.18.46), which is the unchanged
break here.  A model with `≤` at the floor would answer the same value
through the other path; `brk_shrink_unmaps_freed_tail` below, whose
request is the base on a grown heap, is where the two differ.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_at_min_brk_returns_it (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 65536 i m_est o ↔ o = Ok (mkEffect 65536 [] []) m_est [] := by
  sys_norm

/-- A query leaves the no-access ledger alone: `brk_model_next`'s
subtraction is gated on a strict shrink, and a query is not one.  The
break base is ASLR-placed, so a probe cannot name the model state a query
has to preserve.  Linux's query path touches no VMA (mm/mmap.c:140-141,
:209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_query_preserves_noaccess (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 0 i noaccess_brk_model o ↔ o = Ok (mkEffect 69632 [] []) noaccess_brk_model [] := by
  sys_norm

/-- A live two-page mapping `[61440, 69632)` STRADDLING the break at 65536:
what a `munmap` of the heap followed by a wider `MAP_FIXED` leaves. -/
def m_straddled : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(61440, 8192)] [] 65536 65536 demo_limit 0 demo_sp)

/-- `brk(0)` over the straddling mapping: the break itself.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_query_leaves_a_straddling_mapping_whole`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_straddled_query (r : word) : brk_r_ok m_straddled 0 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

attribute [sys_simp] brk_r_ok_straddled_query

/-- …and it leaves the ledger untouched, the straddling entry WHOLE: the
query path reads no VMA and cuts nothing (mm/mmap.c:140-141, :209-212,
Linux v6.18.46).  A ledger that re-cut the entry at the break would split
one allocation into two and narrow `map_has` on the next `munmap`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_query_leaves_a_straddling_mapping_whole (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 0 i m_straddled o ↔ o = Ok (mkEffect 65536 [] []) m_straddled [] := by
  sys_norm

/-! ## brk: the grow

Past the floor and the `check_data_rlimit` call at mm/mmap.c:149-151
(`check_data_rlimit` is include/linux/mm.h:3570-3582, Linux v6.18.46),
`SYSCALL_DEFINE1(brk)` rounds both breaks (:153-154), takes
the `oldbrk == newbrk` exit when they agree (:155-158), and on a grow runs
`check_brk_limits` (:180-181), the one-free-page test (:187-190) and
`do_brk_flags` (:194-195), each refusal a `goto out` answering the old
break; success records the byte request (:197) and returns it (:207).  So
a grow has TWO resolutions, the grant and the old break, and both are
pinned as the allowed set. -/

/-- `brk(131072)` on `m_est`: the grant, or the unchanged break.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_iff`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_grow (r : word) :
    brk_r_ok m_est 131072 r = true ↔ (r = 131072 ∨ r = 65536) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(69640)` on `m_est`, an unaligned request: the grant, or the
unchanged break.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_unaligned_grow_records_bytes_and_installs_pages`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_grow_unaligned (r : word) :
    brk_r_ok m_est 69640 r = true ↔ (r = 69640 ∨ r = 65536) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(69632)` with the neighbour flush at 69632: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_flush_against_neighbour_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_flush (r : word) : brk_r_ok m_neighbour_flush 69632 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

/-- `brk(69632)` with the neighbour at 73728: the grant, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_one_page_below_neighbour_grants`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_gap (r : word) :
    brk_r_ok m_neighbour_gap 69632 r = true ↔ (r = 69632 ∨ r = 65536) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(69632)` with a live page over the break: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_into_live_page_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_covered (r : word) : brk_r_ok m_heap_covered 69632 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

/-- `brk(2^64 - 1)` on `m_est`: unchanged only — the rounded top, `2^64`,
is past `alloc_top`.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_request_near_two_pow_64_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_near_max (r : word) :
    brk_r_ok m_est (Z_to_bv 64 (two_pow_64 - 1)) r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

attribute [sys_simp] brk_r_ok_est_grow brk_r_ok_est_grow_unaligned brk_r_ok_flush brk_r_ok_gap
  brk_r_ok_covered brk_r_ok_est_near_max

/-- THE GROW, both resolutions and nothing else.  Either the kernel installs
`[65536, 131072)` — `do_brk_flags` maps `[oldbrk, newbrk)` anonymous and
zero-filled (mm/mmap.c:194-195, Linux v6.18.46; mm/vma.c:2805), the byte
request becomes the break (:197) and is returned (:207), and the ledger
records the grant — or it refuses and answers the old break (:209-212).
The `iff` refuses a grant without its zeroes, a partial zero-fill, an
errno and a decline.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_grow_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 131072 i m_est o ↔
      (o = Ok (mkEffect 131072 [] [(65536, 65536)])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 65536)] [] 65536 131072 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 65536 [] []) m_est []) := by
  sys_norm

/-- A blocked GROW may always take the failure branch: the break is
unchanged and no memory is granted (`goto out`, mm/mmap.c:209-212, Linux
v6.18.46).  Under default limits Linux grants here, so no recorded trace
exhibits this branch; it is allowed because a real grow can be blocked —
`do_brk_flags`'s -ENOMEM (mm/vma.c:2816-2823), a finite `RLIMIT_DATA`
(:149-151), `mlockall(MCL_FUTURE)`'s -EAGAIN (:111-112) — and musl then
falls back to mmap.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46
rocq-twin: brk_grow_may_fail -/
theorem brk_grow_may_fail (i : SyscallInput) :
    brk_spec 131072 i m_est (Ok (mkEffect 65536 [] []) m_est []) := by
  sys_norm

/-- A grant that does not expose its pages as zeroes is refused: the
installed pages are anonymous memory that reads back zero.
probe: testing/syscall-check/tests/brk_paths.c#reject --mutate brk#5:drop-zeros -/
theorem brk_grow_without_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 131072 i m_est (Ok (mkEffect 131072 [] []) m' evs) := by
  sys_refute

/-- …and a grant zeroing only part of the installed range is refused too:
`do_brk_flags` is handed the whole of `[oldbrk, newbrk)` (mm/mmap.c:194-195,
Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_partial_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 131072 i m_est (Ok (mkEffect 131072 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- A blocked grow answers the old break, never -ENOMEM: `do_brk_flags`'s
-ENOMEM (mm/vma.c:2816-2823, Linux v6.18.46) is turned into `goto out` by
the caller (mm/mmap.c:194-195), which returns `origbrk` (:209-212).
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_grow_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 131072 i m_est (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- The grow never declines: both of its resolutions are Linux's.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_never_unmodeled (i : SyscallInput) :
    ¬ brk_spec 131072 i m_est Unmodeled := by
  sys_refute

/-- An UNALIGNED grow records the byte request and installs whole pages:
`mm->brk = brk` keeps 69640 (mm/mmap.c:197, Linux v6.18.46) while
`do_brk_flags` maps `[PAGE_ALIGN(65536), PAGE_ALIGN(69640))` =
`[65536, 73728)` (:153-154, :194-195).  So the ledger owns the 4104
requested bytes, the zero-fill covers two pages, and the budget is charged
by the byte (`brk_budget.c`'s `steps` case).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_unaligned_grow_records_bytes_and_installs_pages (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69640 i m_est o ↔
      (o = Ok (mkEffect 69640 [] [(65536, 8192)])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4104)] [] 65536 69640 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 65536 [] []) m_est []) := by
  sys_norm

/-- …and a zero-fill of the byte request alone, `[65536, 69640)`, is refused:
the pages are installed whole.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#8:drop-zeros,smuggle-zeros:a0+-16:16 -/
theorem brk_unaligned_grow_byte_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69640 i m_est (Ok (mkEffect 69640 [] [(65536, 4104)]) m' evs) := by
  sys_refute

/-- `brk(65537)` on `m_est`: the one-byte grant, or the unchanged break.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_one_byte_grow_installs_a_page`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_est_one_byte (r : word) :
    brk_r_ok m_est 65537 r = true ↔ (r = 65537 ∨ r = 65536) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_est_one_byte

/-- A grow of ONE BYTE past an aligned break installs a whole page:
`PAGE_ALIGN(65537)` is 69632 (mm/mmap.c:153-154, Linux v6.18.46), so the
exit does not fire and `do_brk_flags` maps `[65536, 69632)` (:194-195)
while `mm->brk` becomes 65537 (:197).  The ledger owns the one byte, the
zero-fill covers the page.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_one_byte_grow_installs_a_page (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 65537 i m_est o ↔
      (o = Ok (mkEffect 65537 [] [(65536, 4096)])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 1)] [] 65536 65537 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 65536 [] []) m_est []) := by
  sys_norm

/-- …and a kernel granting the byte without the page is refused.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_one_byte_grow_without_the_page_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 65537 i m_est (Ok (mkEffect 65537 [] []) m' evs) := by
  sys_refute

/-- A request at the top of the address space answers the unchanged break
and nothing else: Linux's `PAGE_ALIGN(2^64 - 1)` wraps to 0, so
`check_brk_limits(oldbrk, newbrk - oldbrk)` asks `get_unmapped_area` for a
length past `TASK_SIZE` and gets -ENOMEM (mm/mmap.c:180-181, :824-825,
Linux v6.18.46), a `goto out`; the model rounds in `Int`, where `2^64` is
above `alloc_top`, and the header's promise that a round-up near `2^64`
never wraps into a small grant is what this pins.
kernel: mm/mmap.c:brk,check_brk_limits@v6.18.46 -/
theorem brk_request_near_two_pow_64_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec (Z_to_bv 64 (two_pow_64 - 1)) i m_est o ↔ o = Ok (mkEffect 65536 [] []) m_est [] := by
  sys_norm

/-- …so a grant that wrapped into a small range is refused.
kernel: mm/mmap.c:brk,check_brk_limits@v6.18.46 -/
theorem brk_request_near_two_pow_64_wrapped_grant_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec (Z_to_bv 64 (two_pow_64 - 1)) i m_est
        (Ok (mkEffect (Z_to_bv 64 (two_pow_64 - 1)) [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-! ## brk: ONE FREE PAGE ABOVE THE NEW BREAK

`SYSCALL_DEFINE1(brk)` (mm/mmap.c, Linux v6.18.46), after
`check_brk_limits` and before `do_brk_flags`, searches
`vma_find(&vmi, newbrk + PAGE_SIZE + stack_guard_gap)` from `oldbrk` and
refuses when `newbrk + PAGE_SIZE > vm_start_gap(next)` (:187-190), where
`vm_start_gap` is `vm_start` itself for an ordinary mapping
(include/linux/mm.h:3716-3725, Linux v6.18.46).  So a mapping meeting
`[oldbrk, newbrk + PAGE_SIZE)` — the pages being installed and one more —
makes the grant inadmissible and the old break the only answer.  Pinned
from both sides: a neighbour at 69632 blocks the grow from 65536 to 69632
(the installed page `[65536, 69632)` plus one lands flush against it), a
neighbour at 73728 does not, and a mapping over the pages themselves
blocks it too. -/

/-- Flush against the neighbour: the unchanged break is the only answer.
kernel: mm/mmap.c:brk; include/linux/mm.h:vma_find,vm_start_gap@v6.18.46 -/
theorem brk_grow_flush_against_neighbour_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69632 i m_neighbour_flush o ↔ o = Ok (mkEffect 65536 [] []) m_neighbour_flush [] := by
  sys_norm

/-- …and a kernel granting the grow up to the neighbour is refused: the
negative the gate's old `[lo, hi)` range would have answered `CheckOk`.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate brk#3:ret-addr:a0 -- brk-guard
rocq-twin: brk_grow_flush_against_neighbour_rejected -/
theorem brk_grow_flush_against_neighbour_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69632 i m_neighbour_flush (Ok (mkEffect 69632 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- One page below the neighbour the same grow is granted: the lookahead
is one page and not more (`newbrk + PAGE_SIZE`, mm/mmap.c:189, Linux
v6.18.46), so the ledger gains the heap page beside the neighbour.
kernel: mm/mmap.c:brk; include/linux/mm.h:vma_find,vm_start_gap@v6.18.46 -/
theorem brk_grow_one_page_below_neighbour_grants (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69632 i m_neighbour_gap o ↔
      (o = Ok (mkEffect 69632 [] [(65536, 4096)])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4096), (73728, 4096)] [] 65536 69632 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 65536 [] []) m_neighbour_gap []) := by
  sys_norm

/-- A live page over the pages the grow would install blocks it as well:
`vma_find` from `oldbrk` meets it first (mm/mmap.c:187-190, Linux v6.18.46).
kernel: mm/mmap.c:brk; include/linux/mm.h:vma_find@v6.18.46 -/
theorem brk_grow_into_live_page_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69632 i m_heap_covered o ↔ o = Ok (mkEffect 65536 [] []) m_heap_covered [] := by
  sys_norm

/-- …and the grant over the live page is refused: `vma_find` from `oldbrk`
meets the mapping covering it (mm/mmap.c:187-190, Linux v6.18.46).
kernel: mm/mmap.c:brk; include/linux/mm.h:vma_find@v6.18.46 -/
theorem brk_grow_into_live_page_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69632 i m_heap_covered (Ok (mkEffect 69632 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- `brk(65537)` with the neighbour at 69632: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_one_byte_grow_flush_against_neighbour_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_flush_one_byte (r : word) : brk_r_ok m_neighbour_flush 65537 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

attribute [sys_simp] brk_r_ok_flush_one_byte

/-- The gate reads the INSTALLED pages, not the requested bytes: a one-byte
grow past the aligned break installs `[65536, 69632)`, so with the
neighbour at 69632 the lookahead (mm/mmap.c:187-190, Linux v6.18.46)
refuses it exactly as it refuses the full-page grow.
kernel: mm/mmap.c:brk; include/linux/mm.h:vma_find,vm_start_gap@v6.18.46 -/
theorem brk_one_byte_grow_flush_against_neighbour_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 65537 i m_neighbour_flush o ↔ o = Ok (mkEffect 65536 [] []) m_neighbour_flush [] := by
  sys_norm

/-! ## brk: the shrink

`brk <= mm->brk` (mm/mmap.c:161, Linux v6.18.46) hands `do_vmi_align_munmap`
the page range `[newbrk, oldbrk)` (:173-175; mm/vma.c:1557), which tears
the PTEs down: the freed pages really go, and a re-grow of the same
addresses hands back fresh zeroes.  When the two breaks round to one page
the `oldbrk == newbrk` exit (:155-158) moves `mm->brk` and frees not one
byte.  A shrink can fail (`goto out` at :166 and :173-175), so the old
break stays an allowed answer. -/

/-- The shrink test of `brk_maps_next` is spelled `0 < vm_brk && r < vm_brk`,
as in Rocq, and its first conjunct is implied by its second: `bv_unsigned`
is a `Nat` cast, so `r < vm_brk` already puts the break above zero.  The
ledger's test is the strict half of the kernel's shrink test in `brk`
(mm/mmap.c:161, Linux v6.18.46), `brk <= mm->brk`, taken on the RESOLVED
break rather than the request: the equality is the `oldbrk == newbrk` exit
(:155-158), which frees nothing, and the same-page shrink that exit also
takes is where the byte-granular ledger deliberately departs
(`bugs/brk-same-page-shrink-drops-mapped-bytes.md`).  Stated here because
the mutation sweep's `guard-drop` of the first conjunct is an EQUIVALENT
mutant that no pin can kill; `tools/lean_mutation/allowlist.json` names
this theorem as its proof.  Its two bound siblings at the same `<`,
`0 ≤ vm_brk` (bound-flip) and `1 < vm_brk` (bound-shift), are KILLED by
this theorem rather than allowlisted: the shift falsifies the statement at
`vm_brk = 1`, and the flip leaves a `decide (0 ≤ …)` the `pos` bullet's
`simp only` set does not discharge, so neither survives to need an entry.
model: the two spellings of the shrink test coincide because `bv_unsigned r ≥ 0` -/
theorem brk_maps_next_established_conjunct_redundant (h : VmMaps) (req r : word) :
    brk_maps_next h req r =
      (if bv_unsigned r < bv_unsigned h.vm_brk
       then maps_subtract h.vm_maps (bv_unsigned r) (bv_unsigned h.vm_brk)
       else brk_grants req r h.vm_brk ++ h.vm_maps) := by
  unfold brk_maps_next
  have h0 : 0 ≤ bv_unsigned r := by unfold bv_unsigned; omega
  by_cases hr : bv_unsigned r < bv_unsigned h.vm_brk
  · have hb : 0 < bv_unsigned h.vm_brk := by omega
    simp only [hr, hb, decide_true, Bool.and_self, ↓reduceIte]
  · simp only [hr, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- `brk(65536)` on the grown heap: the shrink, or the unchanged break.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_shrink_unmaps_freed_tail`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_grown_shrink (r : word) :
    brk_r_ok m_grown 65536 r = true ↔ (r = 65536 ∨ r = 131072) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(129024)`, inside the break's page: the sub-page shrink, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_subpage_shrink_frees_nothing`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_grown_subpage (r : word) :
    brk_r_ok m_grown 129024 r = true ↔ (r = 129024 ∨ r = 131072) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(126976)`, one page down: the shrink, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_shrink_one_page_frees_that_page`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_grown_one_page (r : word) :
    brk_r_ok m_grown 126976 r = true ↔ (r = 126976 ∨ r = 131072) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_grown_shrink brk_r_ok_grown_subpage brk_r_ok_grown_one_page

/-- A SHRINK unmaps the freed heap tail.  From the grown process (break
131072, heap grant `[65536, 131072)`), `brk(65536)` drops the grant from
the ledger — so the freed space can be re-granted later — AND declares
`[65536, 131072)` in `eff_unmaps`, which erases the machine overlay so a
load through a dangling heap pointer faults; or it fails and answers the
old break.  The request is the base itself: a model with `≤` at the floor
would treat it as a query and could not shrink.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem brk_shrink_unmaps_freed_tail (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 65536 i m_grown o ↔
      (o = Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 65536)] [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 131072 [] []) m_grown []) := by
  sys_norm

/-- …and a shrink that declares NO unmap is inadmissible: the freed pages
really go on Linux.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#3:drop-unmaps
rocq-twin: brk_shrink_must_declare_unmaps -/
theorem brk_shrink_must_declare_unmaps (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 65536 i m_grown (Ok (mkEffect 65536 [] []) m' evs) := by
  sys_refute

/-- …nor may it declare MORE than it freed.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#3:grow-unmaps:4096 -/
theorem brk_shrink_over_declared_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 65536 i m_grown (Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 69632)] [] []) m' evs) := by
  sys_refute

/-- …nor name the wrong range.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#3:shift-unmaps:4096 -/
theorem brk_shrink_shifted_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 65536 i m_grown (Ok (SyscallEffect.mkEffectU 65536 [] [] [(69632, 65536)] [] []) m' evs) := by
  sys_refute

/-- The alignment boundary: a SUB-PAGE shrink frees NOTHING.  Linux
page-aligns both breaks and takes the `newbrk == oldbrk` early exit
(mm/mmap.c:153-158, Linux v6.18.46), so brk from 131072 down to 129024
(0x1f800, inside the same page) moves `mm->brk` and unmaps not one byte —
the written heap survives and `eff_unmaps` is empty.  `vm_maps` still
tracks the break at byte granularity, so the ledger entry shrinks; that
only bounds where a later grant may be placed.  The second disjunct is the
model's shrink-may-fail admission (`brk_r_ok`): both shrink refusals
(:164-166, :173-175) sit below the exit and cannot fire here, and the one
gate above it, `check_data_rlimit` (:149-151), passes for a request under
a break it already admitted — unless another process lowered this task's
`RLIMIT_DATA` with `prlimit64` in between, which no arm models and no
recorded trace shows.  It is admitted for that path and for no other.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_subpage_shrink_frees_nothing (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 129024 i m_grown o ↔
      (o = Ok (mkEffect 129024 [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 63488)] [] 65536 129024 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 131072 [] []) m_grown []) := by
  sys_norm

/-- …so a sub-page shrink claiming to free a page is refused.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#5:smuggle-unmap:a0:4096 -/
theorem brk_subpage_shrink_smuggled_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 129024 i m_grown (Ok (SyscallEffect.mkEffectU 129024 [] [] [(129024, 4096)] [] []) m' evs) := by
  sys_refute

/-- `brk(131071)`, one byte down: the shrink, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_shrink_one_byte_moves_the_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_grown_one_byte (r : word) :
    brk_r_ok m_grown 131071 r = true ↔ (r = 131071 ∨ r = 131072) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_grown_one_byte

/-- The smallest shrink there is: ONE byte down, inside the break's page,
moves `mm->brk` by that byte and frees nothing (mm/mmap.c:155-158, Linux
v6.18.46), and the byte-granular ledger truncates the grant by exactly
one byte.  Pinned so the shrink test cannot be narrowed by a byte.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_one_byte_shrink_truncates_the_grant (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 131071 i m_grown o ↔
      (o = Ok (mkEffect 131071 [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 65535)] [] 65536 131071 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 131072 [] []) m_grown []) := by
  sys_norm

/-- One page down, exactly: `[PAGE_ALIGN(126976), PAGE_ALIGN(131072))` is
the one page `[126976, 131072)`, and that is what goes (mm/mmap.c:173-175,
Linux v6.18.46).
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem brk_shrink_one_page_frees_that_page (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 126976 i m_grown o ↔
      (o = Ok (SyscallEffect.mkEffectU 126976 [] [] [(126976, 4096)] [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 61440)] [] 65536 126976 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 131072 [] []) m_grown []) := by
  sys_norm

/-- A shrink of ONE BYTE moves `mm->brk` and frees nothing — the same-page
exit (mm/mmap.c:155-158, Linux v6.18.46) — and the ledger's byte-granular
entry loses exactly that byte.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_shrink_one_byte_moves_the_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 131071 i m_grown o ↔
      (o = Ok (mkEffect 131071 [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 65535)] [] 65536 131071 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 131072 [] []) m_grown []) := by
  sys_norm

/-! ## brk: the same-page boundary, and the no-access overlay

Moving the break within an already mapped page installs no page and
zero-fills nothing: the `oldbrk == newbrk` exit (mm/mmap.c:155-158, Linux
v6.18.46) — so a shrink-and-regrow within one page must not overwrite
bytes above the temporary break.  The no-access overlay follows the same
physical boundary: start eight bytes below the end of a guarded page,
shrink four bytes, regrow the four, and both transitions preserve the
guard, while `vm_maps` records the two logical pieces. -/

/-- The mirror image on GROW of the sub-page shrink: no page is installed
and nothing is zeroed.
kernel: mm/mmap.c:brk@v6.18.46
rocq-twin: brk_same_page_regrow_zeros_nothing -/
theorem brk_same_page_regrow_zeros_nothing : brk_zeros 69624 69624 69620 = [] := by
  decide

/-- `brk(69620)` on the guarded page: the shrink, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_same_page_shrink_preserves_noaccess`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_same_page_shrink (r : word) :
    brk_r_ok m_brk_same_page 69620 r = true ↔ (r = 69620 ∨ r = 69624) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(69624)` on the shrunk page: the regrow, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_same_page_regrow_preserves_noaccess`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_same_page_regrow (r : word) :
    brk_r_ok m_brk_same_page_shrunk 69624 r = true ↔ (r = 69624 ∨ r = 69620) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(69640)` on the guarded page, crossing into the next: the grow, or
unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_unaligned_cross_page_zeros_exact_new_page`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_same_page_cross (r : word) :
    brk_r_ok m_brk_same_page 69640 r = true ↔ (r = 69640 ∨ r = 69624) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(65536)` on the guarded one-page heap: the shrink, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_shrink_cuts_the_freed_page_out_of_noaccess`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_noaccess_shrink (r : word) :
    brk_r_ok noaccess_brk_model 65536 r = true ↔ (r = 65536 ∨ r = 69632) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_same_page_shrink brk_r_ok_same_page_regrow
  brk_r_ok_same_page_cross brk_r_ok_noaccess_shrink

/-- The four-byte shrink truncates the grant and keeps the guard: no page
is freed (mm/mmap.c:155-158, Linux v6.18.46), so nothing is cut out of
`vm_noaccess`.  The unchanged break is admitted on the same grounds as in
`brk_subpage_shrink_frees_nothing`: only `check_data_rlimit` (:149-151)
under an externally lowered `RLIMIT_DATA` reaches it.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_shrink_preserves_noaccess (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69620 i m_brk_same_page o ↔
      (o = Ok (mkEffect 69620 [] []) m_brk_same_page_shrunk []
       ∨ o = Ok (mkEffect 69624 [] []) m_brk_same_page []) := by
  sys_norm

/-- The four-byte regrow records a second logical piece, `[69620, 69624)`,
installs no page and exposes no zeroes: the guard survives.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_regrow_preserves_noaccess (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69624 i m_brk_same_page_shrunk o ↔
      (o = Ok (mkEffect 69624 [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(69620, 4), (65536, 4084)] [(65536, 4096)] 65536 69624 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 69620 [] []) m_brk_same_page_shrunk []) := by
  sys_norm

/-- …and the old byte-granular zero effect over the regrown bytes is
refused: the page was never released, so its bytes are what they were.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#6:smuggle-zeros:a0+-8:8 -/
theorem brk_same_page_regrow_smuggled_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69624 i m_brk_same_page_shrunk (Ok (mkEffect 69624 [] [(69620, 4)]) m' evs) := by
  sys_refute

/-- The shrunk guarded page with a live page right above it, at 69632. -/
def m_same_page_flush : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4084), (69632, 4096)] [] 65536 69620 demo_limit 0 demo_sp)

/-- `brk(69624)` beside the neighbour: the regrow, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_same_page_regrow_beside_neighbour_grants`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_same_page_flush (r : word) :
    brk_r_ok m_same_page_flush 69624 r = true ↔ (r = 69624 ∨ r = 69620) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_same_page_flush

/-- The guarded page's break at 69624 with a live neighbour flush against
that page, at 69632: the mapping that blocks a grow ONTO it (the second
review's fixture; `m_same_page_flush` above is the shrunk break at 69620
on the same page). -/
def m_same_page_flush_at_69624 : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4088), (69632, 4096)] [] 65536 69624 demo_limit 0 demo_sp)

/-- `brk(69628)` on the guarded page with the neighbour flush at 69632: the
four-byte grow, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_same_page_grow_ignores_the_neighbour`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_same_page_flush_at_69624 (r : word) :
    brk_r_ok m_same_page_flush_at_69624 69628 r = true ↔ (r = 69628 ∨ r = 69624) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_same_page_flush_at_69624

/-- A grow INSIDE the break's page is subject to no address-space test: the
`oldbrk == newbrk` exit (mm/mmap.c:155-158, Linux v6.18.46) returns the
request before the one-free-page test at :187-190 is reached, so the
neighbour at 69632 that blocks a grow onto it
(`brk_grow_flush_against_neighbour_returns_break`) blocks a four-byte grow
inside the page below it not at all.  No page is installed and nothing is
zeroed; the ledger records the four bytes beside the neighbour.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_grow_ignores_the_neighbour (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69628 i m_same_page_flush_at_69624 o ↔
      (o = Ok (mkEffect 69628 [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(69624, 4), (65536, 4088), (69632, 4096)] [] 65536 69628 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 69624 [] []) m_same_page_flush_at_69624 []) := by
  sys_norm

/-- …and a kernel that installed and zeroed the neighbour's page for it is
refused: nothing is installed on that path.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_grow_zeroing_the_neighbour_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69628 i m_same_page_flush_at_69624 (Ok (mkEffect 69628 [] [(69632, 4096)]) m' evs) := by
  sys_refute

/-- A shrink that FREES a guarded page cuts it out of `vm_noaccess` as well:
the page goes with the VMA (`do_vmi_align_munmap`, mm/vma.c:1557, called at
mm/mmap.c:173-175, Linux v6.18.46), so a later grant there must not be born
hidden.  The one pin
where both the freed range and the no-access ledger are non-empty.
probe: testing/syscall-check/tests/noaccess_vm.c#conform -- brk-shrink -/
theorem brk_shrink_cuts_the_freed_page_out_of_noaccess (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 65536 i noaccess_brk_model o ↔
      (o = Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
             (fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [] [] 65536 65536 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 69632 [] []) noaccess_brk_model []) := by
  sys_norm

/-- …and a post-model that keeps the freed page's guard is refused: a page
Linux tore down cannot still be a guard.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem brk_shrink_keeping_the_guard_rejected (i : SyscallInput) (evs : List event) :
    ¬ brk_spec 65536 i noaccess_brk_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
            (fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [] [(65536, 4096)] 65536 65536 demo_limit 0 demo_sp))
            evs) := by
  intro h
  sys_refute at h

/-- Crossing the boundary is exact: an unaligned old break at 0x10ff8 grown
sixteen bytes maps and zeroes precisely the next page `[0x11000, 0x12000)`
(mm/mmap.c:153-154, :194-195, Linux v6.18.46), while the logical ledger
records only the sixteen newly requested bytes and the guard stays.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_unaligned_cross_page_zeros_exact_new_page (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69640 i m_brk_same_page o ↔
      (o = Ok (mkEffect 69640 [] [(69632, 4096)])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(69624, 16), (65536, 4088)] [(65536, 4096)] 65536 69640 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 69624 [] []) m_brk_same_page []) := by
  sys_norm

/-- A cross-page grow must expose the newly mapped page.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#8:drop-zeros -/
theorem brk_cross_page_grow_without_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69640 i m_brk_same_page (Ok (mkEffect 69640 [] []) m' evs) := by
  sys_refute

/-- …and the raw `[old, new)` zero effect is not the physical page effect.
probe: testing/syscall-check/tests/brk_shrink_frees.c#reject --mutate brk#8:drop-zeros,smuggle-zeros:a0+-16:16 -/
theorem brk_cross_page_grow_byte_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69640 i m_brk_same_page (Ok (mkEffect 69640 [] [(69624, 16)]) m' evs) := by
  sys_refute

/-- A SAME-PAGE grow is subject to no address-space test: `oldbrk ==
newbrk` takes the exit (mm/mmap.c:155-158, Linux v6.18.46) before the
lookahead (:187-190), so the four-byte regrow is granted with a live page
flush above the break's page — where a full-page grow would be refused.
The neighbour is a plain `mmap` that landed at 69632, the page above
`PAGE_ALIGN(69620)`.  The unchanged break is reachable here only through
`check_data_rlimit` (:149-151), which precedes the exit and is a
`goto out`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_same_page_regrow_beside_neighbour_grants (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69624 i m_same_page_flush o ↔
      (o = Ok (mkEffect 69624 [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(69620, 4), (65536, 4084), (69632, 4096)] [] 65536 69624 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 69620 [] []) m_same_page_flush []) := by
  sys_norm

/-! ## brk: the allocation budget

`State.vm_limit` (issue #131) meters brk against the same budget as mmap,
by the byte: a PARAMETER OF THE RUN, the model's deterministic
out-of-memory point, not a kernel constant.  Linux's own refusal on a grow
is `do_brk_flags`'s commit charge — `may_expand_vm` and
`security_vm_enough_memory_mm`, each -ENOMEM (mm/vma.c:2816-2823, Linux
v6.18.46), charged in PAGES (`len >> PAGE_SHIFT`) under the overcommit
policy — on which `SYSCALL_DEFINE1(brk)` answers the old break
(mm/mmap.c:194-195, :209-212).  So the OLD-BREAK half of each pin below is
Linux's; the refusal of the over-budget GRANT is the run's declared premise
(`Equivalence.strong_universal_T_budgets`: the source run never reaches a
budget refusal), which Linux under default overcommit does not share — the
kernel granted `brk_budget.c`'s `overbyte` request, and the `reject` case
pins that the model refuses it anyway.  `--alloc-limit` seeds `vm_limit`
for a probe, so `brk_budget.c`'s cases fill a 64 KiB budget where the
fixtures here fill one page: the same decision at another scale. -/

/-- `brk(69632)` under a one-page budget: the grant fits, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_within_budget_grants`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_tight_fits (r : word) :
    brk_r_ok m_tight_brk 69632 r = true ↔ (r = 69632 ∨ r = 65536) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- `brk(73728)` under a one-page budget: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_beyond_budget_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_tight_over (r : word) : brk_r_ok m_tight_brk 73728 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

/-- `brk(69633)`, one byte over a one-page budget: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_one_byte_over_budget_returns_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_tight_over_byte (r : word) : brk_r_ok m_tight_brk 69633 r = true ↔ r = 65536 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

attribute [sys_simp] brk_r_ok_tight_fits brk_r_ok_tight_over brk_r_ok_tight_over_byte

/-- A one-page grow under a one-page budget fits: granted, or refused
(`exact` fills its 64 KiB budget to the byte the same way).
probe: testing/syscall-check/tests/brk_budget.c#conform --alloc-limit 0x10000 -- exact -/
theorem brk_grow_within_budget_grants (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69632 i m_tight_brk o ↔
      (o = Ok (mkEffect 69632 [] [(65536, 4096)])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4096)] [] 65536 69632 4096 0 demo_sp)) []
       ∨ o = Ok (mkEffect 65536 [] []) m_tight_brk []) := by
  sys_norm

/-- A two-page grow under a one-page budget can only fail: the break comes
back unchanged, the answer Linux gives to a grow it cannot back
(mm/mmap.c:194-195, :209-212, Linux v6.18.46) — here forced by the run's
`vm_limit`, where Linux under default overcommit would grant.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_grow_beyond_budget_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 73728 i m_tight_brk o ↔ o = Ok (mkEffect 65536 [] []) m_tight_brk [] := by
  sys_norm

/-- …and the over-budget grant is inadmissible under the declared budget:
the `overbyte` case records the kernel GRANTING it and the model refusing
the recorded answer, which is what a `reject` case without `--mutate` is.
probe: testing/syscall-check/tests/brk_budget.c#reject --alloc-limit 0x10000 -- overbyte
rocq-twin: brk_grow_beyond_budget_rejects_moving -/
theorem brk_grow_beyond_budget_rejects_moving (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 73728 i m_tight_brk (Ok (mkEffect 73728 [] [(65536, 8192)]) m' evs) := by
  sys_refute

/-- The budget is charged by the byte: 4097 bytes over a 4096-byte budget
is refused (the page charge, 8192, would refuse it too; the two charges
separate on a budget between them, which is what `brk_budget.c`'s `steps`
case exercises — unaligned grows charging `r - old`, not a page each).
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_grow_one_byte_over_budget_returns_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 69633 i m_tight_brk o ↔ o = Ok (mkEffect 65536 [] []) m_tight_brk [] := by
  sys_norm

/-- …so the grant of 4097 bytes is inadmissible under the declared budget.
probe: testing/syscall-check/tests/brk_budget.c#reject --alloc-limit 0x10000 -- overbyte -/
theorem brk_grow_one_byte_over_budget_rejects_moving (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec 69633 i m_tight_brk (Ok (mkEffect 69633 [] [(65536, 8192)]) m' evs) := by
  sys_refute

/-! ### The budget mark

`brk_budget_refused_b` is the arm's mark: `true` exactly where a grow's
byte delta does not fit and nothing but the unchanged break remains (the
Rocq mark's header says what a mark is and why it is a function of the
pre-state and the request).  Its dispatch through
`Run.alloc_budget_refused_b` is pinned in `Checks/Cases/Run.lean`; here
the mark itself, on the fixtures above. -/

/-- A fresh process under an EMPTY budget: every grow by a byte is refused. -/
def m_zero_budget : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 0 0 demo_sp)

/-- Two pages under a one-page budget: refused for want of budget, the
request `brk_grow_beyond_budget_returns_break` answers with the old break.
The budget device is the model's (`State.vm_limit`, issue #131): the mark on a closed fixture; the kernel refusal it stands for is pinned above.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_two_pages_refused : brk_budget_refused_b m_tight_brk 73728 = true := by decide

/-- …and one byte over the page is refused too: the mark is charged by the byte.
The budget device is the model's (`State.vm_limit`, issue #131): the mark on a closed fixture; the kernel refusal it stands for is `brk_grow_one_byte_over_budget_returns_break` above.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_one_byte_over_refused : brk_budget_refused_b m_tight_brk 69633 = true := by decide

/-- One page fits the one-page budget exactly: not refused.
The budget device is the model's (`State.vm_limit`, issue #131): the mark on a closed fixture; the grant it leaves is `brk_grow_within_budget_grants` above.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_exact_fit_not_refused : brk_budget_refused_b m_tight_brk 69632 = false := by decide

/-- A grow of one byte under an empty budget is refused: the delta the
mark reads is `r - vm_brk`, not a page count.
The budget device is the model's (`State.vm_limit`, issue #131): the mark on a closed fixture, byte-granular like the ledger entry a grow records.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_one_byte_over_empty_budget_refused : brk_budget_refused_b m_zero_budget 65537 = true := by decide

/-- A query is never budget-refused, whatever the budget…
The budget device is the model's (`State.vm_limit`, issue #131); the mark's request gate; a query moves nothing.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_query_not_refused : brk_budget_refused_b m_zero_budget 0 = false := by decide

/-- With `vm_brk = 0`, a request above `min_brk` and over the empty budget
leaves the mark false: its positive-break conjunct decides this helper
input. The loader establishes the break
in `load_elf_binary` (fs/binfmt_elf.c:1330, Linux v6.18.46). This pins the
helper's budget device.
kernel: fs/binfmt_elf.c:load_elf_binary; mm/mmap.c:brk@v6.18.46 -/
theorem brk_mark_unestablished_break_not_refused :
    brk_budget_refused_b
      (fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 0 0 0 demo_sp))
      65537 = false := by decide

/-- …nor an invalid request below the base…
The budget device is the model's (`State.vm_limit`, issue #131); the mark's request gate; an invalid request moves nothing.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_gap_not_refused : brk_budget_refused_b m_zero_budget 16384 = false := by decide

/-- …nor the base itself, a grow that installs nothing and charges nothing…
The budget device is the model's (`State.vm_limit`, issue #131); the mark's grow gate; `req = vm_brk` is no grow.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_at_base_not_refused : brk_budget_refused_b m_zero_budget 65536 = false := by decide

/-- …nor a shrink, whatever the budget.
The budget device is the model's (`State.vm_limit`, issue #131); the mark's grow gate; a shrink gives backing back.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem brk_mark_shrink_not_refused : brk_budget_refused_b m_grown 65536 = false := by decide

/-! ### The budget mark for mmap

`mmap_budget_refused_b` is the mmap arm's mark (ticket A13 ported it after
this file's mmap half was written; its dispatch is pinned in
`Checks/Cases/Run.lean`).  Pinned here on the mark itself, decision by
decision, so that the mutation gate over this module reads it: the three
argument gates answer `false` before any shape, every shape that consumes
no backing answers `false`, and each charging branch answers exactly the
negation of its own budget gate.  The kernel line that makes -ENOMEM the
budget's answer is `__mmap_prepare`'s `security_vm_enough_memory_mm` on an
accountable mapping (mm/vma.c:2422-2429, Linux v6.18.46), and what makes a
request NOT accountable is `accountable_mapping` there: `VM_NORESERVE`, or
no `VM_WRITE`. -/

/-- One protected page under an EMPTY budget: a rw commit over it must
charge the page and cannot. -/
def noaccess_page_no_budget : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 0 0 demo_sp)

/-- A misaligned offset is answered -EINVAL before any charge (`riscv_sys_mmap`), so the mark is `false` even on a spent budget.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem mmap_mark_misaligned_offset_not_refused :
    mmap_budget_refused_b 0 4096 3 34 mmap_fd_none 1 spent_budget_model = false := by decide

/-- A file-backed request declines before any charge (`ksys_mmap_pgoff` resolves the fd first), so the mark is `false`.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem mmap_mark_file_backed_not_refused :
    mmap_budget_refused_b 0 4096 3 2 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A zero length is -EINVAL before any charge (`do_mmap`), so the mark is `false`.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_mark_zero_len_not_refused :
    mmap_budget_refused_b 0 0 3 34 mmap_fd_none 0 spent_budget_model = false := by decide

/-- The hint-placed rw grant on the spent budget is budget-refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_rw_on_spent_budget_refused :
    mmap_budget_refused_b 0 4096 3 34 mmap_fd_none 0 spent_budget_model = true := by decide

/-- …and two pages on a one-page remainder are…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_two_pages_on_tight_budget_refused :
    mmap_budget_refused_b 0 8192 3 34 mmap_fd_none 0 tight_model = true := by decide

/-- …while one page that fits is not.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_one_page_on_tight_budget_not_refused :
    mmap_budget_refused_b 0 4096 3 34 mmap_fd_none 0 tight_model = false := by decide

/-- `MAP_NORESERVE` (flags 16418) is not accountable at grant time, so the mark is `false` on the spent budget.
kernel: mm/vma.c:accountable_mapping,__mmap_prepare@v6.18.46 -/
theorem mmap_mark_noreserve_not_refused :
    mmap_budget_refused_b 0 4096 3 16418 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A PROT_NONE reservation consumes no backing: `false` on the spent budget…
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mmap_mark_noaccess_not_refused :
    mmap_budget_refused_b 0 4096 0 34 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …and so does a MAP_FIXED PROT_NONE one (flags 50).
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mmap_mark_fixed_noaccess_not_refused :
    mmap_budget_refused_b 131072 4096 0 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- The MAP_FIXED rw gates answer before any charge: a request whose END
passes the address space (`addr + PAGE_ALIGN(len) ≥ 2^64`, here a page
under `2^64` asked for two pages) meets `__get_unmapped_area`'s
`addr > TASK_SIZE - len` bound (mm/mmap.c:857-858, Linux v6.18.46), and a
length whose rounding wraps meets `do_mmap`'s (:368-370); the spec's gate
covers both, and both are -ENOMEM before any charge…
kernel: mm/mmap.c:__get_unmapped_area,do_mmap@v6.18.46 -/
theorem mmap_mark_fixed_overflow_not_refused :
    mmap_budget_refused_b (Z_to_bv 64 (two_pow_64 - 4096)) 8192 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …a range in the stack band…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mmap_mark_fixed_in_stack_band_not_refused :
    mmap_budget_refused_b (Z_to_bv 64 demo_top) 4096 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …a misaligned address…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mmap_mark_fixed_misaligned_not_refused :
    mmap_budget_refused_b 65537 4096 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …and address zero.
kernel: security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mmap_mark_fixed_at_zero_not_refused :
    mmap_budget_refused_b 0 4096 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A contained rw commit over a protected page under an empty budget
charges that page and is refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_contained_commit_refused :
    mmap_budget_refused_b 65536 4096 3 50 mmap_fd_none 0 noaccess_page_no_budget = true := by decide

/-- …while the same commit over an already-accounted live page charges
nothing, even on the spent budget: the delta is what Linux charges.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_contained_recommit_not_refused :
    mmap_budget_refused_b 65536 4096 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A MAP_FIXED rw grant naming a free address is charged like the hint-placed one: refused on the spent budget…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_fixed_free_range_refused :
    mmap_budget_refused_b 131072 4096 3 50 mmap_fd_none 0 spent_budget_model = true := by decide

/-- …and not with `MAP_NORESERVE` beside `MAP_FIXED` (flags 16434).
kernel: mm/vma.c:accountable_mapping,__mmap_prepare@v6.18.46 -/
theorem mmap_mark_fixed_free_range_noreserve_not_refused :
    mmap_budget_refused_b 131072 4096 3 16434 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A SPANNING rw replacement over the live page and the free page above
it charges the free page: refused on the spent budget…
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas@v6.18.46 -/
theorem mmap_mark_span_on_spent_budget_refused :
    mmap_budget_refused_b 65536 8192 3 50 mmap_fd_none 0 spent_budget_model = true := by decide

/-- …and fits on the two-page budget.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_span_on_tight_budget_not_refused :
    mmap_budget_refused_b 65536 8192 3 50 mmap_fd_none 0 tight_model = false := by decide

/-- A MAP_FIXED rw request over the image's LOAD reservation declines, and a declined request is not budget-refused.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_over_image_not_refused :
    mmap_budget_refused_b 4096 4096 3 50 mmap_fd_none 0 image_at_4096 = false := by decide

/-- …even where a live entry also overlaps the reservation, the shape that reaches the contained arm only with the reservation conjunct dropped.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_over_image_overlap_not_refused :
    mmap_budget_refused_b 4096 4096 3 50 mmap_fd_none 0 noaccess_image_overlap = false := by decide

/-- The image reservation beside an accounted live page under a spent
budget: a request over the image declines, whatever the budget. -/
def image_beside_spent_budget : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(65536, 4096)] [] 0 0 4096 0 demo_sp)

/-- A live PROTECTED entry overlapping the image reservation under an
empty budget: the one ledger on which dropping the reservation conjunct
of the contained arm would charge a page. -/
def protected_image_overlap_no_budget : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(4096, 4096)] [(4096, 4096)] 0 0 0 0 demo_sp)

/-- A shape `mmap_spec` declines (PROT_EXEC, 7) is never budget-refused,
whatever address and budget it names: a declined request grants nothing
the budget could refuse, and the mark's MAP_FIXED rw sub-gates are
entered by the rw MAP_FIXED shape alone.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mmap_mark_unmodeled_shape_not_refused :
    mmap_budget_refused_b 131072 4096 7 34 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A MAP_FIXED rw grant ending EXACTLY at the grant top is inside the
model's window (the bound is inclusive, as `mmap_spec`'s) and so is
charged: refused on the spent budget.  A `<` at that bound would make it
a decline and the mark `false`.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_fixed_ending_at_the_top_refused :
    mmap_budget_refused_b (Z_to_bv 64 (demo_top - 4096)) 4096 3 50 mmap_fd_none 0 spent_budget_model = true := by decide

/-- Over the image reservation the request declines even on a spent
budget, where the spanning arm would have refused it for want of budget
had the reservation conjunct not kept it out of that arm.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_over_image_on_spent_budget_not_refused :
    mmap_budget_refused_b 4096 4096 3 50 mmap_fd_none 0 image_beside_spent_budget = false := by decide

/-- …and over a PROTECTED live entry that overlaps the reservation under
an empty budget, where the contained arm would have charged the page had
its reservation conjunct been dropped.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mmap_mark_over_protected_image_overlap_not_refused :
    mmap_budget_refused_b 4096 4096 3 50 mmap_fd_none 0 protected_image_overlap_no_budget = false := by decide

/-- The old break is an admissible answer to EVERY grow, whatever the
ledger holds: each refusal in `SYSCALL_DEFINE1(brk)` is a `goto out`
returning `origbrk` (mm/mmap.c:209-212, Linux v6.18.46), so a gate that
could refuse the refusal would be wrong.  Pinned on a ledger already past
its budget, where the success resolution is refused and the old break is
the only answer left: `brk_r_ok` at `r = vm_brk` on an over-budget
fixture, where the failure resolution's gate is vacuous (`lo = hi`, delta
0), which is what keeps it admissible.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_refusal_admitted_over_budget :
    brk_r_ok (fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 8192)] [] 65536 73728 4096 0 demo_sp))
      77824 73728 = true := by
  decide

/-! ## brk: the sparse-backing lifecycle

A brk shrink is a sparse-lifecycle boundary.  Start with a one-page heap,
replace it by `MAP_FIXED|MAP_NORESERVE` (flags 16434), touch the page, then
shrink the heap away: both sparse ledgers must be empty before an ordinary
eager mmap spends the released page's budget. -/

/-- A one-page heap under a one-page budget. -/
def brk_sparse_grown : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4096)] [] 65536 69632 4096 0 demo_sp)

/-- …replaced in place by a lazily backed page. -/
def brk_sparse_fixed : Model := with_mmap_replacement 16434 65536 4096 brk_sparse_grown

/-- …and touched once, charging the page. -/
def brk_sparse_touched : Model :=
  with_vm_backing (m_vm_lazy brk_sparse_fixed) [65536] brk_sparse_fixed

/-- The `MAP_FIXED|MAP_NORESERVE` rw commit over the heap page is the
contained replacement: 65536 comes back, the page reads as zeroes, and the
heap's ownership stays while its backing turns lazy (`do_mmap` turns the
bit into `VM_NORESERVE` outside strict overcommit; the argument is on
`Mmap.MAP_NORESERVE`).
kernel: mm/mmap.c:do_mmap@v6.18.46
rocq-twin: brk_heap_fixed_noreserve_replacement -/
theorem brk_heap_fixed_noreserve_replacement (i : SyscallInput) :
    mmap_spec 65536 4096 3 16434 mmap_fd_none 0 i brk_sparse_grown
      (Ok (mkEffect 65536 [] [(65536, 4096)]) brk_sparse_fixed []) := by
  sys_norm

/-- The first touch charges the page.
model: `materialize_model_accesses` on a closed model, the model's reading of a first fault on a `VM_NORESERVE` page.
rocq-twin: brk_heap_fixed_noreserve_first_touch -/
theorem brk_heap_fixed_noreserve_first_touch :
    materialize_model_accesses brk_sparse_fixed [(65536, 1)] = some brk_sparse_touched := rfl

/-- `brk(65536)` on the touched sparse heap: the shrink, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_shrink_forgets_fixed_noreserve_touch`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_sparse_shrink (r : word) :
    brk_r_ok brk_sparse_touched 65536 r = true ↔ (r = 65536 ∨ r = 69632) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_sparse_shrink

/-- Shrinking the heap away frees the page (mm/mmap.c:173-175, Linux
v6.18.46), and with it both sparse ledgers: the post-model is the bare
ledger, nothing lazy and nothing materialized.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap@v6.18.46 -/
theorem brk_shrink_forgets_fixed_noreserve_touch (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 65536 i brk_sparse_touched o ↔
      (o = Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 4096 0 demo_sp)) []
       ∨ o = Ok (mkEffect 69632 [] []) brk_sparse_touched []) := by
  sys_norm

/-- A shrink that keeps the freed page's charge — the post-model still
holding the materialized page — is a kernel that did not free it, and is
refused: the charge goes back with the VMA (`vm_unacct_memory` in
`vms_complete_munmap_vmas`, mm/vma.c:1337, Linux v6.18.46).  A post-model
is invisible to a probe, so the kernel reading is the evidence.
kernel: mm/vma.c:do_vmi_align_munmap,vms_complete_munmap_vmas@v6.18.46 -/
theorem brk_shrink_keeping_the_charge_rejected (i : SyscallInput) (evs : List event) :
    ¬ brk_spec 65536 i brk_sparse_touched
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] [])
            (with_vm_backing [] [65536] (fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 4096 0 demo_sp)))
            evs) := by
  intro h
  sys_refute at h

/-- Read off the post-state function directly: after the shrink both
sparse ledgers are empty and the budget is back to nothing spent.
model: `with_brk_next` on a closed model; ledger arithmetic, not a kernel claim.
rocq-twin: brk_shrink_clears_sparse_ledgers -/
theorem brk_shrink_clears_sparse_ledgers :
    m_vm_lazy (with_brk_next brk_sparse_touched 65536 65536) = []
    ∧ m_vm_materialized (with_brk_next brk_sparse_touched 65536 65536) = []
    ∧ vm_backing_used (with_brk_next brk_sparse_touched 65536 65536) = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- …and that post-state IS the bare ledger the pin above names.
model: a closed `Model` equality, the spec's post-state builder against the fixture the pin states; ledger arithmetic, not a kernel claim. -/
theorem brk_shrink_post_is_the_bare_ledger :
    with_brk_next brk_sparse_touched 65536 65536
      = fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 4096 0 demo_sp) := rfl

/-- An ordinary eager grant then spends the released page's budget: a
placement at 131072 is allowed on the bare ledger.
kernel: mm/mmap.c:do_mmap@v6.18.46
rocq-twin: eager_mmap_reuses_budget_after_sparse_brk_shrink -/
theorem eager_mmap_reuses_budget_after_sparse_brk_shrink (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i
      (fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 65536 4096 0 demo_sp))
      (Ok (mkEffect 131072 [] [(131072, 4096)])
          (fixture (VmMaps.mkVmMapsFull brk_reserved [(131072, 4096)] [] 65536 65536 4096 0 demo_sp)) []) := by
  sys_norm

/-! ## brk: the grant top

`alloc_top` is the model's stand-in for the stack's guard: for the
stack's `VM_GROWSDOWN` VMA `vm_start_gap` subtracts `stack_guard_gap`
(include/linux/mm.h:3704-3725, Linux v6.18.46; mm/mmap.c:941), so Linux
refuses a grow to within a page and that gap of the stack's start
(mm/mmap.c:187-190).  The model has no stack VMA; it keeps every grow at
least `stack_max_size` below the run's `sp`
(bugs/brk-grow-ignores-stack-guard-gap.md).  An established break one
page under `demo_top` asked to grow two pages crosses the top under the
low `sp` and does not under the high one. -/

/-- The break one page under `demo_top`, under the low stack pointer. -/
def brk_top_lo_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [] [] (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 (demo_top - 4096))
    demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)

/-- Rocq's `hi_sp`: a stack pointer 256 MiB above the window's bottom, so
its `alloc_top` clears `demo_top` by that much; inside `Run.valid_sp`. -/
def hi_sp : word := Z_to_bv 64 (sp_window_lo + 0x10000000)

/-- The same break under the high stack pointer. -/
def brk_top_hi_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [] [] (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 (demo_top - 4096))
    demo_limit (Z_to_bv 64 mmap_base_max) hi_sp)

/-- The grow across `demo_top` under the low `sp`: unchanged only.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_across_demo_top_returns_break_under_low_sp`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_top_lo (r : word) :
    brk_r_ok brk_top_lo_model (Z_to_bv 64 (demo_top + 4096)) r = true
      ↔ r = Z_to_bv 64 (demo_top - 4096) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact absurd h (by decide)
    · decide
  · subst h; decide

/-- The same grow under the high `sp`: the grant, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_across_demo_top_admitted_under_high_sp`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_top_hi (r : word) :
    brk_r_ok brk_top_hi_model (Z_to_bv 64 (demo_top + 4096)) r = true
      ↔ (r = Z_to_bv 64 (demo_top + 4096) ∨ r = Z_to_bv 64 (demo_top - 4096)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

/-- The grow ending exactly at `demo_top` under the low `sp`: the grant, or
unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_ending_at_alloc_top_grants_under_low_sp`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_top_lo_exact (r : word) :
    brk_r_ok brk_top_lo_model (Z_to_bv 64 demo_top) r = true
      ↔ (r = Z_to_bv 64 demo_top ∨ r = Z_to_bv 64 (demo_top - 4096)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_top_lo brk_r_ok_top_hi brk_r_ok_top_lo_exact

/-- Under the low `sp` the grow crosses the grant top and only the old
break is answered: the stand-in for the stack-guard refusal
(mm/mmap.c:187-190, Linux v6.18.46).
kernel: mm/mmap.c:brk; include/linux/mm.h:vm_start_gap,stack_guard_start_gap@v6.18.46 -/
theorem brk_grow_across_demo_top_returns_break_under_low_sp (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec (Z_to_bv 64 (demo_top + 4096)) i brk_top_lo_model o ↔
      o = Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] []) brk_top_lo_model [] := by
  sys_norm

/-- …and the grant across the top is refused — under the `alloc_top`
premise: Linux's refusal is the stack guard test (mm/mmap.c:187-190, Linux
v6.18.46) against a stack VMA the model does not carry, so the grant is
one Linux gives while the stack has not grown to within the gap of that
bound (bugs/brk-grow-ignores-stack-guard-gap.md).  No probe reaches the
band.
kernel: mm/mmap.c:brk; include/linux/mm.h:vm_start_gap,stack_guard_start_gap@v6.18.46
rocq-twin: brk_grow_across_demo_top_rejected_under_low_sp -/
theorem brk_grow_across_demo_top_rejected_under_low_sp (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ brk_spec (Z_to_bv 64 (demo_top + 4096)) i brk_top_lo_model
        (Ok (mkEffect (Z_to_bv 64 (demo_top + 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 8192)]) m' evs) := by
  sys_refute

/-- Under the high `sp` the same grow is granted: the top is the run's,
not a constant of the model.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46
rocq-twin: brk_grow_across_demo_top_admitted_under_high_sp -/
theorem brk_grow_across_demo_top_admitted_under_high_sp (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec (Z_to_bv 64 (demo_top + 4096)) i brk_top_hi_model o ↔
      (o = Ok (mkEffect (Z_to_bv 64 (demo_top + 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 8192)])
             (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] []
               (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 (demo_top + 4096))
               demo_limit (Z_to_bv 64 mmap_base_max) hi_sp)) []
       ∨ o = Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] []) brk_top_hi_model []) := by
  sys_norm

/-- The grow UP TO `demo_top` under the low `sp`: the grant, or unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_ending_at_alloc_top_grants_under_low_sp`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_top_lo_to_top (r : word) :
    brk_r_ok brk_top_lo_model (Z_to_bv 64 demo_top) r = true
      ↔ (r = Z_to_bv 64 demo_top ∨ r = Z_to_bv 64 (demo_top - 4096)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_top_lo_to_top

/-- The bound is INCLUSIVE: a grow whose installed page ends exactly at
the grant top is granted.  Linux admits a grow while `newbrk + PAGE_SIZE ≤
vm_start_gap(next)` (mm/mmap.c:189, Linux v6.18.46; the page is the
lookahead's own), and for the stack's `VM_GROWSDOWN` VMA `vm_start_gap`
is its start less `stack_guard_gap` (include/linux/mm.h:3704-3725).  The
model's top sits more than `stack_guard_gap + PAGE_SIZE` below that VMA's
start on every run the premise of bugs/brk-grow-ignores-stack-guard-gap.md
covers — here 8 MiB less a page under `sp` — so the boundary grant is
inside Linux's window, and an inclusive bound admits nothing Linux
refuses.
kernel: mm/mmap.c:brk; include/linux/mm.h:vm_start_gap,stack_guard_start_gap@v6.18.46 -/
theorem brk_grow_ending_at_alloc_top_grants_under_low_sp (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec (Z_to_bv 64 demo_top) i brk_top_lo_model o ↔
      (o = Ok (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
             (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] []
               (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 demo_top)
               demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)) []
       ∨ o = Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] []) brk_top_lo_model []) := by
  sys_norm

/-- …so a kernel refusing that grow AND granting one page more is doubly
wrong; the grant one page past `alloc_top` is the lie
`brk_grow_across_demo_top_rejected_under_low_sp` refuses, and the grant
ending at it is admitted above.  Pinned as the pair the boundary separates.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_grow_ending_at_alloc_top_never_unmodeled (i : SyscallInput) :
    ¬ brk_spec (Z_to_bv 64 demo_top) i brk_top_lo_model Unmodeled := by
  sys_refute

/-! ## The divergences inherited from Rocq

`Sys/Mm/Mmap.lean`'s header declares, one `divergence:` line each, the
five `bugs/` entries its Rocq source cites (BUGS-1,
`tools/check_lean_spec_parity.py`).  Each line owes this file one pin whose
docstring opens `inherited-divergence: bugs/<x>.md` and whose statement is
the KERNEL's answer per the entry, stated in the form the model gives it
today: a refutation where the model refuses what Linux does, an admission
where it allows what Linux never does.  The day a spec change closes one,
the pin flips and the header line says `fixed: <pin>`, which is what
`tools/lean_replay.py` reads as the evidence a divergence-register entry
rests on.  The vm-limit pins sit with the MAP_FIXED argument gate above;
the other four are here, after the brk fixtures they use. -/

/-- inherited-divergence: bugs/grants-into-the-stack-band.md -- a HINT into
the model's stack band is refused where Linux honours it.  The hint
`demo_top` is page-aligned, free on this ledger and under `TASK_SIZE - len`;
Linux's hinted-address test asks nothing more of it than that it clear the
guard gap of the VMA above (`generic_get_unmapped_area_topdown`,
mm/mmap.c:753-761, Linux v6.18.46), and a fresh process's stack VMA starts
far above `sp - 8 MiB`, so the pinned kernel answers the hint with the hint
-- the entry's `mmap addr=top-page` case is this shape one page under
`TASK_SIZE`.  The fresh-grant `choose` refuses every resolution ending
above `alloc_top` (`rw_grant_hint_is_only_a_hint`: the hint changes
nothing), so the kernel's answer is `CheckReject` here: the divergence in
the direction that costs the theorem, inherited from Rocq.  Stated as the
refutation the model gives today; an arm choosing over the kernel's bound
and declining the band flips this to an admission and the header line to
`fixed:`.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,__get_unmapped_area@v6.18.46 -/
theorem hinted_grant_into_the_stack_band_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec (Z_to_bv 64 demo_top) 4096 3 34 mmap_fd_none 0 i one_map_model
        (Ok (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)]) m' evs) := by
  sys_refute

/-- The ledger `Checks.VmMapsDisjoint.wit_overlap` reaches in six modeled
calls -- a 100-byte entry lying wholly inside the page at 65536 -- under
`tight_model`'s two-page budget. -/
def overlap_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(67536, 100), (65536, 4096)] [] 0 0 8192 0 demo_sp)

/-- inherited-divergence: bugs/live-bytes-double-counts-overlapping-entries.md
-- `live_bytes` SUMS the entries, so this ledger is charged 4196 bytes for
the 4096 distinct bytes it owns, and one more page overruns the two-page
budget by the 100 bytes counted twice.  Linux grants it: the pinned guest
runs overcommit mode 1, under which `__vm_enough_memory` (mm/util.c, Linux
v6.18.46) refuses nothing, and `do_mmap` (mm/mmap.c) meters no ledger of
this shape.  The model answers -ENOMEM alone, the narrowing the entry
records, inherited from Rocq.  Stated as today's refutation; counting the
union of the entries flips it to an admission and the header line to
`fixed:`.
kernel: mm/mmap.c:do_mmap; mm/util.c:__vm_enough_memory@v6.18.46 -/
theorem grant_over_a_double_counted_ledger_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mmap_spec 0 4096 3 34 mmap_fd_none 0 i overlap_model
        (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)]) m' evs) := by
  sys_refute

/-- The control: the same page over the same 4096 distinct bytes counted
once -- `tight_model`, the inner entry gone -- is granted, so the 100 bytes
charged twice are all that flips the answer above.
kernel: mm/mmap.c:do_mmap; mm/util.c:__vm_enough_memory@v6.18.46 -/
theorem grant_over_the_same_bytes_counted_once_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i tight_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-- Rocq's `holed_reservation`: two PROT_NONE reservations covering the
address space from `TASK_UNMAPPED_BASE` (0x2aaaaab000) up to `demo_top`,
except for one free page at 0x3aaaaab000. -/
def holed_reservation : List (word × word) :=
  [(Z_to_bv 64 0x2aaaaab000, Z_to_bv 64 0x1000000000),
   (Z_to_bv 64 0x3aaaaac000, Z_to_bv 64 (demo_top - 0x3aaaaac000))]

/-- Rocq's `holed_model`: the reservations owned and inaccessible, nothing
backed, under the demo budget. -/
def holed_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] holed_reservation holed_reservation 0 0
    demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)

/-- inherited-divergence: bugs/mmap-placement-admits-unreachable-addresses.md
-- the page BELOW `TASK_UNMAPPED_BASE` is granted although a fitting gap
sits above it at 0x3aaaaab000.  No kernel search returns it: the top-down
search takes the highest fitting gap under `mmap_base`, and its bottom-up
fallback, like the legacy layout, the lowest fitting gap at or above
`TASK_UNMAPPED_BASE` (`generic_get_unmapped_area_topdown` and
`generic_get_unmapped_area`, mm/mmap.c, Linux v6.18.46); neither walks
past free space to a lower address.  The spec constrains a NULL-hint
placement by admissibility alone -- aligned, positive, under `alloc_top`,
disjoint -- so it allows this one: the over-admission the entry records,
priority 2, kept because the kernel's own answer turns on VMAs and a
randomised base the ledger does not hold.  Stated as the admission the
model gives today; a placement rule narrowed to the kernel's flips this to
a refutation and the header line to `fixed:`.  Rocq states the same case
at the checker.
rocq-twin: mmap_null_hint_skipping_a_free_gap_admitted -/
theorem null_hint_skipping_a_free_gap_admitted (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i holed_model
      (Ok (mkEffect (Z_to_bv 64 0x2aaaaaa000) [] [(Z_to_bv 64 0x2aaaaaa000, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] ((Z_to_bv 64 0x2aaaaaa000, 4096) :: holed_reservation)
            holed_reservation 0 0 demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)) []) := by
  sys_norm

/-- inherited-divergence: bugs/brk-grow-ignores-stack-guard-gap.md -- the
grow whose installed page ends exactly at `alloc_top` is granted whatever
the stack VMA does, because the model carries no stack VMA.  Linux's test
is `newbrk + PAGE_SIZE > vm_start_gap(next)` against the VMA `vma_find`
finds within `PAGE_SIZE + stack_guard_gap` above the new break
(mm/mmap.c:187-190, Linux v6.18.46), and for the stack's `VM_GROWSDOWN`
VMA `vm_start_gap` subtracts `stack_guard_gap` (include/linux/mm.h); so
once the stack has grown to within a page and that gap of `sp - 8 MiB`,
Linux answers the old break where this grant is allowed -- the permissive
divergence the entry records, inherited from Rocq under the premise that
no covered program grows its heap there.  Stated as the admission the
model gives today; carrying the stack VMA and its gap in the ledger flips
this to a refutation and the header line to `fixed:`.
kernel: mm/mmap.c:brk; include/linux/mm.h:vm_start_gap,stack_guard_start_gap@v6.18.46 -/
theorem brk_grow_to_alloc_top_admitted_without_a_stack_vma (i : SyscallInput) :
    brk_spec (Z_to_bv 64 demo_top) i brk_top_lo_model
      (Ok (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] []
            (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 demo_top)
            demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)) []) := by
  sys_norm

/-! ## brk: the unestablished break

`brk_is_grow` and `brk_grow_ok` both open with `0 < old`.  A break that is
not established — `vm_brk = 0`, a state no loaded image has, since
`Run.valid_brk` puts the break above the image — is neither granted nor
gated: Rocq's stated design ("a grow from an unestablished break, which
`brk_grow_ok` does not gate", the budget mark's header).  On every loaded
fixture the two guards are redundant, so they are pinned here as model
arithmetic, where a guard dropped as dead would show. -/

/-- With no established break a resolution records no grant and zero-fills
nothing, whatever the request.
model: `brk_grants` and `brk_zeros` on `old = 0`; the guard Rocq keeps so both effects stay gated on the path that may grow. -/
theorem brk_unestablished_break_grants_nothing :
    brk_grants 4096 4096 0 = [] ∧ brk_zeros 4096 4096 0 = [] := by
  exact ⟨by decide, by decide⟩

/-- …and is not gated: under no budget and over the image's own page the
gate still answers `true`, because its `0 < vm_brk` guard is false
(`brk_grow_ok` on `vm_brk = 0`; Rocq's "a grow from an unestablished
break, which brk_grow_ok does not gate").  No run reaches the state: the
loader establishes the break before the first instruction,
`mm->start_brk = mm->brk = ELF_PAGEALIGN(elf_brk)` in `load_elf_binary`
(fs/binfmt_elf.c:1330, Linux v6.18.46), so on every run the guard is true
and decides nothing; the pin keeps the model's arithmetic visible.
kernel: fs/binfmt_elf.c:load_elf_binary@v6.18.46 -/
theorem brk_unestablished_break_is_not_gated :
    brk_grow_ok (fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 0 0 0 0 demo_sp)) 4096 4096 = true := by
  decide

/-! ## munmap: the argument gates, in `do_vmi_munmap`'s order

`SYSCALL_DEFINE2(munmap)` (mm/mmap.c:1077-1081, Linux v6.18.46) untags
`addr` (:1079; the identity on every modeled run, `Sys/Mm/Mmap.lean`'s
munmap header says why) and reaches `do_vmi_munmap` (mm/vma.c:1604-1627)
through `__vm_munmap` (mm/vma.c:3189-3205).  Its first statement refuses
an unaligned `start`,
a `start` above `TASK_SIZE` and a `len` past `TASK_SIZE - start`, all
-EINVAL (:1611-1612); its second refuses `end == start`, which only
`len = 0` reaches (:1614-1616).  Every refusal is the same errno, so the
order among them is unobservable; what is observable is that all of them
precede the VMA lookup (:1619). -/

/-- A two-page lazy grant at 65536 under a two-page budget, both pages
touched: what the sparse ledgers hold before the unmap. -/
def mmap_lazy_materialized : Model :=
  with_vm_backing [(65536, 8192)] [65536, 69632]
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp))

/-- An unaligned address is -EINVAL whatever the model holds:
`offset_in_page(start)` is the first test (mm/vma.c:1611-1612, Linux
v6.18.46), before the ledger is read.  The `iff` refuses a 0, an unmap
and a decline.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unaligned_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    munmap_spec 65537 4096 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- A kernel that rounded the address down and unmapped the page is lying:
`offset_in_page(start)` is -EINVAL before any lookup (mm/vma.c:1611-1612,
Linux v6.18.46).  No recorded probe issues an unaligned `munmap`.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unaligned_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 65537 4096 i one_map_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- `len = 0` is -EINVAL at an aligned address: `end == start`
(mm/vma.c:1614-1616, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_len_zero_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    munmap_spec 65536 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and never 0, limit or no limit.
probe: testing/syscall-check/tests/munmap_va_limit.c#reject --mutate munmap#2:ret=0 -- zero -/
theorem munmap_len_zero_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 65536 0 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Both at once: the two refusals answer the same errno, so a model that
tested them in the other order would answer the same here (mm/vma.c:1611-1616,
Linux v6.18.46); the pin fixes the answer, not an order.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unaligned_len_zero_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    munmap_spec 65537 0 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Unaligned AND past `TASK_SIZE` at once — `TASK_SIZE + 1` is both —
is -EINVAL from either disjunct of `do_vmi_munmap`'s first test
(mm/vma.c:1611-1612, Linux v6.18.46), so the order between the model's
alignment gate and its range gate is unobservable and the pin fixes the
answer.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unaligned_past_task_size_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 (TASK_SIZE + 1)) 4096 i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and never 0.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unaligned_past_task_size_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec (Z_to_bv 64 (TASK_SIZE + 1)) 4096 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A range whose page-rounded end passes `TASK_SIZE` is -EINVAL before
the ledger is consulted: `start = 2^63`, `len = 2^63` has
`start + PAGE_ALIGN(len) = 2^64`, and Linux's `start > TASK_SIZE` refuses
it (mm/vma.c:1611-1612, Linux v6.18.46) before it forms `end`; the model's
`Int` sum sees the same.  A bound on the rounded length alone would miss it.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_high_addr_sum_wraps_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)) i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- …and never 0.
probe: testing/syscall-check/tests/mmap_shape_args.c#reject --mutate munmap:ret=0 -- munmap-wrap -/
theorem munmap_high_addr_sum_wraps_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 63)) i one_map_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A mapping the MODEL holds just under `2^64` — which no riscv64 kernel
can hand out — is refused by `munmap` with Linux's own -EINVAL, because
the range test precedes the ledger: `start > TASK_SIZE` fails first
(mm/vma.c:1611-1612, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46
rocq-twin: munmap_near_max_is_einval -/
theorem munmap_near_max_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 i near_ceiling_sum_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) near_ceiling_sum_model [] := by
  sys_norm

/-- …and the unmap that used to be reported here is refused: `start >
TASK_SIZE` (mm/vma.c:1611-1612, Linux v6.18.46).  No trace can place a
mapping there, so the kernel reading is the evidence.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_near_max_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 i near_ceiling_sum_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)] [] []) m' evs) := by
  sys_refute

/-- A free range STARTING at `TASK_SIZE` is -EINVAL: `len > TASK_SIZE -
start` with the subtraction zero (mm/vma.c:1611-1612, Linux v6.18.46).
probe: testing/syscall-check/tests/munmap_va_limit.c#conform -- over -/
theorem munmap_at_task_size_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 TASK_SIZE) 4096 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- One byte more than the page under `TASK_SIZE`: Linux's raw
`len > TASK_SIZE - start` (4097 > 4096, mm/vma.c:1611, Linux v6.18.46)
refuses it; in the model's page-rounded `nZ` that is the round-up crossing
the limit, the same refusal by the header's argument.
probe: testing/syscall-check/tests/munmap_va_limit.c#conform -- round -/
theorem munmap_rounding_past_task_size_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 (TASK_SIZE - 4096)) 4097 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- …and never 0.
probe: testing/syscall-check/tests/munmap_va_limit.c#reject --mutate munmap:ret=0 -- round -/
theorem munmap_rounding_past_task_size_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec (Z_to_bv 64 (TASK_SIZE - 4096)) 4097 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The last page under `TASK_SIZE` PASSES the gate — `len > TASK_SIZE -
start` is false at equality (mm/vma.c:1611, Linux v6.18.46) — and then
declines: it is inside the stack band `[alloc_top, TASK_SIZE)` the ledger
does not carry, where Linux answers 0 whether the page is free or the
stack's, and the model cannot tell which.  Neither -EINVAL nor Linux's 0
is admitted.
probe: testing/syscall-check/tests/munmap_va_limit.c#fail-closed -- at -/
theorem munmap_last_page_under_task_size_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 (TASK_SIZE - 4096)) 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so a naive inclusive bound answering -EINVAL there is refused: the
kernel's test is strict.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_last_page_under_task_size_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec (Z_to_bv 64 (TASK_SIZE - 4096)) 4096 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and even Linux's 0 is declined there.
probe: testing/syscall-check/tests/munmap_va_limit.c#fail-closed --mutate munmap#1:ret=0 -- at -/
theorem munmap_last_page_under_task_size_success_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec (Z_to_bv 64 (TASK_SIZE - 4096)) 4096 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ## munmap: the exact match, the no-op, and what declines

Past the gates `do_vmi_munmap` finds the first VMA meeting `[start, end)`
at mm/vma.c:1619 (Linux v6.18.46) through `vma_find`
(include/linux/mm.h:1024-1027): none, and it answers 0 (:1620-1623); one,
and `do_vmi_align_munmap` (:1626; mm/vma.c:1557, Linux v6.18.46) unmaps
the range, splitting a VMA the range only partly covers
(`vms_gather_munmap_vmas`, mm/vma.c:1372, `__split_vma` at :1401 and
:1422).  The model answers the exact whole-mapping case and the free
range; the split it declines. -/

/-- A range EXACTLY a recorded mapping: 0, the mapping gone from the
ledger, the range declared in `eff_unmaps` so a later access faults
instead of reading stale bytes, and nothing else — no errno, no decline.
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46 -/
theorem munmap_exact_grant (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 65536 4096 i one_map_model o ↔
      o = Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [])
             (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) [] := by
  sys_norm

/-- An effect that keeps the memory mapped (no `eff_unmaps`) is refused: a
successful unmap must DECLARE the range it made inaccessible.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate munmap:drop-unmaps -- unmap-protect
rocq-twin: munmap_without_unmap_rejected -/
theorem munmap_without_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 65536 4096 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and one declaring MORE than the mapping is refused too.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate munmap:grow-unmaps:4096 -- unmap-protect -/
theorem munmap_wider_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 65536 4096 i one_map_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 8192)] [] []) m' evs) := by
  sys_refute

/-- An errno on the exact match is refused: every -EINVAL of
`do_vmi_munmap` is an argument test this call passes (mm/vma.c:1611-1616,
Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_exact_grant_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 65536 4096 i one_map_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `len` is page-rounded before the lookup (`end = start + PAGE_ALIGN(len)`,
mm/vma.c:1614, Linux v6.18.46): 4095 bytes name the whole page, and the
unmap is of the whole page.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_len_rounds_up_to_the_page (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 65536 4095 i one_map_model o ↔
      o = Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] [])
             (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp)) [] := by
  sys_norm

/-- …so an unmap of 4095 bytes is refused: `end = start + PAGE_ALIGN(len)`
(mm/vma.c:1614, Linux v6.18.46) — a lie declaring LESS than the page, which
no recorded case mutates in.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_unrounded_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 65536 4095 i one_map_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 4095)] [] []) m' evs) := by
  sys_refute

/-- A range containing no mapped pages is a no-op 0, as on Linux: `vma_find`
finds nothing and `do_vmi_munmap` returns 0 (mm/vma.c:1619-1623, Linux
v6.18.46), with nothing torn down and no state change.
probe: testing/syscall-check/tests/munmap_va_limit.c#conform -- highrepeat -/
theorem munmap_free_range_noop (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 131072 4096 i one_map_model o ↔ o = Ok (mkEffect 0 [] []) one_map_model [] := by
  sys_norm

/-- A free range under `TASK_SIZE` is never -EINVAL.
probe: testing/syscall-check/tests/munmap_va_limit.c#reject --mutate munmap#2:ret=-EINVAL -- highrepeat -/
theorem munmap_free_range_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 131072 4096 i one_map_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and it declares nothing: there was no VMA to tear down.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_free_range_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 131072 4096 i one_map_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(131072, 4096)] [] []) m' evs) := by
  sys_refute

/-- The free-range arm's bound is this run's `alloc_top`, INCLUSIVE: a
free page ending exactly at it is the no-op 0.  `one_map_model`'s stack
pointer is `demo_sp`, so its `alloc_top` is `demo_top`; a `<` in place of
the `≤` would turn this red.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_free_range_ending_at_alloc_top_is_noop (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 i one_map_model o ↔
      o = Ok (mkEffect 0 [] []) one_map_model [] := by
  sys_norm

/-- …and the page above it is inside the stack band the ledger does not
describe, so the arm declines: Linux would answer 0 whether the page is
free or the stack's, which is why neither answer is given.
probe: testing/syscall-check/tests/munmap_va_limit.c#fail-closed -- at -/
theorem munmap_free_range_in_the_stack_band_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec (Z_to_bv 64 demo_top) 4096 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …with Linux's own 0 not admitted there.
probe: testing/syscall-check/tests/munmap_va_limit.c#fail-closed --mutate munmap#1:ret=0 -- at -/
theorem munmap_stack_band_success_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec (Z_to_bv 64 demo_top) 4096 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A PARTIAL unmap declines: Linux splits the mapping (`__split_vma`
from `vms_gather_munmap_vmas`, mm/vma.c:1401, Linux v6.18.46) and answers
0 with the tail still mapped, a state the ledger's whole-entry `map_has`
does not describe; the model fails closed rather than guess.
probe: testing/syscall-check/tests/mremap_shapes.c#fail-closed -- aftermovepartial
rocq-twin: munmap_partial_is_error -/
theorem munmap_partial_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 65536 4096 i two_page_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so Linux's own answer, 0 with the first page gone, is not admitted,
nor a plain 0.
probe: testing/syscall-check/tests/mremap_shapes.c#fail-closed -- aftermovepartial -/
theorem munmap_partial_answers_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 65536 4096 i two_page_map_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) m' evs)
    ∧ ¬ munmap_spec 65536 4096 i two_page_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  constructor <;> sys_refute

/-- A range covered by two ADJACENT entries is not one recorded mapping and
is not free: it declines.  Linux unmaps both VMAs and answers 0
(mm/vma.c:1619-1626, Linux v6.18.46); the model's `map_has` names one
entry, so the answer is withheld rather than guessed.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_spanning_two_entries_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 65536 8192 i adjacent_maps_model o ↔ o = Unmodeled := by
  sys_norm

/-- A range touching the image's LOAD reservation declines: the image
bytes are `State.Image` segments, not entries of the ledger, and Linux's
0 there (it unmaps the segment's page like any other) is not admitted.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_image_range_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 4096 4096 i m_est o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 is not admitted.
kernel: mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem munmap_image_range_success_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ munmap_spec 4096 4096 i m_est
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] []) m' evs) := by
  sys_refute

/-- Unmapping an exact whole mapping that is wholly inaccessible drops it
from BOTH ledgers: a later grant at the same address must not be born
hidden.  Linux tears the `PROT_NONE` VMA down like any other
(mm/vma.c:1626, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46
rocq-twin: munmap_exact_noaccess_removes_both_ledgers -/
theorem munmap_exact_noaccess_removes_both_ledgers (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 65536 12288 i noaccess_three_pages o ↔
      o = Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 12288)] [] [])
             (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 16384 0 demo_sp)) [] := by
  sys_norm

/-- Unmapping a lazily backed, touched mapping forgets its lazy provenance
AND its materialized pages: the post-model is the bare ledger, so the
charge is given back with the pages (Linux frees the pages with the VMA,
`do_vmi_align_munmap`, mm/vma.c:1557, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_munmap,do_vmi_align_munmap@v6.18.46
rocq-twin: munmap_forgets_lazy_and_materialized_metadata -/
theorem munmap_forgets_lazy_and_materialized_metadata (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 65536 8192 i mmap_lazy_materialized o ↔
      o = Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 8192)] [] [])
             (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp)) [] := by
  sys_norm

/-- A 0 that KEEPS the charge — the post-model still holding the
materialized pages — is a kernel that did not free them, and is refused:
the charge goes back with the VMA (`vm_unacct_memory` in
`vms_complete_munmap_vmas`, mm/vma.c:1337, Linux v6.18.46).
kernel: mm/vma.c:do_vmi_align_munmap,vms_complete_munmap_vmas@v6.18.46 -/
theorem munmap_keeping_the_charge_rejected (i : SyscallInput) (evs : List event) :
    ¬ munmap_spec 65536 8192 i mmap_lazy_materialized
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 8192)] [] [])
            (with_vm_backing [] [65536, 69632] (fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp)))
            evs) := by
  intro h
  sys_refute at h

/-- Read off the destroyed post-state directly: nothing lazy, nothing
materialized, nothing charged — and it is the bare ledger the pin names.
model: `with_mmap_destroyed` on a closed model; ledger arithmetic, not a kernel claim.
rocq-twin: munmap_metadata_cannot_be_recharged_after_removal -/
theorem munmap_metadata_cannot_be_recharged_after_removal :
    m_vm_lazy (with_mmap_destroyed 65536 8192 (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp) mmap_lazy_materialized) = []
    ∧ m_vm_materialized (with_mmap_destroyed 65536 8192 (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp) mmap_lazy_materialized) = []
    ∧ vm_backing_used (with_mmap_destroyed 65536 8192 (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp) mmap_lazy_materialized) = 0
    ∧ with_mmap_destroyed 65536 8192 (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp) mmap_lazy_materialized
        = fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp) := by
  refine ⟨by decide, by decide, by decide, rfl⟩

/-! ## munmap of the heap record, and the grow that follows

Unmapping a recorded brk grow is faithful too: Linux unmaps the pages and
`mm->brk` is unchanged — `do_vmi_munmap` never writes it — and a later grow
continues above the old break, from `PAGE_ALIGN(mm->brk)`
(`SYSCALL_DEFINE1(brk)`, mm/mmap.c:153-154, :194, Linux v6.18.46): the
hole stays a hole. -/

/-- The grown process after its heap record was unmapped: the break still
at 131072, nothing owned. -/
def m_heap_unmapped : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [] [] 65536 131072 demo_limit 0 demo_sp)

/-- `munmap` of the heap record on the grown process: the record goes, the
break stays at 131072.
probe: testing/syscall-check/tests/brk_budget.c#conform --alloc-limit 0x1000 -- heapunmap -/
theorem munmap_heap_record_leaves_the_break (i : SyscallInput) (o : outcome SyscallEffect) :
    munmap_spec 65536 65536 i m_grown o ↔
      o = Ok (SyscallEffect.mkEffectU 0 [] [] [(65536, 65536)] [] []) m_heap_unmapped [] := by
  sys_norm

/-- `brk(135168)` after that unmap: the grow above the old break, or
unchanged.
The allowed resolutions of `brk_r_ok` on this fixture, read off once for `sys_norm`;
the pin that states the kernel claim is `brk_grow_after_heap_unmap_continues_above_the_break`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem brk_r_ok_after_heap_unmap (r : word) :
    brk_r_ok m_heap_unmapped 135168 r = true
      ↔ (r = 135168 ∨ r = 131072) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases brk_r_ok_resolutions h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide)
  · rcases h with rfl | rfl <;> decide

attribute [sys_simp] brk_r_ok_after_heap_unmap

/-- The grow that follows installs `[131072, 135168)` above the old break
and leaves the hole `[65536, 131072)` unowned.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem brk_grow_after_heap_unmap_continues_above_the_break (i : SyscallInput) (o : outcome SyscallEffect) :
    brk_spec 135168 i m_heap_unmapped o ↔
      (o = Ok (mkEffect 135168 [] [(131072, 4096)])
             (fixture (VmMaps.mkVmMapsFull brk_reserved [(131072, 4096)] [] 65536 135168 demo_limit 0 demo_sp)) []
       ∨ o = Ok (mkEffect 131072 [] [])
             m_heap_unmapped []) := by
  sys_norm

/-- The SAME model admits a grant one page lower (Rocq
`mmap_modeled_at_ceiling_boundary_grants`): `demo_top - 4096` ends exactly at
`alloc_top`, so the refusal at `demo_top` above is the `alloc_top` conjunct
and nothing else — the ledger is empty and the budget untouched, so region
and budget are as permissive there as here.  Without this the two refusals
above would hold of a model the spec admitted nothing on.
kernel: mm/util.c:mmap_base@v6.18.46 -/
theorem rw_grant_ending_at_alloc_top_admitted_under_low_sp (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i ceiling_room_model
      (Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] []
                      0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- The PROT_NONE twin (Rocq `mmap_noaccess_at_ceiling_boundary_grants`): the
grant also lands in `vm_noaccess`.
kernel: mm/util.c:mmap_base@v6.18.46 -/
theorem noaccess_grant_ending_at_alloc_top_admitted_under_low_sp (i : SyscallInput) :
    mmap_spec 0 4096 0 34 mmap_fd_none 0 i ceiling_room_model
      (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] []
              [(Z_to_bv 64 (demo_top - 4096), 4096)] [] [])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)]
                      [(Z_to_bv 64 (demo_top - 4096), 4096)] 0 0 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-! ## The dispatcher -/

/-- Syscall 222 reaches `mmap_spec` with a0..a5 as its six arguments. 
kernel: include/uapi/asm-generic/unistd.h:__NR3264_mmap; arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap; mm/mmap.c:do_mmap@v6.18.46 -/
theorem sysno_222_is_mmap (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 222 [0, 0, 3, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] :=
  zero_len_anonymous_is_einval
    (SyscallInput.mkInput 222 [0, 0, 3, 34, mmap_fd_none, 0] (fun _ => none) (fun _ => none)) m o

/-- Syscall 214 reaches `brk_spec` with `a0` as the request: the query on
`m_est` through the table is the query on the spec.
kernel: include/uapi/asm-generic/unistd.h:__NR_brk; mm/mmap.c:brk@v6.18.46 -/
theorem sysno_214_is_brk (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 214 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m_est o
      ↔ o = Ok (mkEffect 65536 [] []) m_est [] :=
  brk_zero_returns_current_break
    (SyscallInput.mkInput 214 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) o

/-- Syscall 215 reaches `munmap_spec` with `a0` and `a1`: the unaligned
address is -EINVAL before the model is read, so this holds of every model.
kernel: include/uapi/asm-generic/unistd.h:__NR_munmap; mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem sysno_215_is_munmap (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 215 [65537, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] :=
  munmap_unaligned_is_einval
    (SyscallInput.mkInput 215 [65537, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o

/-! `mremap` (216) and `mprotect` (226) are ported: their dispatcher pins
are `Checks/Cases/Mm/Mremap.lean`'s `sysno_216_is_mremap` and
`Checks/Cases/Mm/Mprotect.lean`'s `sysno_226_is_mprotect`. -/


/-! ## The budget mark, read directly

`mmap_budget_refused_b` is the arm's half of `Run.alloc_budget_refused_b`;
`Checks/Cases/Run.lean` pins it through the dispatcher, at the syscall
number.  These pins read the mark itself, one per branch of it, so that its
behaviour is fixed in THIS file — the twin `tools/lean_mutate.py` builds for
`Sys/Mm/Mmap` — and a mutant of the mark dies here rather than one module
over, where that tool's `--spec Mm/Mmap` closure does not look (the second
review of PR #829 sampled four mark mutants: every one survived this twin
and died in `Cases/Run.lean`).  Each pin names its own fixture.  A ledger
`Cases/Run.lean` reads too is defined here, since that file imports this
one and so cannot be imported here, and its docstring gives the name it
has there.  On a shape `mmap_spec` declines -- a
file-backed request, MAP_FIXED or MAP_FIXED_NOREPLACE at 0, a MAP_FIXED rw
request meeting the image -- the mark answers `false` because no grant
exists for the budget to refuse; the `kernel:` line such a pin carries is
the check whose behaviour the decline stands in for, not an exemption
Linux grants, and each says so, since `model:` is not admissible on a
statement naming the twin's own decision procedure
(`tools/check_lean_pin_evidence.py`, MODEL-TWIN).  Every mutant
`tools/lean_mutate.py` builds of the mark either dies here or is
behaviourally equivalent to it and carries its reason in
`tools/lean_mutation/allowlist.json`.  The equivalent ones live at the
gates the shape gates subsume (a misaligned or file-backed request, and
any PROT_NONE one, matches no charging shape); at the overflow gate the
ceiling gate subsumes; in the swaps of two mutually exclusive checks,
four pairs of shapes that differ in prot and the contained and free-range
gates, which no range passes both of; at the contained gate's else
branch, whose charge the spanning gate repeats on a contained range; and
at the `0 < addr` floor, both copies, whose shift to `1 < addr` differs
only at address 1, which the alignment gate before it has already
answered.
The six registers are `mmap_spec`'s, `fd` unread by either. -/

/-- One page at 65536, owned and inaccessible, under budget `lim`
(`Cases/Run.lean`'s `fixed_rw_model`). -/
def noaccess_page_model (lim : Int) : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 lim 0 demo_sp)

/-- Three pages at 65536, owned and inaccessible, under budget `lim`
(`Cases/Run.lean`'s `three_pages_span_model`). -/
def noaccess_three_pages_model (lim : Int) : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 12288)] 0 0 lim 0 demo_sp)

/-- One page at 65536 reserved to the image, under budget `lim`. -/
def reserved_page_model (lim : Int) : Model :=
  fixture (VmMaps.mkVmMapsFull [(65536, 4096)] [] [] 0 0 lim 0 demo_sp)

/-- The bottom page owned and inaccessible, under a spent budget: a ledger
no run reaches, held only to show the address gate is read before it. -/
def zero_page_noaccess_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(0, 4096)] [(0, 4096)] 0 0 0 0 demo_sp)

/-- A ledger already past its budget: one live rw page under a limit of 0.
No grant produces one, since each is refused beyond the limit; it is held
because two of the mark's decisions can be told apart on it and nowhere
else: the length gate from the charge behind it, and the free-range test
from the spanning one. -/
def over_budget_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 0 0 demo_sp)

/-- The page at 65536 reserved to the image AND owned inaccessible, under a
spent budget: a ledger no run reaches, since every grant is disjoint from
the image (`Sys/Mm/Mmap.lean`'s header), held because it is the only shape
on which the contained branch's two tests disagree. -/
def reserved_live_page_model : Model :=
  fixture (VmMaps.mkVmMapsFull [(65536, 4096)] [(65536, 4096)] [(65536, 4096)] 0 0 0 0 demo_sp)

/-! ### The argument gates: silent on every budget -/

/-- A misaligned offset is -EINVAL in the arch entry, before generic mm
sees the request: the mark's first gate answers `false` on a spent budget.
kernel: arch/riscv/kernel/sys_riscv.c:riscv_sys_mmap@v6.18.46 -/
theorem mark_misaligned_offset_is_silent :
    mmap_budget_refused_b 0 4096 3 34 mmap_fd_none 1 spent_budget_model = false := by decide

/-- A file-backed request (MAP_ANONYMOUS clear) is outside the modeled
shapes: the arm declines it and the mark is silent, on a spent budget too.
The silence is the decline's, not a kernel exemption: Linux resolves the
file in `ksys_mmap_pgoff` -- after `riscv_sys_mmap`'s offset test, the
mark's first read, and before anything else the mark reads -- and charges
a private writable file mapping like an anonymous one
(`accountable_mapping`, mm/vma.c:2326-2336 at v6.18.46, the
`(VM_NORESERVE | VM_SHARED | VM_WRITE) == VM_WRITE` test); the model
carries neither the file nor its charge, so the whole request declines and
no grant exists for the budget to refuse.
kernel: mm/mmap.c:ksys_mmap_pgoff; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mark_file_backed_is_silent :
    mmap_budget_refused_b 0 4096 3 2 3 0 spent_budget_model = false := by decide

/-- A zero length is -EINVAL in `do_mmap` before any accounting.  The
ledger is `over_budget_model`, already past its budget: a request of no
pages that reached the hint-placed charge would be refused there
(`4096 + 0 ≤ 0` fails), so this is the one ledger on which the length
gate can be told from the charge behind it -- on a budget merely spent,
a zero charge is silent with or without the gate.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_zero_length_is_silent :
    mmap_budget_refused_b 0 0 3 34 mmap_fd_none 0 over_budget_model = false := by decide

/-! ### The hint-placed shape -/

/-- Two pages on a one-page remainder: the mark fires…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_two_pages_on_tight_budget_fires :
    mmap_budget_refused_b 0 8192 3 34 mmap_fd_none 0 tight_model = true := by decide

/-- …one page within it does not…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_one_page_on_tight_budget_is_silent :
    mmap_budget_refused_b 0 4096 3 34 mmap_fd_none 0 tight_model = false := by decide

/-- …and one page on the spent budget does: the fixture whose `iff` above,
`rw_grant_over_budget_is_enomem`, admits nothing but -ENOMEM.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_one_page_on_spent_budget_fires :
    mmap_budget_refused_b 0 4096 3 34 mmap_fd_none 0 spent_budget_model = true := by decide

/-- `MAP_NORESERVE` is not accountable at grant time — `do_mmap` turns it
into `VM_NORESERVE` whenever `sysctl_overcommit_memory` is not
`OVERCOMMIT_NEVER`, the overcommit modes 0 and 1 the `MAP_NORESERVE`
docstring of `Sys/Mm/Mmap.lean` states — so the mark is silent on a spent
budget.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mark_noreserve_is_silent :
    mmap_budget_refused_b 0 4096 3 16418 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …and never charged whatever the ledger already holds: a free-range
MAP_FIXED rw request under `MAP_NORESERVE` is silent on a ledger past its
budget, where re-checking the whole ledger after the grant, as the
spanning gate does, would refuse.  `do_mmap` gives the flag `VM_NORESERVE`
unless the overcommit policy is `OVERCOMMIT_NEVER`, and
`accountable_mapping` charges no such vma.
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`; under strict overcommit Linux charges the mapping, a variant this pin does not cover.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mark_fixed_rw_noreserve_over_budget_is_silent :
    mmap_budget_refused_b 131072 4096 3 16434 mmap_fd_none 0 over_budget_model = false := by decide

/-- PROT_NONE consumes no backing: without `VM_WRITE` the mapping is not
accountable, whatever the budget.
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mark_prot_none_is_silent :
    mmap_budget_refused_b 0 4096 0 34 mmap_fd_none 0 spent_budget_model = false := by decide

/-! ### The MAP_FIXED shapes -/

/-- MAP_FIXED PROT_NONE consumes no backing either.
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mark_fixed_prot_none_is_silent :
    mmap_budget_refused_b 65536 4096 0 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A MAP_FIXED rw length that wraps past `2^64` is -ENOMEM in `do_mmap`
(`PAGE_ALIGN(len)` is 0) ahead of any charge: the mark is silent on a
spent budget.  Its overflow gate answers the `false`, and the ceiling gate
behind it would answer the same, since `alloc_top h < 2^64`
(`State/Vm.lean`'s `alloc_top_lt`); that is why no pin can kill a mutant
of the overflow gate, and why each is allowlisted as equivalent rather
than pinned.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_fixed_rw_overflowing_len_is_silent :
    mmap_budget_refused_b 0x1001 (Z_to_bv 64 (-1)) 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- A MAP_FIXED rw range that ends below `2^64` but above every
`alloc_top` — the second-to-last page — is the address space's -ENOMEM
(`addr > TASK_SIZE - len`), not the budget's.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_fixed_rw_above_ceiling_is_silent :
    mmap_budget_refused_b (Z_to_bv 64 (two_pow_64 - 8192)) 4096 3 50 mmap_fd_none 0 spent_budget_model
      = false := by decide

/-- …and the gate is inclusive: `mmap_spec`'s MAP_FIXED rw arm declines
a range above `alloc_top` and places one ending exactly there, and the
mark's gate mirrors that boundary — so the last page under the ceiling
reaches the charge, and a spent budget refuses it.  The boundary is the
spec's: whether Linux admits a MAP_FIXED grant ending exactly at the
model's `alloc_top` is the judgement `tools/lean_mutation/allowlist.json`'s
`V-Mm-Mmap-mmap` entry records as still owed on the spec side, and what
this pin fixes is that the mark moves with the spec, so a port that moves
the boundary in both sees it flip.  Linux's own ceiling test,
`addr > TASK_SIZE - len`, is inclusive in the same sense.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_fixed_rw_ending_at_ceiling_on_spent_budget_fires :
    mmap_budget_refused_b (Z_to_bv 64 (demo_top - 4096)) 4096 3 50 mmap_fd_none 0 spent_budget_model
      = true := by decide

/-- A misaligned MAP_FIXED address is -EINVAL in `__get_unmapped_area`.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_fixed_rw_misaligned_addr_is_silent :
    mmap_budget_refused_b 65537 4096 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- MAP_FIXED at address 0: the spec's placement clause wants `0 < a` and
the mark's gate mirrors it, so no charge is reached; what Linux answers at
the bottom page is a minimum-address policy question, not the budget's —
-EPERM below `dac_mmap_min_addr` (`cap_mmap_addr`,
security/commoncap.c:1459-1471 at v6.18.46) — which the twin declines
whole (`fixed_rw_at_zero_is_unmodeled` above).
kernel: security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mark_fixed_rw_at_zero_is_silent :
    mmap_budget_refused_b 0 4096 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …whatever the ledger holds there.  An inaccessible page owned at 0
under a spent budget would be an exposure the delta gate refuses, but the
address gate is read first, as `security_mmap_addr` is asked in
`__get_unmapped_area` before `__mmap_prepare` counts a page.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_fixed_rw_at_zero_is_silent_over_an_owned_page :
    mmap_budget_refused_b 0 4096 3 50 mmap_fd_none 0 zero_page_noaccess_model = false := by decide

/-- The contained rw replacement is charged as a delta: over the live rw
page of the spent budget the delta is nothing, and the mark is silent…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_over_rw_page_is_silent :
    mmap_budget_refused_b 65536 4096 3 50 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …over an inaccessible page it is the whole page — `pglen -
nr_accounted`, the exposed pages not accounted before — refused on a spent
budget…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_expose_on_spent_budget_fires :
    mmap_budget_refused_b 65536 4096 3 50 mmap_fd_none 0 (noaccess_page_model 0) = true := by decide

/-- …and granted with a page left.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_expose_within_budget_is_silent :
    mmap_budget_refused_b 65536 4096 3 50 mmap_fd_none 0 (noaccess_page_model 4096) = false := by decide

/-- A free-range MAP_FIXED rw grant charges like any grant: one page on
the spent budget is refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_fresh_on_spent_budget_fires :
    mmap_budget_refused_b 131072 4096 3 50 mmap_fd_none 0 spent_budget_model = true := by decide

/-- …and one page on the tight budget is not.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_fresh_within_budget_is_silent :
    mmap_budget_refused_b 131072 4096 3 50 mmap_fd_none 0 tight_model = false := by decide

/-- The spanning commit — the last inaccessible page and the free page
beyond — charges both: two pages on a one-page budget are refused…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_span_on_one_page_budget_fires :
    mmap_budget_refused_b 73728 8192 3 50 mmap_fd_none 0 (noaccess_three_pages_model 4096) = true := by
  decide

/-- …and fit a two-page budget.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_span_within_budget_is_silent :
    mmap_budget_refused_b 73728 8192 3 50 mmap_fd_none 0 (noaccess_three_pages_model 8192) = false := by
  decide

/-- The spanning commit charges the delta as well, not the request: over
the live rw page of the tight budget and the free page beyond, the live
page is `VM_ACCOUNT` and counted in `nr_accounted`, so the charge is one
page and the page left fits it — a charge of the whole request would not.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_span_over_rw_page_within_budget_is_silent :
    mmap_budget_refused_b 65536 8192 3 50 mmap_fd_none 0 tight_model = false := by decide

/-- A MAP_FIXED rw request meeting the image's LOAD reservations is a
shape the twin declines — the final arm of `mmap_spec`'s MAP_FIXED rw
shape, because the image bytes are not entries of this ledger — so there
is no grant for the budget to refuse, and the mark falls to its final
`false` on a spent budget.  Linux would unmap what is there and charge the
request less the accounted pages it removes.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_over_reserved_is_silent :
    mmap_budget_refused_b 65536 4096 3 50 mmap_fd_none 0 (reserved_page_model 0) = false := by decide

/-- …and the reservation is read before the containment: a request that
`vm_maps` contains but that meets the image is the declined shape, not the
contained replacement, so the exposure the delta gate would refuse on a
spent budget is never charged and the mark is silent.  The order is
`mmap_spec`'s, whose contained arm tests `region_free h.vm_reserved`
first; Linux, which keeps no such reservation, would unmap and charge the
page as in the pin above.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_fixed_rw_over_reserved_live_page_is_silent :
    mmap_budget_refused_b 65536 4096 3 50 mmap_fd_none 0 reserved_live_page_model = false := by
  decide

section A18

/-! ### The MAP_FIXED_NOREPLACE shapes

A18's budget marks, apart from its section above and after the MAP_FIXED
marks they follow, so that this part of the file still pins every branch
of the mark in one place. -/

/-- The MAP_FIXED_NOREPLACE rw grant over a free range is charged like any
fresh grant: two pages on `tight_model`'s one remaining page fire the mark…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_beyond_budget_fires :
    mmap_budget_refused_b 131072 8192 3 1048610 mmap_fd_none 0 tight_model = true := by decide

/-- …one page does not…
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_within_budget_is_silent :
    mmap_budget_refused_b 131072 4096 3 1048610 mmap_fd_none 0 tight_model = false := by decide

/-- …the MAP_NORESERVE spelling charges nothing…
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mark_noreplace_noreserve_is_silent :
    mmap_budget_refused_b 131072 8192 3 1064994 mmap_fd_none 0 tight_model = false := by decide

/-- …nor does the PROT_NONE spelling…
kernel: mm/vma.c:accountable_mapping@v6.18.46 -/
theorem mark_noreplace_noaccess_is_silent :
    mmap_budget_refused_b 131072 8192 0 1048610 mmap_fd_none 0 tight_model = false := by decide

/-- …and over a live page the answer is -EEXIST, which `do_mmap` returns
before `mmap_region` charges anything, so a spent budget refuses nothing.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_over_live_is_silent :
    mmap_budget_refused_b 65536 8192 3 1048610 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …and over the image's LOAD reservation likewise: the mark tests the
range free of `vm_reserved` as well as `vm_maps`, the refusal's own
operands, so the -EEXIST charges nothing on a spent budget.  A mark
reading `vm_maps` alone would take this page for free and fire.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mark_noreplace_over_reserved_is_silent :
    mmap_budget_refused_b 65536 4096 3 1048610 mmap_fd_none 0 (reserved_page_model 0) = false := by
  decide

/-- …and over an inaccessible page likewise: `find_vma_intersection` finds
a PROT_NONE VMA like any other, and the -EEXIST (mm/mmap.c:410-413, Linux
v6.18.46) comes before the charge, so a spent budget refuses nothing.  A
mark reading the backed mappings alone would take the page for free and
fire…
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mark_noreplace_over_an_inaccessible_page_is_silent :
    mmap_budget_refused_b 65536 4096 3 1048610 mmap_fd_none 0 (noaccess_page_model 0) = false := by
  decide

/-- …while the page above it meets nothing and has its charge refused.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_beside_an_inaccessible_page_fires :
    mmap_budget_refused_b 69632 4096 3 1048610 mmap_fd_none 0 (noaccess_page_model 0) = true := by
  decide

/-- The charge counts backed bytes alone: `accountable_mapping` makes only
a private writable mapping without VM_NORESERVE accountable
(mm/vma.c:2326-2336, Linux v6.18.46), and `__mmap_prepare` charges only
that (:2422-2429), so the inaccessible page at 65536 holds none of the
4096-byte budget, the page beside it at 69632 fits, and the mark is
silent.  A charge counting every live byte would fire.
kernel: mm/vma.c:__mmap_prepare,accountable_mapping@v6.18.46 -/
theorem mark_noreplace_beside_an_inaccessible_page_within_budget_is_silent :
    mmap_budget_refused_b 69632 4096 3 1048610 mmap_fd_none 0 (noaccess_page_model 4096) = false := by
  decide

/-- MAP_FIXED | MAP_FIXED_NOREPLACE is the same request as the bit alone
(`mmap_noreplace_flags_b`): `do_mmap` ORs MAP_FIXED into a NOREPLACE
request (mm/mmap.c:361-362, Linux v6.18.46) and tests the NOREPLACE bit
alone (:410-413).  Over a free range the combined word is charged like
the bit alone, so the spent budget refuses it and the mark fires.  A mark
deaf to the combined word would stay silent…
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_with_map_fixed_fires :
    mmap_budget_refused_b 131072 4096 3 1048626 mmap_fd_none 0 spent_budget_model = true := by decide

/-- …and over an inaccessible page the combined word is -EEXIST before
any charge, as the bit alone is
(`mark_noreplace_over_an_inaccessible_page_is_silent`), so a zero budget
refuses nothing.  A mark letting MAP_FIXED win would charge the exposure
of the page and fire.
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mark_noreplace_with_map_fixed_over_an_inaccessible_page_is_silent :
    mmap_budget_refused_b 65536 4096 3 1048626 mmap_fd_none 0 (noaccess_page_model 0) = false := by
  decide

/-- One MAP_NORESERVE rw page at 65536, untouched, under a 4096-byte
budget: lazily backed, so it holds none of the budget. -/
def lazy_rw_page_model : Model :=
  with_vm_backing [(65536, 4096)] []
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 4096 0 demo_sp))

/-- The charge reads the budget the backing holds: the untouched
MAP_NORESERVE page at 65536 holds none of it, so the page beside it at
69632 fits the 4096-byte budget and the mark is silent.  `accountable_mapping` leaves a
VM_NORESERVE mapping unaccounted (mm/vma.c:2326-2336, Linux v6.18.46).  A
charge counting the lazy page would fire…
Premise: `do_mmap` sets `VM_NORESERVE` only while `sysctl_overcommit_memory != OVERCOMMIT_NEVER`.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping,__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_beside_a_lazy_page_is_silent :
    mmap_budget_refused_b 69632 4096 3 1048610 mmap_fd_none 0 lazy_rw_page_model = false := by
  decide

/-- …while `materialized_model`'s page, touched, holds the whole budget,
and the same page beside it at 69632 is refused its charge: -ENOMEM is
the spec's only answer there.  That hold is the model's own device: no Linux fault
path charges a touched MAP_NORESERVE page against the commit limit, and
the model charges it on first access
(bugs/vm-limit-environment-obligation.md).  The `kernel:` line covers the
new grant's charge alone.  A charge ignoring materialized pages would stay
silent.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_beside_a_materialized_page_fires :
    mmap_budget_refused_b 69632 4096 3 1048610 mmap_fd_none 0 materialized_model = true := by
  decide

/-- The region test reads the request's own pages and no more.
`find_vma_intersection` searches `[addr, addr + len - 1]`
(mm/mmap.c:885-893, Linux v6.18.46) and a VMA is stored as
`[vm_start, vm_end - 1]` (`vma_iter_store_overwrite`, mm/vma.h:549), so
the page just below the live one at 65536 meets nothing, and
`__mmap_prepare` refuses its charge on the spent budget
(mm/vma.c:2422-2429).  A test reaching past the request's end would meet
the live page and stay silent…
Premise: `dac_mmap_min_addr` is its default 4096 (under qemu-user, the
host's, and no host page this request maps through starts below it), and
no enforcing SELinux policy denies the caller `memprotect:mmap_zero` below
`CONFIG_LSM_MMAP_MIN_ADDR`
(`bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`).
kernel: mm/mmap.c:do_mmap,find_vma_intersection; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_touching_the_live_page_from_below_fires :
    mmap_budget_refused_b 61440 4096 3 1048610 mmap_fd_none 0 spent_budget_model = true := by decide

/-- …and so does the page just above it, which a test reaching before the
request's start would meet.
kernel: mm/mmap.c:do_mmap,find_vma_intersection; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_touching_the_live_page_from_above_fires :
    mmap_budget_refused_b 69632 4096 3 1048610 mmap_fd_none 0 spent_budget_model = true := by decide

/-- The region test reads every page of the request, not its first alone:
a request meeting the live page past its first page is -EEXIST and
charges nothing.  `find_vma_intersection` searches all of
`[61440, 69631]` (mm/mmap.c:885-893, Linux v6.18.46), and `do_mmap`
answers -EEXIST (:410-413) before `mmap_region` reaches the charge in
`__mmap_prepare` (mm/vma.c:2422-2429).  A test reading the first page
alone would find it free and fire.
kernel: mm/mmap.c:do_mmap,find_vma_intersection; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_meeting_the_live_page_past_its_first_page_is_silent :
    mmap_budget_refused_b 61440 8192 3 1048610 mmap_fd_none 0 spent_budget_model = false := by decide

/-- The rw branch reads `prot` whole.  PROT_SEM beside rw is a prot the
spec declines (`noreplace_prot_sem_is_unmodeled`), so no grant exists for
the budget to refuse, and the mark is silent where the same request at
prot 3 fires (`mark_noreplace_touching_the_live_page_from_above_fires`).
Linux reads the three prot bits alone and charges this request like rw,
so the `kernel:` line names the check the decline stands in for, not an
exemption Linux grants.  A mark reading prot's low three bits, or none of
it, would fire, and a run reaching the decline would be excluded by the
budget premise instead of falsifying `modeled`…
kernel: include/linux/mman.h:calc_vm_prot_bits; mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_prot_sem_is_silent :
    mmap_budget_refused_b 69632 4096 11 1048610 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …and so is a prot with bit 32 set beside rw, which the spec declines
too (`noreplace_prot_bit_32_is_unmodeled`) and Linux reads as rw.
kernel: include/linux/mman.h:calc_vm_prot_bits; mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_prot_bit_32_is_silent :
    mmap_budget_refused_b 69632 4096 4294967299 1048610 mmap_fd_none 0 spent_budget_model = false := by
  decide

/-- …and so is each shape the next pins name, one change from the rw
request that the spec declines: a page-aligned offset
(`noreplace_nonzero_offset_is_unmodeled`), which `__get_unmapped_area`
treats as zero for anonymous memory (mm/mmap.c:838-840, Linux
v6.18.46)…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_noreplace_nonzero_offset_is_silent :
    mmap_budget_refused_b 69632 4096 3 1048610 mmap_fd_none 4096 spent_budget_model = false := by
  decide

/-- …an executable prot (`noreplace_exec_prot_is_unmodeled`)…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_exec_prot_is_silent :
    mmap_budget_refused_b 69632 4096 7 1048610 mmap_fd_none 0 spent_budget_model = false := by
  decide

/-- …MAP_SHARED (`noreplace_shared_is_unmodeled`)…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_shared_is_silent :
    mmap_budget_refused_b 69632 4096 3 1048609 mmap_fd_none 0 spent_budget_model = false := by
  decide

/-- …MAP_POPULATE (`noreplace_populate_is_unmodeled`)…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_populate_is_silent :
    mmap_budget_refused_b 69632 4096 3 1081378 mmap_fd_none 0 spent_budget_model = false := by
  decide

/-- …MAP_HUGETLB, set up by `ksys_mmap_pgoff` (mm/mmap.c:584-601, Linux
v6.18.46) before `do_mmap` runs…
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem mark_noreplace_hugetlb_is_silent :
    mmap_budget_refused_b 69632 4096 3 1310754 mmap_fd_none 0 spent_budget_model = false := by
  decide

/-- …and a read-only prot (`noreplace_read_only_is_unmodeled`).  A mark
that dropped the offset test, or took any of these shapes for rw, would
fire on its pin.
kernel: include/linux/mman.h:calc_vm_prot_bits; mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_read_only_is_silent :
    mmap_budget_refused_b 69632 4096 1 1048610 mmap_fd_none 0 spent_budget_model = false := by
  decide

/-- The pins above take the declined shapes one at a time; this takes the
class: the mark fires only on one of the spec's three rw shapes.  As in
`mark_noreplace_prot_sem_is_silent`, the `kernel:` line names the charge
a decline stands in for, not an exemption Linux grants.
kernel: mm/vma.c:accountable_mapping,__mmap_prepare; mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_fires_only_on_a_charging_shape (addr len prot flags fd off : word) (m : Model) :
    mmap_budget_refused_b addr len prot flags fd off m = true →
      mmap_modeled_b prot flags off = true ∨ mmap_fixed_rw_b prot flags off = true
        ∨ mmap_noreplace_rw_b prot flags off = true := by
  intro h
  unfold mmap_budget_refused_b at h
  by_cases h1 : mmap_modeled_b prot flags off = true
  · exact Or.inl h1
  by_cases h2 : mmap_fixed_rw_b prot flags off = true
  · exact Or.inr (Or.inl h2)
  by_cases h3 : mmap_noreplace_rw_b prot flags off = true
  · exact Or.inr (Or.inr h3)
  simp only [Bool.not_eq_true] at h1 h2 h3
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, ite_self] at h

/-- The mark's gate is `mmap_spec`'s, word for word, so each answer that is
not a grant charges nothing on the spent budget: a range ending below `2^64`
but above every `alloc_top` is the address space's (:857), not the
budget's…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_noreplace_above_ceiling_is_silent :
    mmap_budget_refused_b (Z_to_bv 64 (two_pow_64 - 8192)) 4096 3 1048610 mmap_fd_none 0
      spent_budget_model = false := by decide

/-- …a page-rounded end reaching `2^64` is -ENOMEM before the ceiling is
read, whether the length wraps under `PAGE_ALIGN` (mm/mmap.c:368-370,
Linux v6.18.46)…
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem mark_noreplace_overflowing_len_is_silent :
    mmap_budget_refused_b 0x1001 (Z_to_bv 64 (-1)) 3 1048610 mmap_fd_none 0 spent_budget_model
      = false := by decide

/-- …or the range does (mm/mmap.c:857-858, Linux v6.18.46)…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_noreplace_wrapping_range_is_silent :
    mmap_budget_refused_b (Z_to_bv 64 (two_pow_64 - 4096)) 8192 3 1048610 mmap_fd_none 0
      spent_budget_model = false := by decide

/-- …while the last page under the ceiling reaches the charge, the bound
being inclusive as in `mark_fixed_rw_ending_at_ceiling_on_spent_budget_fires`…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_noreplace_ending_at_ceiling_on_spent_budget_fires :
    mmap_budget_refused_b (Z_to_bv 64 (demo_top - 4096)) 4096 3 1048610 mmap_fd_none 0
      spent_budget_model = true := by decide

/-- …a misaligned address over a free range is -EINVAL…
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mark_noreplace_misaligned_addr_is_silent :
    mmap_budget_refused_b 0x40000001 4096 3 1048610 mmap_fd_none 0 spent_budget_model = false := by
  decide

/-- …and address 0, free on this ledger, is declined before the ledger is
read, as `mark_fixed_rw_at_zero_is_silent` is.
kernel: security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mark_noreplace_at_zero_is_silent :
    mmap_budget_refused_b 0 4096 3 1048610 mmap_fd_none 0 spent_budget_model = false := by decide

/-- …while the page above it reaches the charge: the address gate is
`mmap_spec`'s `0 < addr`, so 4096, free on this ledger, has its page
refused on the spent budget.  A gate reading `page_size < addr` would
stay silent there.
Premise: `dac_mmap_min_addr` is its default 4096 (under qemu-user, the
host's, and no host page this request maps through starts below it), and
no enforcing SELinux policy denies the caller `memprotect:mmap_zero` below
`CONFIG_LSM_MMAP_MIN_ADDR`
(`bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`).
kernel: security/commoncap.c:cap_mmap_addr; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_first_page_on_spent_budget_fires :
    mmap_budget_refused_b 4096 4096 3 1048610 mmap_fd_none 0 spent_budget_model = true := by decide

/-! #### Every gate of the branch reads the page-rounded length

`do_mmap` rounds the length (mm/mmap.c:368-370, Linux v6.18.46) before the
-EEXIST test, the range tests and the charge read it.  A page-aligned
length cannot tell a rounded read from an unrounded one, so each pin below
takes a length that is not a whole number of pages. -/

/-- A hundred live bytes at 67536, mid-page, under budget `lim`.  An entry
starting on a page boundary meets a page-aligned request's unrounded range
exactly when it meets the rounded one, so an overlap test is told apart
only by an entry like this.  Its live list is the one
`brk_unbacked_ledger` in `Checks/Cases/Checks/Sys/Mm/Mmap.lean` carries on
the witness chain, where no VMA backs the page: there the model's -EEXIST
over the hundred bytes, and their charge, are the residual
bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md records.  Its
reservation, brk and budget are hand-built.  The pins on
it state the mark against the spec's own gates, and stand when a fix to brk
leaves this ledger unreached. -/
def hundred_live_bytes_model (lim : Int) : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(67536, 100)] [] 0 0 lim 0 demo_sp)

/-- One live page at 65536 under a spent budget, started at an entry `sp`
2048 bytes above `demo_sp`, so that its `alloc_top` is `demo_top + 2048`.
A page-aligned request ends at or below a page-aligned line exactly when
its rounded end does, so the ceiling is told apart only by a line like
this. -/
def offset_top_spent_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 4096 0 (Z_to_bv 64 (sp_window_lo + 2048)))

/-- The charge: 8000 bytes cost two pages, which a budget of 8100 bytes
does not hold, so the mark fires where an unrounded read would find the
request within budget…
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_rounded_length_beyond_budget_fires :
    mmap_budget_refused_b 131072 8000 3 1048610 mmap_fd_none 0 (reserved_page_model 8100) = true := by
  decide

/-- …while a budget of exactly two pages holds them.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_rounded_length_within_budget_is_silent :
    mmap_budget_refused_b 131072 8000 3 1048610 mmap_fd_none 0 (reserved_page_model 8192) = false := by
  decide

/-- The -EEXIST gate reads `[addr, addr + len)` with `len` rounded, as
`do_mmap` (mm/mmap.c:410-413, Linux v6.18.46) does, passing
`find_vma_intersection` the length that :368-370 rounded.  So a hundred
bytes at 65536 reach the page holding the live bytes at 67536, the spec
answers -EEXIST, and a spent budget refuses nothing.  A gate reading the
unrounded range would find it free and fire…
kernel: mm/mmap.c:do_mmap,find_vma_intersection@v6.18.46 -/
theorem mark_noreplace_over_bytes_in_the_rounded_page_is_silent :
    mmap_budget_refused_b 65536 100 3 1048610 mmap_fd_none 0 (hundred_live_bytes_model 4096) = false := by
  decide

/-- …as the same request on the page beside them, at 69632, does: it
meets nothing and is charged its whole page, which the 3996 bytes the
hundred leave of the budget do not hold.  A charge of the unrounded
hundred would fit.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_beside_the_hundred_bytes_fires :
    mmap_budget_refused_b 69632 100 3 1048610 mmap_fd_none 0 (hundred_live_bytes_model 4096) = true := by
  decide

/-- The ceiling: under an `alloc_top` 2048 bytes past a page boundary,
2048 bytes at `demo_top` end on the line unrounded and 2048 bytes past it
rounded.  The spec declines a range reaching the stack band, so there is
no grant, and the mark is silent on a spent budget.  `do_mmap` rounds before `__get_unmapped_area`
reads the range (mm/mmap.c:368-370 and :406, Linux v6.18.46)…
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem mark_noreplace_rounded_past_the_ceiling_is_silent :
    mmap_budget_refused_b (Z_to_bv 64 demo_top) 2048 3 1048610 mmap_fd_none 0 offset_top_spent_model
      = false := by decide

/-- …while the page below ends under the line rounded, is free, and has
its charge refused on the spent budget.
kernel: mm/mmap.c:do_mmap; mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem mark_noreplace_rounded_under_the_ceiling_fires :
    mmap_budget_refused_b (Z_to_bv 64 (demo_top - 4096)) 2048 3 1048610 mmap_fd_none 0
      offset_top_spent_model = true := by decide

end A18

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_misaligned_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 8191)) (Z_to_bv 64 (8192)) 3 50 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_error_band_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4095)) (Z_to_bv 64 (4096)) 3 50 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_rounded_length_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 3 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_rw_aligned_over_end_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 3 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_misaligned_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 8191)) (Z_to_bv 64 (8192)) 0 50 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_error_band_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4095)) (Z_to_bv 64 (4096)) 0 50 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_rounded_length_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem fixed_noaccess_aligned_over_end_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 0 50 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_misaligned_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 8191)) (Z_to_bv 64 (8192)) 3 1048610 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_error_band_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4095)) (Z_to_bv 64 (4096)) 3 1048610 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_rounded_length_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 3 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_rw_aligned_over_end_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 3 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_misaligned_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 8191)) (Z_to_bv 64 (8192)) 0 1048610 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_error_band_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4095)) (Z_to_bv 64 (4096)) 0 1048610 mmap_fd_none 0 i m o ↔
      o = Unmodeled := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_rounded_length_wrap_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 22)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm

/-- The spec records the bounds and the source check orders.
kernel: mm/mmap.c:do_mmap,__get_unmapped_area@v6.18.46 -/
theorem noreplace_noaccess_aligned_over_end_t206 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mmap_spec (Z_to_bv 64 (2 ^ 64 - 4096)) (Z_to_bv 64 (8192)) 0 1048610 mmap_fd_none 0 i m o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := by
  sys_norm


end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
