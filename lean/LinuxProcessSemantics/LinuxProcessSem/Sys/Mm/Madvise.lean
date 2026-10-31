import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Mm.Madvise — madvise (233)

Mirrors `theories/LinuxProcessSem/Sys/Mm/Madvise.v`, which answers to Linux
`mm/madvise.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq's `Z.eqb`/`Z.leb` Bool tests are Lean's `==`/decidable `≤` on `Int`,
and its `mod` is `%` — on a non-negative `bv_unsigned` and a positive
`page_size`, `Int.emod` and `Z.modulo` agree; nothing else differs in
spelling.

ONE advice value is answered, `MADV_DONTNEED`, over a range the ledger
describes completely; every other advice value declines.  What the arm
exists for is the backed-memory budget: a `MAP_NORESERVE` page is charged
to `vm_limit` on its first touch (`State.materialize_model_accesses`), and
this arm is the one way short of unmapping the whole mapping to give that
charge back (issue #683; the Rocq header carries the runtime scenario).

THE KERNEL'S ORDER, which the spec follows wherever a call can tell — the
order is behavior — and departs from in one place no call can, named below.
`do_madvise` (mm/madvise.c:1967-1988, Linux v6.18.46) opens with
`madvise_should_skip` (mm/madvise.c:1830-1842), which is `is_valid_madvise`
(mm/madvise.c:1798-1817) — advice validity, `PAGE_ALIGNED(start)`, a
`PAGE_ALIGN(len_in)` that wrapped to zero, `start + len < start`, each
-EINVAL — and then the zero-length exit, which answers 0.  Every refusal in
`is_valid_madvise` is -EINVAL, so the order AMONG them is unobservable and
the arm tests alignment first; what IS observable is that the alignment
and advice gates precede the zero-length exit, which is why `len = 0`
answers 0 only behind the advice gate.  The other two checks are inert at
`len_in = 0` — `len_in && !len` is skipped and `start + 0 < start` is
false — so the arm runs its wrap test AFTER the zero-length exit, and
`Checks/Cases/Mm/Madvise.lean`'s `zero_len_never_wraps` proves the two
orders answer alike.  (The Rocq header's "all four precede the zero-length
exit" is the kernel's source order, not a claim about the arm.)  The
advice gate declines rather than answering -EINVAL for an
unknown value because `madvise_behavior_valid`'s list (mm/madvise.c:1518-1558,
Linux v6.18.46) is under `CONFIG_KSM`, `CONFIG_TRANSPARENT_HUGEPAGE` and
`CONFIG_MEMORY_FAILURE`, so which values are "unknown" is not a fact about
the source alone.  QEMU's user-mode emulation agrees on the two argument
errnos and the zero-length success — `target_madvise` (linux-user/mmap.c:1259-1273,
QEMU 11.1.1): a misaligned `start` -EINVAL (:1264-1266), `len_in == 0`
answered 0 (:1267-1269), a `TARGET_PAGE_ALIGN(len_in)` that wraps to 0 or
a range the guest space cannot hold -EINVAL (:1270-1273) — so all three
are inside the intersection AGENTS.md's priorities require, with ONE
exception: at the exact boundary `start + PAGE_ALIGN(len) = 2^64` Linux's
wrap test refuses (`is_valid_madvise`, mm/madvise.c:1813-1814, Linux
v6.18.46) where QEMU's range test is inclusive (`guest_range_valid_untagged_vaddr`,
include/user/guest-host.h:63-66, QEMU 11.1.1, behind the wrapper at
:116-119) and its `MADV_DONTNEED` arm answers 0 by a path its own
comment calls wrong (linux-user/mmap.c:1303-1307, QEMU 11.1.1);
`bugs/madvise-wrap-boundary-qemu-user-answers-zero.md`
records that residual and `Checks/Cases/Mm/Madvise.lean`'s boundary pins
name it.  QEMU reads
the advice only AFTER its zero-length answer, where Linux validates it
first; the two differ only on an advice this spec declines, so the
advice gate's place before the zero-length answer is Linux's order and
costs nothing under QEMU.

THE ANSWERED SHAPE.  Past the gates the kernel walks the VMAs the range
meets (`madvise_walk_vmas`, mm/madvise.c:1624-1697, Linux v6.18.46) applying
`madvise_vma_behavior` (mm/madvise.c:1338) to each; for `MADV_DONTNEED`
that is `madvise_dontneed_free` (mm/madvise.c:906) and, unless
`madvise_dontneed_free_valid_vma` (mm/madvise.c:875-904) refuses the VMA
— on a non-hugetlb VMA, `VM_PFNMAP`, or `VM_LOCKED` under plain
`MADV_DONTNEED` (:881-888); on a hugetlb VMA, another advice or a start
that is not huge-page aligned (:890-893; an aligned `MADV_DONTNEED` on
hugetlb proceeds with its end rounded down, :901-903) — -EINVAL at
:912-913 —
`madvise_dontneed_single_vma`
(mm/madvise.c:859-872, Linux v6.18.46), which zaps the page range and
returns 0.  None of
the refusing VMA kinds, nor the -EPERM of `can_madvise_modify`
(mm/madvise.c:1290-1325, a sealed VMA, mm/madvise.c:1346-1347, Linux
v6.18.46), nor the userfaultfd retry (mm/madvise.c:918), can arise on a
modeled run: mlock,
mlockall and mseal are outside the modeled surface, the model maps no
device memory, and `Mmap.mmap_spec` declines `MAP_HUGETLB`.  So over a
range inside ONE live anonymous mapping of the ledger, every page of it
read-write, the answer is forced: 0, the range reads back as zeros, and no
event.  `madvise_dontneed_ok` is that gate, one conjunct per way the
ledger's picture could fall short of the kernel's; the Rocq header argues
each conjunct, and the argument is not repeated here.

Nothing here is nondeterministic and no errno is injectable: the only
failures `do_madvise` can report on the answered shape are the -EINTR of a
killable write lock (`madvise_lock`, mm/madvise.c:1737-1739, Linux
v6.18.46), which `MADV_DONTNEED` does not take (`get_lock_mode` gives it
`MADVISE_VMA_READ_LOCK`, mm/madvise.c:1720-1723, same version), and the
walk's -ENOMEM for a hole (mm/madvise.c:1662, returned at :1696, Linux
v6.18.46), which the containment
gate excludes.  `Checks/Cases/Mm/Madvise.lean` pins each of these. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- Is the advice `MADV_DONTNEED`?  `advice` arrives narrowed by
`Syscall.int32`: the kernel declares it `int`
(`SYSCALL_DEFINE3(madvise, unsigned long, start, size_t, len_in, int,
behavior)`, mm/madvise.c:1990-1993, Linux v6.18.46), so the register's high
half is discarded before the switch reads it.  Rocq:
`Z.eqb (bv_unsigned advice) MADV_DONTNEED`. -/
def madvise_dontneed_b (advice : word) : Bool :=
  bv_unsigned advice == MADV_DONTNEED

/-- The answered shape's ledger gate (see the header): clear of the image's
LOAD reservations, inside one live anonymous mapping, every page
read-write.  The argument for each conjunct is on the Rocq definition,
`Madvise.madvise_dontneed_ok`. -/
def madvise_dontneed_ok (h : VmMaps) (addr n : word) : Bool :=
  region_free h.vm_reserved addr n
  && map_contains h.vm_maps addr n
  && region_free h.vm_noaccess addr n

/-- The post-state: every materialized page in the range is dropped, so its
first-touch charge is given back, and nothing else moves — the mapping
stays in `vm_maps`, its lazy provenance stays in `m_vm_lazy`.  Linux keeps
the commit charge of a `VM_ACCOUNT` VMA across a zap too
(`madvise_dontneed_single_vma`, mm/madvise.c:859-872, Linux v6.18.46,
touches no accounting), and the model's eager charge is that commit-time
guarantee.  The bounds are taken in `Int`, as every ledger range is; the
gate above has already bounded `addr + n` below `2^64`. -/
def madvise_dontneed_next (m : Model) (addr n : word) : Model :=
  with_vm_backing (m_vm_lazy m)
    (List.filter
       (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (m_vm_materialized m)) m

/-- `madvise addr len advice`, in the arm's order — the header's, with the
wrap test behind the zero-length exit: the alignment -EINVAL (`is_valid_madvise`, mm/madvise.c:1805-1806, Linux
v6.18.46) before the advice is read; an advice other than `MADV_DONTNEED`
declined; `len = 0` answered 0 (`madvise_should_skip`, mm/madvise.c:1837-1840);
a page-rounded range reaching `2^64` -EINVAL — `PAGE_ALIGN(len_in)` wraps
to 0 exactly when `page_round_up_Z len = 2^64`, and `start + len` wraps
exactly when `addr + nZ ≥ 2^64` for an `nZ` below it, so `is_valid_madvise`'s
last two refusals (mm/madvise.c:1810-1814, Linux v6.18.46) are one test in
`Int`; then the
ledger gate, and the forced answer with `eff_zeros` over the whole
page-rounded range. -/
def madvise_spec (addr len advice : word) : Sys SyscallEffect :=
  if !(bv_unsigned addr % page_size == 0) then err_ret EINVAL
  else if !(madvise_dontneed_b advice) then unmodeled
  else if w_is0 len then ret_only (Z_to_bv 64 0)
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
  then err_ret EINVAL
  else
    m <- get_model ;;
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if madvise_dontneed_ok h addr n then
      modify (fun _ => madvise_dontneed_next m addr n) ;;
      Monad.pure (mkEffect (Z_to_bv 64 0) [] [(addr, n)])
    else unmodeled

end LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise
