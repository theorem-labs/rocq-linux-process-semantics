import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: e3f958f69fdfd31ebcfd5bf8a395be3f4a28414c
drift-ticket: mremap_spec R-Mm-Mremap-rebase -- Issue #1426 changes alignment, zero-new and non-growth answers to declines in both twins; uncommitted port verified locally, advance baseline to the landed commit after merge -/

/-! # LinuxProcessSem.Sys.Mm.Mremap — mremap (216)

Mirrors `theories/LinuxProcessSem/Sys/Mm/Mremap.v`, which answers to Linux
`mm/mremap.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.
The ledger lemma `mremap_move_charge_at_fresh` and its helpers live in `Checks/BudgetPremise.lean`, because a proof in the spec file makes the guard mutants of `mremap_move_charge` STILLBORN.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The port was written against the Rocq file as it read at f44244ad, whose
line numbers were Linux v6.12's, where the syscall was one
`SYSCALL_DEFINE5` body; at v6.18.46 the same decisions are spread over
`do_mremap`, `check_mremap_params`, `check_prep_vma`, `mremap_at`,
`expand_vma` and `move_vma` (mm/mremap.c), threaded through a
`vma_remap_struct`.  Every number here was read at v6.18.46 itself, and
where the two kernels differ in more than a line number the docstring
says how.

Spellings that differ from Rocq without changing a value: `Z.eqb`, `Z.ltb`
and `Z.leb` are Lean's decidable `==`, `<` and `≤` on `Int`; `Z.modulo` by
`page_size` is Lean's `%`, which agrees with Rocq's floor modulo for a
positive divisor; `Z.of_nat (length …)` is a `Nat` cast; `negb (bv_eqb …)`
is `!(bv_eqb …)`.  Rocq's word addition `old + new_n` is `BitVec` addition
here, wrapping the same way.

The Rocq spec declines a page-rounded `new_len` above `TASK_SIZE` at the
same place.  `check_mremap_params` (mm/mremap.c:1775-1776, Linux v6.18.46)
answers it -EINVAL on every path,
before the lock is taken and before any VMA is looked at.  At Linux v6.12
the test sat inside `mremap_to`, the entry point the syscall body took only
under `MREMAP_FIXED` or `MREMAP_DONTUNMAP`, so a `MREMAP_MAYMOVE` grow of
that size never met it and was answered -ENOMEM — by the RLIMIT_AS test of
`may_expand_vm` (mm/mmap.c, Linux v6.12), which the v6.12 grow path ran first
from its `vma_to_resize`, or, past it, by the syscall body's placement search
(mm/mremap.c:1170, Linux v6.12), whose `__get_unmapped_area` (mm/mmap.c, Linux
v6.12) refuses a length above TASK_SIZE.  Two supported kernels answer
differently, so the intersection AGENTS.md's priorities require is empty, and `mremap_spec` declines the
shape rather than pick a version. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The modeled shape — flags exactly `MREMAP_MAYMOVE`, `old` page aligned,
both rounded sizes nonzero, the source one tracked private anonymous rw
mapping — can still fail at RUN time on exactly one errno, ENOMEM, and
only on a RESIZING call.  The Rocq `mremap_errnos` comment walks the v6.12
body; re-read at Linux v6.18.46, mm/mremap.c:

- equal size: NONE.  `check_prep_vma` returns 0 as soon as the call will
  map nothing new (:1676-1677) and `mremap_at` answers `addr` for
  `MREMAP_NO_RESIZE` (:1558-1559) with no allocation, split or accounting
  in between, so nothing on that Linux branch can fail; `mremap_spec`
  declines equal sizes because qemu-user relocates them.
- shrink: `shrink_vma` (:1337-1338) hands the tail to `do_vmi_munmap`
  (mm/vma.c:1604-1627, Linux v6.18.46), which splits the VMA at the new end
  (`vms_gather_munmap_vmas`, mm/vma.c:1382-1403, Linux v6.18.46) — a split that
  can fail to allocate (`__split_vma`, mm/vma.c:510-512, :523-524,
  :527-528, :531-532, Linux v6.18.46) — and, when the kernel's VMA runs
  past the modeled entry, can exceed `sysctl_max_map_count`
  (mm/vma.c:1389-1393, Linux v6.18.46).
- any grow: `may_expand_vm` (mm/mmap.c:1324-1347, Linux v6.18.46,
  RLIMIT_AS / RLIMIT_DATA) in `check_prep_vma` (:1742-1743), which
  `do_mremap` runs (:1932) before `mremap_at` chooses between the two
  paths (:1937).
- grow in place: the commit charge (`vrm_calc_charge` →
  `security_vm_enough_memory_mm`, :990-991, from `expand_vma_in_place`
  at :1458-1459) and a failed `vma_merge_extend` (:1470-1474).
- grow by moving: a failed `get_unmapped_area` in `vrm_set_new_addr`
  (:957-960), and inside `move_vma` the map-count check of
  `prep_move_vma` (:1043-1044), the commit charge (:1281-1282), a failed
  `copy_vma` (`copy_vma_and_data`, :1193-1198) and a short
  `move_page_tables` (:1208-1210).

- EFAULT: no VMA at `addr` (`check_prep_vma`, :1658-1659) and `old_len`
  running past the VMA's end (:1720-1721) are excluded by
  `mremap_source_b`, which demands the source be exactly one tracked
  mapping; VM_DONTEXPAND / VM_PFNMAP (:1736-1737) is never set on an
  anonymous grant — the setters are `remap_pfn_range_internal`
  (mm/memory.c:2953, Linux v6.18.46), `remap_vmalloc_range_partial`
  (mm/vmalloc.c:4615, Linux v6.18.46) and `__install_special_mapping`
  (mm/mmap.c:1455, Linux v6.18.46) among the drivers', and the anonymous
  leg of `do_mmap` reaches none of them: the driver hook `mmap_file` runs
  inside `__mmap_new_file_vma` (mm/vma.c:2458, Linux v6.18.46), which
  `__mmap_new_vma` calls only `if (map->file)` (mm/vma.c:2520-2521, Linux
  v6.18.46), and its `else` at mm/vma.c:2525 (Linux v6.18.46) calls
  `vma_set_anonymous`, defined in include/linux/mm.h:947 (Linux v6.18.46).
- EAGAIN: `mlock_future_ok` (mm/mmap.c:228-243, Linux v6.18.46) returns
  true at once unless VM_LOCKED (:233-234), which only `MAP_LOCKED`,
  `mlock`/`mlock2` (mm/mlock.c:661-666, Linux v6.18.46) or `mlockall`
  (:747, through `mm->def_flags`, :712-714) can set — all outside the
  modeled surface.
- EPERM for a sealed VMA (`check_prep_vma`, :1662-1663, through
  `vma_is_sealed`, mm/vma.h:611-614, Linux v6.18.46) is unreachable:
  VM_SEALED is set by `mseal` (462; `mseal_apply`, mm/mseal.c:71-78, Linux
  v6.18.46, reached from `SYSCALL_DEFINE3(mseal)` at :187), outside the
  modeled surface, and as `VM_SEALED_SYSMAP` (include/linux/mm.h:4402-4405,
  Linux v6.18.46) on kernel-installed system mappings such as the vDSO
  (arch/riscv/kernel/vdso.c:139, Linux v6.18.46), which the ledger never
  carries.
- EINTR from `mmap_write_lock_killable` (`do_mremap`, :1924-1925) is
  unobservable: the wait is TASK_KILLABLE (`down_write_killable`,
  kernel/locking/rwsem.c:1598-1610, Linux v6.18.46, whose slow path
  `__down_write_killable` passes TASK_KILLABLE at :1331), and
  `signal_pending_state` (include/linux/sched/signal.h:408-416, Linux
  v6.18.46) aborts
  such a wait only on a fatal signal, which kills the task before the
  -EINTR reaches a register.  The same argument `Mprotect.mprotect_errnos`
  makes for its own killable lock. -/
def mremap_errnos : List Int := [ENOMEM]

/-- Replace the one mapping based at `old` with `(dst, new_n)`.  The source
is required below to have no `vm_noaccess` overlap, while a moved
destination is fresh, so the no-access ledger is preserved verbatim.
Rocq: `Mremap.mremap_maps_next`. -/
def mremap_maps_next (h : VmMaps) (old dst new_n : word) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved ((dst, new_n) :: map_remove h.vm_maps old)
    h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp

/-- A source is either uniformly lazy or wholly eager.  A MAP_FIXED inside
it can split the backing provenance without splitting `vm_maps`; mremap
fails closed on that mixed representation rather than guess which
provenance a grown tail inherits.  Rocq: `Mremap.mremap_backing_uniform_b`. -/
def mremap_backing_uniform_b (m : Model) (old old_n : word) : Bool :=
  map_contains (m_vm_lazy m) old old_n || region_free (m_vm_lazy m) old old_n

/-- Is the source uniformly lazy (MAP_NORESERVE)?  Rocq: `Mremap.mremap_source_lazy_b`. -/
def mremap_source_lazy_b (m : Model) (old old_n : word) : Bool :=
  map_contains (m_vm_lazy m) old old_n

/-- Update the ownership and sparse-backing ledgers as one state transition.
Materialized pages move with their source-relative offsets; a shrink
releases pages beyond the new end, and a lazy grow extends the lazy range
without eagerly charging its tail.  The kernel behaviour `State.vm_resize_backing`
tracks is cited on that definition.  Rocq: `Mremap.mremap_model_next`. -/
def mremap_model_next (m : Model) (old old_n dst new_n : word) : Model :=
  vm_resize_backing (mremap_source_lazy_b m old old_n) old old_n dst new_n
    (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n) m)

/-- The grown delta reads as fresh zeroes.  Neither `vma_merge_extend`
(mm/vma.c:1750-1760, Linux v6.18.46, called from `expand_vma_in_place`,
mm/mremap.c:1470, Linux v6.18.46) on the in-place path nor `copy_vma`
(mm/vma.c:1853, Linux v6.18.46, called from `copy_vma_and_data`,
mm/mremap.c:1193, Linux v6.18.46) on the move path installs page tables for
it, and a `pte_none` fault on a PRIVATE|ANONYMOUS VMA is served by
`do_anonymous_page` (mm/memory.c:5149, Linux v6.18.46): a read from the
shared zero page (:5169-5172), a write from a zeroed folio
(`alloc_anon_folio`, mm/memory.c:5059-5142, Linux v6.18.46, whose fallback
`folio_prealloc`, mm/memory.c:1200-1207, Linux v6.18.46, allocates it with
`need_zero` set).

The `old_nZ < new_nZ` guard never fires false where this is used:
`mremap_spec` declines equal and shrinking sizes before constructing
effects, so both call sites have already established growth.  It is kept because the
function is total in its arguments and its name promises the tail of a
grow; no trace can distinguish dropping it.  Rocq: `Mremap.mremap_tail`. -/
def mremap_tail (base old_n : word) (old_nZ new_nZ : Int) : List (word × word) :=
  if old_nZ < new_nZ then [(base + old_n, Z_to_bv 64 (new_nZ - old_nZ))] else []

/-- Linux's `PAGE_ALIGN(len)` (`do_mremap`, mm/mremap.c:1917-1918, Linux
v6.18.46) expands to `(len + 4095) & ~4095` on an `unsigned long`
(`PAGE_ALIGN`, include/linux/mm.h:222 → `ALIGN`, include/vdso/align.h:8,
reached through include/linux/align.h → `__ALIGN_KERNEL_MASK`,
include/uapi/linux/const.h:48-49, all Linux v6.18.46), which WRAPS.  It
yields zero on exactly two kinds of input: `len = 0`, and `len` in the top
partial page `[2^64-4095, 2^64-1]`.  (Not the whole top page: `2^64-4096`
is already aligned and survives.)  Computing the round in `Int`, that is
`page_round_up_Z len = 0 ∨ = 2^64`, which is what this decides — so the two
arms of Linux's `!new_len` test (`check_mremap_params`, :1771-1772) need no
separate treatment.  Rocq: `Mremap.page_align_is0_b`. -/
def page_align_is0_b (len : word) : Bool :=
  w_is0 len || (two_pow_64 ≤ page_round_up_Z (bv_unsigned len))

/-- The modeled source.  Linux needs only `vma_lookup(mm, addr)` to succeed
(`do_mremap`, mm/mremap.c:1931, refused at `check_prep_vma`, :1658-1659,
Linux v6.18.46); requiring an EXACT tracked entry is stricter, hence fail
closed, and it is what lets `mremap_model_next` carry `vm_noaccess` over
untouched.  The `vm_reserved` and `vm_noaccess` conjuncts keep the image
and PROT_NONE guards out: the model has no ledger shape for remapping
either.  The Rocq `mremap_source_b` note argues which conjuncts pull their
weight only jointly, and why the `alloc_top` bound is what keeps a
successful in-place return from being mistaken for an encoded errno. -/
def mremap_source_b (h : VmMaps) (old old_n : word) (old_nZ : Int) : Bool :=
  (bv_unsigned old + old_nZ ≤ alloc_top h)
  && region_free h.vm_reserved old old_n
  && map_has h.vm_maps old old_n
  && region_free h.vm_noaccess old old_n

/-- The budget analogue of `may_expand_vm` (mm/mmap.c:1324-1347, Linux
v6.18.46), which mremap reaches from `check_prep_vma` (mm/mremap.c:1742-1743)
with `npages = delta >> PAGE_SHIFT` — Linux charges the NET DELTA, never a
transient peak of both mappings, and its commit charge is the same delta
(`vrm_calc_charge`, :986).  The model checks the complete post-state
instead: that is the same delta for eager mappings, while a MAP_NORESERVE
tail remains lazy and costs nothing until touched.  `check_prep_vma` runs
before `mremap_at` (`do_mremap`, :1932 then :1937), so the same gate
applies to the in-place and the move path; the model does the same.
Rocq: `Mremap.mremap_final_budget_b`. -/
def mremap_final_budget_b (m : Model) (old old_n dst new_n : word) : Bool :=
  vm_backing_within_limit (mremap_model_next m old old_n dst new_n)

set_option linter.unusedVariables false in
/-- Linux grows in place when the request runs exactly to the VMA's end
and `vma_expandable` holds (`vrm_can_expand_in_place`,
mm/mremap.c:1436-1441, Linux v6.18.46; `vma_expandable`, mm/mremap.c:1415-1427).
This is a coarser predicate in both directions — see `mremap_spec` for
why the resulting over-admission is presented as an `alt` rather than a
claim.

Both halves of the `region_free` conjunct are LIVE: the `vm_maps` half is
what the probe's in-place mutation pins, and the `vm_reserved` half — an
in-place grow running into the binary image — has no probe, because no
modeled trace can put a tracked mapping below a LOAD segment, and is
pinned by a hand-built ledger instead.  The `alloc_top` conjunct is LIVE
too, and it is the only thing keeping a grown mapping clear of the dynamic
stack: the stack is in neither `vm_reserved` nor `vm_maps`, so
`region_free` cannot see it.  The Rocq `mremap_inplace_grow_b` note names
the pinning pair for each.  The `old_nZ` parameter is unread here, as in
Rocq; the signature is kept.  Rocq: `Mremap.mremap_inplace_grow_b`. -/
def mremap_inplace_grow_b (m : Model) (old old_n new_n : word) (old_nZ new_nZ : Int) : Bool :=
  let h := m_vmmaps m
  (bv_unsigned old + new_nZ ≤ alloc_top h)
  && region_free (h.vm_reserved ++ map_remove h.vm_maps old) old new_n
  && mremap_final_budget_b m old old_n old new_n

set_option linter.unusedVariables false in
/-- A moved destination.  A MAYMOVE destination IS a preference-free
placement: `vrm_set_new_addr` (mm/mremap.c:942-964, Linux v6.18.46) asks
`get_unmapped_area` with `new_addr = 0` unless `MREMAP_FIXED` or
`MREMAP_DONTUNMAP` is set (:949) and without `MAP_FIXED` unless
`MREMAP_FIXED` is (:952-953), then takes what the search returns
(:957-960).  So the conditions that hold of one hold of the other —
page-aligned, nonzero, below `State.alloc_top`, disjoint from every recorded
mapping — and the conditions that do NOT are the same conditions, for the
same reason; the placement section of the Rocq `Mmap.v` carries the
argument against pinning the search, and this guard lost its search-order
conjunct with its mmap twin.

DISJOINTNESS DOES MORE WORK HERE than in an ordinary grant.  `dst` can never
overlap the source: the search runs while the source VMA is still live
(`vrm_set_new_addr` is called at `expand_vma`, :1539, and the source is
not unmapped until `move_vma` reaches `unmap_source_vma`, :1312, whose
`do_vmi_munmap` is at :1122), so `old` is still in `vm_maps` when
`region_free` is evaluated.  `dst ≠ old` is therefore redundant against a
well-formed ledger; it is load-bearing in the SPEC, because without it the
`choose` would let the move arm produce move-shaped effects at `old`.

`vm_noaccess` is deliberately ABSENT from the `region_free` list; the Rocq
`mremap_fresh_b` note argues why no reachable destination can reach a
protected slice a live entry does not own, and pins the boundary on the
brk-shrink orphan state.  The `old_nZ` parameter is unread here, as in Rocq;
the signature is kept.  Rocq: `Mremap.mremap_fresh_b`. -/
def mremap_fresh_b (m : Model) (old_nZ new_nZ : Int) (old old_n dst new_n : word) : Bool :=
  let h := m_vmmaps m
  !(bv_eqb dst old)
  && (bv_unsigned dst % page_size == 0)
  && (0 < bv_unsigned dst)
  && (bv_unsigned dst + new_nZ ≤ alloc_top h)
  && region_free (h.vm_reserved ++ h.vm_maps) dst new_n
  && mremap_final_budget_b m old old_n dst new_n

/-- Staying at `old`: a shrink drops exactly the tail
`[addr+new_len, addr+old_len)` — the range `shrink_vma` (mm/mremap.c:1330,
:1337-1338, Linux v6.18.46) hands to `do_vmi_munmap` (mm/vma.c:1604, Linux
v6.18.46) — and a grow zero-fills exactly the delta. The shrink branch is a helper
contract only: `mremap_spec` declines it. Rocq: `Mremap.mremap_inplace_effect`. -/
def mremap_inplace_effect (old old_n new_n : word) (old_nZ new_nZ : Int) : SyscallEffect :=
  if new_nZ < old_nZ then
    SyscallEffect.mkEffectU old [] [] [(old + new_n, Z_to_bv 64 (old_nZ - new_nZ))] [] []
  else mkEffect old [] (mremap_tail old old_n old_nZ new_nZ)

/-- A move relocates the whole source: `move_ptes` (mm/mremap.c:193-315,
Linux v6.18.46) clears each source PTE (`get_and_clear_ptes`, :287) and
installs it at the destination (`set_ptes`, :300), so the same physical
pages appear at `dst`; untouched `pte_none` entries are skipped (:268-269)
and refault as zeroes through `do_anonymous_page` (mm/memory.c:5149, Linux
v6.18.46) for a PRIVATE|ANONYMOUS VMA.  Hence the copy length is the WHOLE source,
`old_n` — not `min old_n new_n`: a move only happens on growth, because
`mremap_at` serves `MREMAP_NO_RESIZE` and `MREMAP_SHRINK` in place
(:1558-1572) and only `MREMAP_EXPAND` reaches `expand_vma` (:1573-1574).

The source is then unmapped by `unmap_source_vma` (:1122), which is why the
copy source is inside `eff_unmaps`: `Run.apply_copies` reads the
PRE-EFFECT snapshot, matching the kernel's order.  The grown tail carries
no page tables — neither `copy_vma` nor `vma_merge_extend` installs any
for the delta — so it reads as fresh zeroes, which is `mremap_tail`.
Rocq: `Mremap.mremap_move_effect`. -/
def mremap_move_effect (old old_n dst : word) (old_nZ new_nZ : Int) : SyscallEffect :=
  SyscallEffect.mkEffectU dst [] (mremap_tail dst old_n old_nZ new_nZ) [(old, old_n)]
    [MemCopy.mkCopy old dst old_n] []

/-! ## The spec

`mremap old old_size new_size flags`, the bounded
`mremap(old, old_size, new_size, MREMAP_MAYMOVE)` shape musl's realloc
uses.  The source must be exactly one tracked readable/writable anonymous
mapping.  Equal-size and shrinking calls decline;
grow may extend into a free adjacent range; and MAYMOVE permits a fresh
disjoint placement that symbolically copies the preserved prefix, unmaps
the old range, and zero-fills only a grown tail.

ORDER, against `SYSCALL_DEFINE5(mremap)` (mm/mremap.c:1961-1994, Linux
v6.18.46), which fills a `vma_remap_struct` and calls `do_mremap`
(:1911-1952).  Which gate fires first is as much a part of the syscall as
its result, so the branches below are in the kernel's order:

1. `do_mremap` rounds BOTH lengths with the wrapping `PAGE_ALIGN`
   (:1917-1918) and then `check_mremap_params` (:1752-1820) validates the
   flags before any other argument is inspected (:1759-1760).  One read
   precedes it — `untagged_addr(addr)` in the syscall body (:1980) — but
   it cannot change an answer: riscv's `untagged_addr`
   (arch/riscv/include/asm/uaccess.h:31-34, Linux v6.18.46) strips
   `mm->context.pmlen` high bits under CONFIG_RISCV_ISA_SUPM and is the
   identity otherwise (:44), and `pmlen` is reset to 0 at exec
   (`activate_mm`, arch/riscv/include/asm/mmu_context.h:24, Linux v6.18.46)
   and set only by `set_tagged_addr_ctrl` (arch/riscv/kernel/process.c:285-346,
   Linux v6.18.46), which
   `prctl(PR_SET_TAGGED_ADDR_CTRL)` reaches and no modeled arm admits.
   (Even a nonzero `pmlen` moves only high bits, so the page test below is
   unaffected; what would move is the VMA lookup.)  A tagged `old`
   therefore keeps its tag into `vma_lookup` (:1931), where Linux answers
   -EFAULT while the model fails closed at `mremap_source_b` — the safe
   direction — and the flag test really is the first gate that can decide
   the answer.  The model's narrower shape (exactly `MREMAP_MAYMOVE`)
   fails closed first, ahead of the alignment and new-length declines below.  Linux
   answers a deterministic EINVAL for a flag word outside
   {FIXED, MAYMOVE, DONTUNMAP} and serves `flags = 0` on the very path
   MAYMOVE takes (no test before `expand_vma`'s move branch, :1535-1536,
   distinguishes the two: the earlier reads of `vrm->flags` — :1759,
   :1779, :1672-1676, :1696, :1928, :1937 — test only the mask, FIXED and
   DONTUNMAP); declining both is a deliberate narrowing, not a fidelity
   claim.
2. `offset_in_page(addr)` → -EINVAL (`check_mremap_params`, :1763-1764).
3. A rounded NEW length of zero → -EINVAL (:1771-1772).  So a `new_size` in
   the top partial page is -EINVAL, exactly like `new_size = 0`
   (`page_align_is0_b`); the model declines both because qemu-user can
   answer differently.
4. A rounded NEW length above `TASK_SIZE` → -EINVAL (:1775-1776) — the
   DECLARED DECLINE of the header, `unmodeled` here because Linux v6.12
   answered the MAYMOVE shape -ENOMEM instead.  `TASK_SIZE` is the Sv48
   `State.TASK_SIZE` the tree pins (arch/riscv/include/asm/pgtable.h:1081;
   `TASK_SIZE` is `TASK_SIZE_64` at :1088, or at :1085-1086 for a 64-bit
   task under CONFIG_COMPAT; `Checks/Cases/Uaccess.v`'s
   `task_size_is_the_sv48_top`).
5. A rounded OLD length of zero is the "duplicate a mapping" shape, which
   Linux refuses with -EINVAL for a private mapping in `check_prep_vma`
   (:1690-1694) — but only after `vma_lookup` (:1931), the seal check
   (:1662-1663), and only on the growth path (:1676-1677 returns 0 before
   it for a call that maps nothing new).  The model does not track enough
   to reproduce that -EINVAL's preconditions, so it fails closed; it does
   so HERE, after the alignment and new-length gates above.  `PAGE_ALIGN` wraps a
   near-`2^64` `old_size` to 0, so the wrap and the literal zero are the
   same case and share this gate.
6. `vma_lookup` (:1931) requires a VMA at `addr`, and nothing more on the
   equal-size and shrink paths: `check_prep_vma` returns 0 for them at
   :1676-1677 before `old_len` is ever compared against
   `vma->vm_end - addr` (:1720-1721).  An equal-size call therefore
   succeeds and returns `addr` even when `[addr, addr+old_len)` spans a
   hole, several VMAs, or runs off the end of the mapping — the only other
   requirements are that the VMA is unsealed (:1662-1663) and, for a
   hugetlb VMA, huge-page aligned (:1666-1667).  The model
   instead demands an exact tracked entry, a much larger narrowing than
   "not an exact entry" reads as; it is the safe direction (fail closed).

RESULTS.  `mremap_at` (:1550-1580) never moves for `old_len ≥ new_len`:
`MREMAP_NO_RESIZE` returns `addr` outright (:1558-1559), and
`MREMAP_SHRINK` returns `addr` once `shrink_vma` has dropped the tail
(:1568-1572, with the lock released inside `do_vmi_munmap`).  Growth is
the only case that can move, and `expand_vma` (:1512-1544) reaches the
move (:1535-1543) only after the in-place expansion behind
`vrm_can_expand_in_place` (:1520-1526) was not taken.

Linux's equal-size path carries NO injectable failure: from `do_mremap`'s lock
to `mremap_at`'s return the only exits on this shape are -EINTR
(:1924-1925), -EFAULT (:1658-1659), -EPERM (:1662-1663) and the hugetlb
-EINVAL (:1666-1667), all excluded by the modeled shape (`mremap_errnos`),
and there is no allocation, no split and no accounting on that branch.
The shrink arm is different: `do_vmi_munmap` splits the VMA and can fail
to allocate or exceed `sysctl_max_map_count` (`mremap_errnos`).

The choice between growing in place and moving is a genuine `alt`, because
Linux's in-place test reads state the model's ledger does not have:
`vma_expandable` (:1415-1427) consults the next VMA in the maple tree
(`find_vma_intersection`, :1421-1422) and the `MAP_FIXED` placement search
(`get_unmapped_area`, :1423-1425, whose `__get_unmapped_area`,
mm/mmap.c:812-864, Linux v6.18.46, tests `TASK_SIZE`, the alignment and
`security_mmap_addr` at :857-863); and `vrm_can_expand_in_place`
(:1436-1437) requires the
request to run exactly to the VMA's end, which a kernel-side merge can
defeat.  Any of those can send Linux to the move path where the model sees
free space, so the model admits both.  That argument does NOT apply to the
equal-size and shrink arms — they never reach `vma_expandable` — which is
why Linux keeps them in place; qemu-user relocates them, so they decline.

An injected ENOMEM leaves no memory effects: a `copy_vma` failure returns
before anything moved (`copy_vma_and_data`, :1193-1198); a short
`move_page_tables` moves the entries back and re-points the request at the
NEW area (:1208-1228), so what `unmap_source_vma` (:1312) then unmaps is
the destination and the source is left as it was, with the errno returned
at :1316.  The argument is specific to MAYMOVE: under `MREMAP_FIXED` the
destination is destroyed by `mremap_to` (:1363-1413) before the move, so
THAT errno does have memory effects.  FIXED is unmodeled.

BOUNDED APPROXIMATION, on the SUCCESS path.  `unmap_source_vma`'s
`do_vmi_munmap` (:1122) is best effort: when it fails its error is
SWALLOWED (:1125-1128, "OOM: unable to split vma, just get accounts right")
and `move_vma` returns `new_addr` at :1316.  So a successful Linux mremap
can leave the source range still mapped, at an address the program knows.
The model always emits `eff_unmaps [(old, old_n)]` and always drops `old`
from the ledger.  What makes it reachable is that Linux only requires
`old_len ≤ vma->vm_end - addr` (:1720-1721), so the model's exact ledger
entry can be a strict prefix of a merged kernel VMA that the unmap has to
split.  The cost is a fidelity gap, not a checker unsoundness — what the
ledger claims is FREE stays a superset of what is really free —
`bugs/mremap-maymove-answers-success.md` carries the bullet.

The fifth syscall argument is ignored: `vrm->new_addr` is read only under
`MREMAP_FIXED`/`MREMAP_DONTUNMAP` (`check_mremap_params`, :1779-1780,
returns before its tests, and `check_prep_vma`, :1672-1673, overwrites the
field with `addr` when no new address is implied) and inside the hugetlb
alignment (`align_hugetlb`), unreachable for one tracked anonymous
mapping.

Size rounding is done in `Int` and checked before conversion back to
`word`.  Protected/mixed/non-exact sources, FIXED, DONTUNMAP, and every
other flag combination fail closed. -/
def mremap_spec (old old_size new_size flags : word) : Sys SyscallEffect :=
  -- This gate declines TWO different kernel answers, and only one of them
  -- is a refusal: -EINVAL for a flag word outside {FIXED, MAYMOVE,
  -- DONTUNMAP} (`check_mremap_params`, mm/mremap.c:1759-1760, Linux
  -- v6.18.46) and the
  -- success `flags = 0` gets on the MAYMOVE path up to the move (:1535).
  -- Declining `flags = 0` is a deliberate narrowing, not a claim that
  -- Linux fails; `unmodeled` never asserts a wrong result.
  if !(bv_unsigned flags == MREMAP_MAYMOVE) then unmodeled
  /- QEMU 11.1.1 linux-user/mmap.c `target_mremap`:1194-1209
     reserves a fresh range with `mmap_find_vma` before host mremap with
     MREMAP_FIXED. A misaligned source can therefore get -ENOMEM before
     host -EINVAL; a new length rounding to zero gets -ENOMEM from the
     size-zero host mmap (`mmap_find_vma`:481-486). Equal and shrinking
     calls relocate or fail -ENOMEM. Linux v6.18.46 (commit
     1f99e9ab748fc5c32120de9c4eca31abfe54a4d5), mm/mremap.c
     `check_mremap_params`:1763-1772 gives the EINVALs, while `mremap_at`
     keeps equal/shrinking calls in place. Decline these four shapes.
     BOUND / ASSUMPTION: the unchanged grow set (in place | fresh move |
     -ENOMEM) contains qemu-user's answers (fresh move | -ENOMEM) only
     assuming a host with 4 KiB pages and no -R (reserved_va). With -R,
     `target_mremap`:1206-1208 unmaps the source even on host failure;
     on larger-page hosts `mmap_find_vma`:454 aligns to the host page
     and :463 rounds the allocation size; a 4K-aligned source can pass host -EINVAL through. Both remain open
     questions to the owner on #1426. See bugs/qemu-user-mremap-grow-host-page-and-reserved-va.md.
     Containment also requires the whole destination extent below alloc_top;
     qemu-user places bottom-up above its stack (QEMU 11.1.1
     linux-user/elfload.c:420, setup_arg_pages; linux-user/main.c:880, main),
     but Run.valid_sp already excludes its sp, so the theorems are unaffected.
     No theories/Examples program calls
     mremap, so these new declines are unreachable there and no
     strong_universal loses its modeled conjunct. -/
  else if !(bv_unsigned old % page_size == 0) then unmodeled
  else if page_align_is0_b new_size then unmodeled
  else if TASK_SIZE < page_round_up_Z (bv_unsigned new_size) then unmodeled  -- :1775-1776, declared
  else if page_align_is0_b old_size then unmodeled                  -- clone: :1690-1694
  else
    m <- get_model ;;
    let h := m_vmmaps m
    let old_nZ := page_round_up_Z (bv_unsigned old_size)
    let new_nZ := page_round_up_Z (bv_unsigned new_size)
    let old_n := Z_to_bv 64 old_nZ
    let new_n := Z_to_bv 64 new_nZ
    if !(mremap_source_b h old old_n old_nZ && mremap_backing_uniform_b m old old_n)
    then unmodeled                                                  -- :1931, :1658-1659
    else if new_nZ ≤ old_nZ then unmodeled
    else
      alt
        (e <- errno_from mremap_errnos ;; err_ret e)
        (let move : Sys SyscallEffect :=
             (dst <- choose (fun dst =>
                mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) ;;
              modify (fun _ => mremap_model_next m old old_n dst new_n) ;;
              Monad.pure (mremap_move_effect old old_n dst old_nZ new_nZ))
           if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ then
             alt
               (modify (fun _ => mremap_model_next m old old_n old new_n) ;;
                Monad.pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ))
               move
           else move)

/-! ## The budget mark for mremap

See the Rocq `Mmap.brk_budget_refused_b` for what a mark is.  The Rocq
`mremap_move_charge` and `mremap_budget_refused_b` notes carry the
argument in full; what is kept here is the shape. -/

/-- THE MOVE'S CHARGE, WITH THE DESTINATION FACTORED OUT.  A grow's budget
gate is `mremap_final_budget_b` on the complete post-state, and the moved
resolution's post-state depends on the destination the `choose` picks —
which the mark, reading only the request and the state, does not have.  At
a destination that is FRESH — disjoint from every live mapping and carrying
no protected bytes, no lazy reservation and no materialized page — the
re-created mapping is charged in full when the source is eager and not at
all when it is lazy (its materialized pages move with it and are charged
by count), and nothing else in the post-state mentions the destination.  So
the charge is one number for every fresh destination, and this is that
number, written out of the same pieces `State.vm_resize_backing` assembles.
The Rocq lemma `mremap_move_charge_at_fresh` proves it equal to the gate's
reading at any destination of that shape.  Rocq: `Mremap.mremap_move_charge`. -/
def mremap_move_charge (m : Model) (old old_n new_n : word) : Int :=
  let h := m_vmmaps m
  let old_lo := bv_unsigned old
  let old_hi := old_lo + bv_unsigned old_n
  let source_lazy := mremap_source_lazy_b m old old_n
  let kept_lazy := maps_subtract (m_vm_lazy m) old_lo old_hi
  let kept_pages := (m_vm_materialized m).filter (page_outside_range old_lo old_hi)
  let moved_pages :=
    if source_lazy then
      (m_vm_materialized m).filter
        (fun p => page_in_half_open old_lo old_hi p && bv_unsigned p - old_lo < bv_unsigned new_n)
    else []
  live_bytes
      (maps_subtract_all (maps_subtract_all (map_remove h.vm_maps old) h.vm_noaccess) kept_lazy)
    + (if source_lazy then 0 else bv_unsigned new_n)
    + ((moved_pages.length + kept_pages.length : Nat) : Int) * page_size

/-- The move's budget gate, destination-free: the same comparison
`State.vm_backing_within_limit` makes, on the charge above.
Rocq: `Mremap.mremap_move_budget_b`. -/
def mremap_move_budget_b (m : Model) (old old_n new_n : word) : Bool :=
  mremap_move_charge m old old_n new_n ≤ (m_vmmaps m).vm_limit

/-- Only a GROW charges, and a grow has both resolutions, each behind its
own reading of `mremap_final_budget_b`: in place, on the mapping grown at
`old`, and moved, on the mapping re-created at a fresh destination.  THE
MARK FIRES WHEN EITHER GATE REFUSES — it tests the larger of the charges,
the in-place post-state's directly and the move's through
`mremap_move_budget_b` — because neither post-state is charged at least as
much as the other on every state: a lazy neighbour makes the in-place
post-state dearer and a PROT_NONE neighbour makes it cheaper (the charge
subtracts `vm_noaccess`).  So the mark is at least as strong as either
resolution's refusal and never weaker, and over-marks where the in-place
gate refuses while a move fits — the safe direction for a premise.
Shrinks, equal-size calls, and every shape the arm declines
— the declared `TASK_SIZE` decline included — are not budget
refusals.  Rocq: `Mremap.mremap_budget_refused_b`. -/
def mremap_budget_refused_b (old old_size new_size flags : word) (m : Model) : Bool :=
  if !(bv_unsigned flags == MREMAP_MAYMOVE) then false
  else if !(bv_unsigned old % page_size == 0) then false
  else if page_align_is0_b new_size then false
  else if TASK_SIZE < page_round_up_Z (bv_unsigned new_size) then false
  else if page_align_is0_b old_size then false
  else
    let h := m_vmmaps m
    let old_nZ := page_round_up_Z (bv_unsigned old_size)
    let new_nZ := page_round_up_Z (bv_unsigned new_size)
    let old_n := Z_to_bv 64 old_nZ
    let new_n := Z_to_bv 64 new_nZ
    if !(mremap_source_b h old old_n old_nZ && mremap_backing_uniform_b m old old_n) then false
    else if new_nZ ≤ old_nZ then false
    else !(mremap_final_budget_b m old old_n old new_n && mremap_move_budget_b m old old_n new_n)


end LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap
