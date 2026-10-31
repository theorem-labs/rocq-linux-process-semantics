import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
divergence: bugs/brk-grow-ignores-stack-guard-gap.md -- inherited
divergence: bugs/grants-into-the-stack-band.md -- inherited
divergence: bugs/live-bytes-double-counts-overlapping-entries.md -- inherited
divergence: bugs/mmap-placement-admits-unreachable-addresses.md -- inherited
divergence: bugs/vm-limit-environment-obligation.md -- inherited -/

/-! # LinuxProcessSem.Sys.Mm.Mmap — brk (214), mmap (222), munmap (215)

Mirrors `theories/LinuxProcessSem/Sys/Mm/Mmap.v`, which answers to Linux
`mm/mmap.c`.  Which file a spec belongs in is the kernel's choice, not a
judgement call (the Rocq header's placement rule; `Specs.v` carries the
whole map): `brk`, `mmap` and `munmap` are defined there and live here, and
`remap_file_pages` (234), also defined there, has no arm anywhere and the
table declines it.

TRUST BOUNDARY: this file is part of the trusted specification.

The docstrings carry the kernel citation each decision rests on — file,
function, and the line numbers at Linux v6.18.46 (commit 1f99e9ab748f)
unless a v6.12 pin is named — and point at the Rocq definition for the
argument in full, so there is one place to correct it.

Two spellings differ from Rocq without changing a value: bit tests on the
flags word are done on the `word` (`bv_and`) where Rocq does them on
`bv_unsigned` in `Z` (`Z.land`, `Z.ldiff`) — the constants are below
`2^64`, so the two agree — and the `Z.leb`/`Z.ltb`/`Z.eqb` Bool tests are
Lean's decidable `≤`/`<`/`=` on `Int`.  Rocq's `fold_left` is `List.foldl`
with the arguments in Lean's order, and a `Fixpoint` is a structural `def`.

ANONYMOUS MEMORY IS ZERO-BACKED, as on Linux: a successful grant carries
the granted region in `eff_zeros`, and `Run.apply_effect` materializes it as
zeros in the writable overlay.  Every grant is disjoint from the binary
image and from THIS run's stack (`State.alloc_top`); it is NOT disjoint from
every other live allocation in the byte-granular `brk` corner the Rocq
header describes. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! ## brk (214)

`brk req` models the raw Linux `SYSCALL_DEFINE1(brk)` (mm/mmap.c:115-213,
Linux v6.18.46), which NEVER returns `-errno`: the new break on success
(:207), and the CURRENT break UNCHANGED on any failure — `out:` restores
and returns `origbrk` (:209-212).  The one errno in the function, the
-EINTR of `mmap_write_lock_killable` (:125-126), reaches only a task a
fatal signal is already killing, which never reads it.  Three paths, each
keyed on the request against `min_brk` and the tracked break, and each
with the resolutions the kernel really produces: QUERY / INVALID
(`brk < min_brk`, :140-141, the path `sbrk(0)` takes), GROW (:180-197) and
SHRINK (:161-178), both of which may also answer the old break.  The
argument for each — and for the break base being a quantified parameter
of the run, established from the first instruction on — is on the Rocq
header of `theories/LinuxProcessSem/Sys/Mm/Mmap.v`; the docstrings below
keep the citation each decision rests on.  Rounding stays in `Int` over
unsigned values, as in Rocq: a page round-up near `2^64` must not wrap
into a small number.

`SYSCALL_DEFINE1(brk)` is at mm/mmap.c:115-213 at the pin; the Rocq
comments still quote the early exit as mm/mmap.c:156-161 and the shrink
block as :164-181, which are v6.12 numbers. -/

/-- The lowest legal break.  Linux's `min_brk` is `mm->start_brk`
(`SYSCALL_DEFINE1(brk)`, mm/mmap.c:130, Linux v6.18.46): the ASLR-placed
heap base itself, `vm_start_brk`, set at execve.  A request below it — the
ASLR gap between the image top and the base included — returns the break
unchanged with no state change (:140-141).  This is the randomised reading:
the `CONFIG_COMPAT_BRK` branch that lowers `min_brk` to `mm->end_data`
while `brk_randomized` is clear (:131-139) is not carried, and on that
configuration with brk randomisation off a request between `end_data` and
`start_brk` is invalid here where Linux honours it —
bugs/brk-min-brk-assumes-a-randomised-break.md. -/
def min_brk (h : VmMaps) : word := h.vm_start_brk

/-- Whether a brk resolution actually GREW the break: a real move
(`req ≠ 0`) from an established break (`0 < old`) to a resolution `r`
strictly above it.  Both grow effects, `brk_grants` and `brk_zeros`, are
gated on this one test so they cannot drift apart.  The first two conjuncts
are redundant given `brk_r_ok` — a query resolves to `r = old`, and
`old ≥ min_brk > 0` for any real image — and kept so that both effects
stay gated on the path that may grow, as the Rocq definition says.  Rocq:
`negb (w_is0 req) && Z.ltb 0 (bv_unsigned old) && Z.ltb (bv_unsigned old)
(bv_unsigned r)`. -/
def brk_is_grow (req r old : word) : Bool :=
  !(w_is0 req) && 0 < bv_unsigned old && bv_unsigned old < bv_unsigned r

/-- The byte-granular grant ledger of a brk transition: exactly a GROW
SUCCESS from `old` up to `r` owns `[old, r)`; every other case owns
nothing.  Byte-granular where `brk_zeros` is page-granular, on purpose:
Linux moves `mm->brk` by the byte (`SYSCALL_DEFINE1(brk)`, mm/mmap.c:197,
Linux v6.18.46) and installs page-rounded memory (:153-154, :194-195), and
the logical range here is what makes `vm_backing_used` charge exactly the
requested growth.  `r - old` cannot wrap: `brk_is_grow` has `old < r`
unsigned. -/
def brk_grants (req r old : word) : List (word × word) :=
  if brk_is_grow req r old then [(old, r - old)] else []

/-- A nonempty half-open `[lo, hi)` in unbounded address arithmetic, in the
effect/ledger `(base, length)` spelling; empty when `lo ≥ hi`.  Both brk
directions round through this one helper so their page rounding cannot
drift apart.  Admissible brk transitions keep both endpoints below
`alloc_top`, so the conversion back to 64-bit words is lossless. -/
def brk_page_range (lo hi : Int) : List (word × word) :=
  if lo < hi then [(Z_to_bv 64 lo, Z_to_bv 64 (hi - lo))] else []

/-- The zero-fill VISIBLE to the process after a brk GROW SUCCESS: exactly
the newly installed pages `[PAGE_ALIGN(old), PAGE_ALIGN(r))`.
`SYSCALL_DEFINE1(brk)` rounds both breaks (mm/mmap.c:153-154, Linux
v6.18.46), takes the `oldbrk == newbrk` exit installing nothing when they
agree (:155-158), and otherwise hands `do_brk_flags` (mm/vma.c:2805) the
interval `[oldbrk, newbrk)` (:194-195).  So a grow within the already
mapped final page exposes no new bytes, and shrinking and regrowing inside
one page preserves its old contents. -/
def brk_zeros (req r old : word) : List (word × word) :=
  if brk_is_grow req r old
  then brk_page_range (page_round_up_Z (bv_unsigned old)) (page_round_up_Z (bv_unsigned r))
  else []

/-- The pages a brk transition FREES: a SHRINK from `old` down to `r`
releases exactly `[PAGE_ALIGN(r), PAGE_ALIGN(old))`.  `SYSCALL_DEFINE1(brk)`'s
shrink block hands `do_vmi_align_munmap` (mm/vma.c:1557) the interval
`[newbrk, oldbrk)` (mm/mmap.c:161-178, Linux v6.18.46), which tears the PTEs
down for real — a later re-grow of the same addresses hands back fresh
zeroes.  EMPTY when the two breaks round to the same page: the
`oldbrk == newbrk` exit (:155-158) frees nothing on a sub-page shrink.
Every other resolution (query/invalid, and grow, which keep `old ≤ r`)
frees nothing either.  The mirror image of `brk_zeros`, with the arithmetic
in `Int`.  Under the guard `lo` is below `2^64` and `hi - lo ≤ 2^64 - lo`,
so both re-enter `word` losslessly; the one corner that would not (`lo = 0`
with `hi = 2^64`) needs `r = 0`, which no `brk_r_ok` resolution admits once
the break is established, as the Rocq definition argues.  The `0 < old`
guard itself is Rocq's and decides nothing on its own — with `old = 0` the
range is already empty (`hi = 0`) — it is kept so that the unestablished
break stays visibly ungated, as `brk_grow_ok`'s guard does. -/
def brk_unmaps (r old : word) : List (word × word) :=
  let lo := page_round_up_Z (bv_unsigned r)
  let hi := page_round_up_Z (bv_unsigned old)
  if 0 < bv_unsigned old then brk_page_range lo hi else []

/-- The budget conjunct of a brk grow, ONE definition read by `brk_grow_ok`
(and by the budget mark `brk_budget_refused_b` below):
the grow's byte delta `r - vm_brk` must fit the backing still unspent.
Byte-granular, like the ledger entry a grow records.  Linux's counterpart
is the commit charge `do_brk_flags` takes for the new pages
(`do_brk_flags`, mm/vma.c:2805-2823, Linux v6.18.46, refusing with -ENOMEM
through `may_expand_vm`, mm/mmap.c:1324, and `security_vm_enough_memory_mm`,
security/security.c:1289), on which `SYSCALL_DEFINE1(brk)` answers the old
break (mm/mmap.c:194-195). -/
def brk_budget_ok (m : Model) (r : word) : Bool :=
  let h := m_vmmaps m
  vm_backing_used m + bv_unsigned (r - h.vm_brk) ≤ h.vm_limit

set_option linter.unusedVariables false in
/-- The GROW gate: when `r` is strictly above the break, the physical pages
newly installed — `[PAGE_ALIGN(vm_brk), PAGE_ALIGN(r))` — must lie below
`alloc_top`, and they AND THE ONE PAGE ABOVE THEM must be disjoint from the
image and every live mapping.  `SYSCALL_DEFINE1(brk)` (mm/mmap.c, Linux
v6.18.46), after `check_brk_limits` (:180-181; it tests nothing against
other mappings: its `get_unmapped_area(NULL, oldbrk, len, 0, MAP_FIXED)`
hands `oldbrk` straight back unless `newbrk > TASK_SIZE` or
`security_mmap_addr(oldbrk)` objects (`__get_unmapped_area`, mm/mmap.c:812-864,
Linux v6.18.46),
and `mlock_future_ok` adds an -EAGAIN only with `VM_LOCKED` in `def_flags`,
:103-113 — each a `goto out` answering the old break like every refusal
below) and before `do_brk_flags`:

    vma_iter_init(&vmi, mm, oldbrk);
    next = vma_find(&vmi, newbrk + PAGE_SIZE + stack_guard_gap);
    if (next && newbrk + PAGE_SIZE > vm_start_gap(next))
            goto out;

(:187-190).  `vma_find(&vmi, max)` is `mas_find(&vmi->mas, max - 1)`
(include/linux/mm.h:1024-1027, Linux v6.18.46), the first VMA meeting
`[oldbrk, max)`, and `vm_start_gap` (include/linux/mm.h:3716-3725, same
version) is `vm_start` itself for a VMA that is neither `VM_GROWSDOWN` nor `VM_SHADOW_STACK`
(`stack_guard_start_gap`, :3704-3714).  So for an ordinary mapping the
test refuses exactly when the mapping meets `[oldbrk, newbrk + PAGE_SIZE)`,
the pages being installed and one more, and answers the OLD break
(:209-212).  A same-page grow has no physical interval and is not subject
to it: the `oldbrk == newbrk` exit (:155-158) sits before every VMA test,
so such a grow enters `vm_maps` with no address-space test at all — what
Linux does, not a hole; the Rocq definition carries that argument and the
v6.5–v6.18 history of the prologue.  The budget conjunct is LOGICAL,
`r - vm_brk` bytes, so the deterministic out-of-memory point of issue #131
does not move.  For the stack `vm_start_gap` subtracts `stack_guard_gap`
(mm/mmap.c:941, 256 pages unless the command line says otherwise); the
model has no stack VMA, `alloc_top` stands in, and
bugs/brk-grow-ignores-stack-guard-gap.md records the premise.  `req` is a
parameter for the Rocq signature's sake and is not read. -/
def brk_grow_ok (m : Model) (req r : word) : Bool :=
  let h := m_vmmaps m
  if 0 < bv_unsigned h.vm_brk && bv_unsigned h.vm_brk < bv_unsigned r
  then let lo := page_round_up_Z (bv_unsigned h.vm_brk)
       let hi := page_round_up_Z (bv_unsigned r)
       (if lo < hi
        then hi ≤ alloc_top h
             && region_free (h.vm_reserved ++ h.vm_maps)
                            (Z_to_bv 64 lo) (Z_to_bv 64 (hi + page_size - lo))
        else true)
       && brk_budget_ok m r
  else true

/-- May the kernel report resolved break `r` for `brk req` under model `m`?
The three Linux paths, keyed on the request against `min_brk` and the
tracked break `b` (`SYSCALL_DEFINE1(brk)`, mm/mmap.c, Linux v6.18.46):
QUERY / INVALID, `req = 0` or `req < min_brk` (:140-141), answers `b`
unchanged; SHRINK, `req < b`, answers `req` or `b` — a shrink can fail when
`vma_find` from `newbrk` meets no VMA below `oldbrk` at all (`!brkvma`,
:164-166: a VMA it does meet, the heap's or a foreign one, is handed to
`do_vmi_align_munmap` and unmapped, and the `vm_start >= oldbrk` disjunct
cannot hold for what `vma_find(&vmi, oldbrk)` returns), or when
`do_vmi_align_munmap` fails (:173-175), each a `goto out`; and above the
same-page exit `check_data_rlimit` (:149-151) refuses any request once
another process has lowered this task's `RLIMIT_DATA` with `prlimit64`,
which no arm here models; GROW answers `req` under
`brk_grow_ok`, or `b` (:180-195, each refusal a `goto out`).  `req = b` is
a grow that installs nothing and answers `b` either way. -/
def brk_r_ok (m : Model) (req r : word) : Bool :=
  let h := m_vmmaps m
  let b := h.vm_brk
  if w_is0 req || bv_unsigned req < bv_unsigned (min_brk h) then
    bv_eqb r b
  else if bv_unsigned req < bv_unsigned b then
    bv_eqb r req || bv_eqb r b
  else
    (bv_eqb r req || bv_eqb r b) && brk_grow_ok m req r

/-- The `vm_maps` ledger after resolving to break `r`.  A GROW SUCCESS
records the granted interval, so a later mmap can never alias the live
heap (the converse fails: a grow inside one page is gated on nothing, see
`brk_grow_ok`).  A SHRINK drops the logical tail `[r, b)` through
`maps_subtract`, dropping heap grants inside it while sparing higher
anonymous mmaps; every other resolution leaves `vm_maps` untouched.
Byte-granular on purpose even though `brk_zeros`/`brk_unmaps` describe the
page-rounded memory effects (the Rocq definition's argument). -/
def brk_maps_next (h : VmMaps) (req r : word) : List (word × word) :=
  if 0 < bv_unsigned h.vm_brk && bv_unsigned r < bv_unsigned h.vm_brk
  then maps_subtract h.vm_maps (bv_unsigned r) (bv_unsigned h.vm_brk)
  else brk_grants req r h.vm_brk ++ h.vm_maps

/-- Apply exactly the page ranges named by a brk unmap effect to a mapping
overlay.  `brk_unmaps` is empty or a singleton today; a fold keeps the
`vm_noaccess` subtraction tied to the effect if that changes.  Each range
is a `(base, length)` pair, so the end is recovered in `Int` — a `word` sum
could wrap at `2^64` and hand `maps_subtract` a range ending at 0, which
subtracts nothing.  Rocq's `fold_left f ranges maps` is `List.foldl f maps
ranges`. -/
def maps_subtract_ranges (maps ranges : List (word × word)) : List (word × word) :=
  ranges.foldl
    (fun acc p => maps_subtract acc (bv_unsigned p.1) (bv_unsigned p.1 + bv_unsigned p.2))
    maps

/-- The ledger after a brk resolution: `brk_maps_next` for ownership, the
freed pages cut out of `vm_noaccess`, the break at `r`, everything else
kept. -/
def brk_model_next (h : VmMaps) (req r : word) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved (brk_maps_next h req r)
    (maps_subtract_ranges h.vm_noaccess (brk_unmaps r h.vm_brk))
    h.vm_start_brk r h.vm_limit h.vm_mmap_base h.vm_init_sp

/-- Forget the lazy and materialized backing of each range in turn: the
freed pages of a shrink give their first-touch charges back, as the pages
themselves go.  Rocq's `Fixpoint`, structural on the list. -/
def forget_vm_ranges (ranges : List (word × word)) (m : Model) : Model :=
  match ranges with
  | [] => m
  | (a, n) :: rest =>
      forget_vm_ranges rest
        (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)

/-- The whole post-state of a brk resolution: the ledger of
`brk_model_next`, then the backing of the freed pages forgotten. -/
def with_brk_next (m : Model) (req r : word) : Model :=
  let h := m_vmmaps m
  forget_vm_ranges (brk_unmaps r h.vm_brk)
    (with_vmmaps (brk_model_next h req r) m)

/-- `brk req`: the kernel resolves the break to some `r` that `brk_r_ok`
admits, the model moves to `with_brk_next`, and the effect carries `r` as
the return, the newly installed pages as zeroes and the released pages as
unmaps (`SYSCALL_DEFINE1(brk)`, mm/mmap.c:115-213, Linux v6.18.46).  No
errno arm: the function returns a break on every path (:207, :212). -/
def brk_spec (req : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let h := m_vmmaps m
  r <- choose (fun r => brk_r_ok m req r = true) ;;
  modify (fun _ => with_brk_next m req r) ;;
  Monad.pure (SyscallEffect.mkEffectU r [] (brk_zeros req r h.vm_brk)
                (brk_unmaps r h.vm_brk) [] [])

/-! ## The budget mark for brk

See the Rocq `Mmap.brk_budget_refused_b` for what a mark is: a function of
the PRE-state and the request, never of the answer drawn, that is `true`
exactly where the arm's own budget gate refuses the only success
resolution and nothing but a refusal remains.  `Run.alloc_budget_refused_b`
dispatches 214 to it, and `tools/check_budget_marks.py` counts
`brk_budget_ok`'s uses in this file against its uses here.  For brk the
mark fires on a real request (`req ≠ 0`, at or above `min_brk`) that GROWS
the break from an established one and whose byte delta does not fit; a
query, an invalid address, a shrink, a grow from an unestablished break
(which `brk_grow_ok` does not gate) and a grow that fits are not budget
refusals, whatever the answer.  `brk_r_ok` then allows only `r = vm_brk`;
the mark's soundness is `Checks/BudgetPremise.v`'s, whose Lean twin is
ticket K10. -/
def brk_budget_refused_b (m : Model) (req : word) : Bool :=
  let h := m_vmmaps m
  !(w_is0 req || bv_unsigned req < bv_unsigned (min_brk h))
  && 0 < bv_unsigned h.vm_brk
  && bv_unsigned h.vm_brk < bv_unsigned req
  && !(brk_budget_ok m req)

/-- Anonymous mmap fails only for lack of memory / address space. -/
def mmap_errnos : List Int := [ENOMEM]

/-- `MAP_NORESERVE` (include/uapi/asm-generic/mman.h:11, Linux v6.12).  It
changes only Linux's commit accounting, and only outside strict overcommit
(`do_mmap`, mm/mmap.c, Linux v6.12: the bit becomes `VM_NORESERVE` when
`sysctl_overcommit_memory != OVERCOMMIT_NEVER`).  The model always honors
it — it describes overcommit modes 0 and 1 — and records such a mapping as
LAZY: each page consumes `vm_limit` only on its first successful access.
The mode condition is part of the environment obligation
bugs/vm-limit-environment-obligation.md states. -/
def MAP_NORESERVE : Int := 16384          -- 0x4000

/-- The flags word with `MAP_NORESERVE` and ONLY `MAP_NORESERVE` removed:
what the shape predicates below match on.  Masking the bit out of the
shape match is the conservative direction — it selects the lazy LEDGER and
leaves every errno, placement and effect gate identical — and the bit is
read back by `mmap_noreserve_b` at the one place it changes an answer.
Rocq: `Z.ldiff (bv_unsigned flags) MAP_NORESERVE`. -/
def mmap_flags_core (flags : word) : Int :=
  bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 MAP_NORESERVE)))

/-- Is `MAP_NORESERVE` set?  Rocq: `Z.land (bv_unsigned flags) MAP_NORESERVE ≠ 0`. -/
def mmap_noreserve_b (flags : word) : Bool :=
  !(bv_unsigned (bv_and flags (Z_to_bv 64 MAP_NORESERVE)) == 0)

/-- Record a fresh grant's backing: lazy under `MAP_NORESERVE`, eager
otherwise. -/
def with_mmap_backing (flags a n : word) (m : Model) : Model :=
  if mmap_noreserve_b flags then vm_add_lazy a n m else m

/-- A replacement first forgets every lazy or materialized entry in the
range, then records the new backing. -/
def with_mmap_replacement (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n
    (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)

/-- A fixed mapping's destructive failure and `munmap` share the same
lifecycle transition: the ownership/no-access ledgers change and every lazy
or materialized entry in the removed range is forgotten. -/
def with_mmap_destroyed (a n : word) (h' : VmMaps) (m : Model) : Model :=
  vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
    (with_vmmaps h' m)

/-- `-1`: the `fd` a caller conventionally passes with `MAP_ANONYMOUS`.  No
shape below requires it — `ksys_mmap_pgoff` (mm/mmap.c, Linux v6.18.46)
resolves a file only inside `if (!(flags & MAP_ANONYMOUS))` and never reads
`fd` on the anonymous arm, so `mmap(NULL, 4096, rw, MAP_PRIVATE|MAP_ANONYMOUS,
3, 0)` succeeds on Linux for ANY `fd`.  The constant stays because the
worked examples name it. -/
def mmap_fd_none : word := Z_to_bv 64 (-1)

/-- Is `MAP_ANONYMOUS` set?  The ONE bit that decides whether Linux
resolves `fd` at all — `ksys_mmap_pgoff` (mm/mmap.c, Linux v6.18.46) opens
with `if (!(flags & MAP_ANONYMOUS)) { audit_mmap_fd(fd, flags); file =
fget(fd); if (!file) return -EBADF; …` (:573-577) — so it gates the file-backed branch of `mmap_spec`.  With the
bit clear the `fget` happens first whatever else the flags word carries,
`MAP_HUGETLB` included. -/
def mmap_anon_b (flags : word) : Bool :=
  !(bv_unsigned (bv_and flags (Z_to_bv 64 MAP_ANONYMOUS)) == 0)

/-- Is `off` page-aligned?  riscv answers -EINVAL when it is not, BEFORE
any generic mm code runs — before the flags are read, before `fget`, before
`do_mmap`'s zero-length check: `riscv_sys_mmap`
(arch/riscv/kernel/sys_riscv.c, Linux v6.18.46) returns -EINVAL on
`offset & (~PAGE_MASK >> page_shift_offset)`, and `__NR_mmap` (222) enters
it with `page_shift_offset` zero, so the mask is exactly `PAGE_SIZE - 1`.
Argument-only: no model state is consulted, which is why `mmap_spec` can
answer it first.  That order is Linux's: qemu-user reads the flags word
before anything else (`do_mmap`, linux-user/syscall.c:6164-6186,
QEMU 11.1.1) and answers -EOPNOTSUPP for a MAP_SHARED_VALIDATE word
carrying a bit outside its legacy set, MAP_FIXED_NOREPLACE among them,
where this gate proves -EINVAL:
bugs/mmap-shared-validate-refuses-qemu-user-eopnotsupp.md. -/
def mmap_off_aligned_b (off : word) : Bool :=
  bv_unsigned off % page_size == 0

/-- Does `PAGE_ALIGN(len)` stay inside an `unsigned long`?  The kernel
rounds in machine arithmetic, so a `len` within a page of `2^64` rounds to
ZERO and `do_mmap` answers -ENOMEM (`len = PAGE_ALIGN(len); if (!len)
return -ENOMEM;`, mm/mmap.c).  The model rounds in `Int`, so the condition
is spelled out.

It guards the misaligned-offset -EINVAL for a reason that is not about
Linux: QEMU's user-mode emulation (`target_mmap`, linux-user/mmap.c,
QEMU 11.1.1: `len = TARGET_PAGE_ALIGN(len); if (!len || …) errno = ENOMEM`
comes before `if (offset & ~TARGET_PAGE_MASK) errno = EINVAL`) checks the
length FIRST and answers -ENOMEM where the pinned kernel answers -EINVAL — measured, `mmap(0, (size_t)-1, PROT_READ, MAP_PRIVATE, 999, 1)`.
AGENTS.md counts qemu-user among the supported implementations, so proving
-EINVAL there would prove a behaviour outside their intersection; the
decline costs coverage, never soundness. -/
def mmap_pglen_ok_b (len : word) : Bool :=
  page_round_up_Z (bv_unsigned len) < two_pow_64

/-- The PLAIN anonymous shape — `MAP_ANONYMOUS` set, `MAP_HUGETLB` clear:
the only flag class on which the model ANSWERS `do_mmap`'s `if (!len)
return -EINVAL` (mm/mmap.c:347-348, Linux v6.18.46).  The -EINVAL is not
this shape's alone.  `ksys_mmap_pgoff` inspects the flags before the
length: with `MAP_ANONYMOUS` clear it `fget`s first (:573-577) — -EBADF
for a closed fd, -EINVAL at `ksys_mmap_pgoff`'s own :580-582 for a live
non-hugetlb file with `MAP_HUGETLB` set, and for a live non-hugetlb file
without it a fall-through to the same :347-348 -EINVAL on the pinned
configuration: `vm_mmap_pgoff`
(mm/util.c:575-577, Linux v6.18.46) runs the LSM and fsnotify permission
hooks between the two, and both answer 0 there — `security_mmap_file` is the
`CONFIG_SECURITY`-less stub (include/linux/security.h:1173-1177) and
`fsnotify_mmap_perm` is the `CONFIG_FANOTIFY_ACCESS_PERMISSIONS`-less stub
(include/linux/fsnotify.h:221-225, Linux v6.18.46; the real body, :174-184,
returns 0 for a file with no HSM watcher) — and with `MAP_HUGETLB` set it is `hstate_sizelog`
/ `hugetlb_file_setup` (:584-601), whose errors are returned as is.  Both
are `unmodeled` here, the file-backed class because this arm never reads
the fd table (`mmap_fd_none`) and so cannot tell the two answers apart.  INSIDE the plain shape the -EINVAL holds whatever
`addr`, `prot` or `off` say: nothing before :347 looks at them, and
`MAP_TYPE` is validated only at :539-540.  That is Linux's order;
qemu-user validates `MAP_TYPE` first and answers some MAP_SHARED_VALIDATE
words -EOPNOTSUPP here, which
bugs/mmap-shared-validate-refuses-qemu-user-eopnotsupp.md records. -/
def mmap_plain_anon_b (flags : word) : Bool :=
  !(bv_unsigned (bv_and flags (Z_to_bv 64 MAP_ANONYMOUS)) == 0)
  && (bv_unsigned (bv_and flags (Z_to_bv 64 MAP_HUGETLB)) == 0)

/-! ## The modeled argument shapes

Each is a test on `(prot, flags, off)` with `MAP_NORESERVE` masked out of
`flags` and `off` pinned to 0; the two MAP_FIXED_NOREPLACE shapes follow
the budget gates, in their own section, as in Rocq.  `fd` is not part of any shape (see
`mmap_fd_none`).  A page-aligned NONZERO `off` is an ordinary success on
Linux for an anonymous mapping — `__get_unmapped_area` zeroes the page
offset it places with (mm/mmap.c:838-840, Linux v6.18.46) and `do_mmap` resets the one the
VMA records (:533-538) — and `unmodeled` here: still a narrowing, and a
smaller one than it was.  A non-NULL `addr` without `MAP_FIXED` is a hint
the kernel may honor or ignore, and the nondeterministic placement covers
both. -/

/-- The ordinary rw shape: PRIVATE ANONYMOUS READ+WRITE at offset 0. -/
def mmap_modeled_b (prot flags off : word) : Bool :=
  (bv_unsigned prot == PROT_READ + PROT_WRITE)
  && (mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS)
  && w_is0 off

/-- A fresh inaccessible anonymous reservation — musl's mallocng after a
failed brk, or a sanitizer runtime reserving its shadow up front. -/
def mmap_noaccess_b (prot flags off : word) : Bool :=
  (bv_unsigned prot == PROT_NONE)
  && (mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS)
  && w_is0 off

/-- The MAP_FIXED PROT_NONE shape: a guard page punched into something
owned, or a fresh inaccessible reservation naming its own address. -/
def mmap_fixed_noaccess_b (prot flags off : word) : Bool :=
  (bv_unsigned prot == PROT_NONE)
  && (mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)
  && w_is0 off

/-- The MAP_FIXED rw shape: the COMMIT half of the reserve-then-commit
idiom, or a grant naming its own address.  This shape makes memory MORE
reachable — it hands back readable zeroes — so its containment gate
(`map_contains` on `vm_maps`) is the one `mprotect` uses before exposing
zeroes, and for the same reason. -/
def mmap_fixed_rw_b (prot flags off : word) : Bool :=
  (bv_unsigned prot == PROT_READ + PROT_WRITE)
  && (mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)
  && w_is0 off

/-! ## Post-states

`maps_subtract` is exactly `__split_vma`'s effect on the model's intervals:
it keeps the parts of each entry outside the cut, splitting a straddling
entry into a left and a right remnant.  The CONTAINED arms do not re-cut
`vm_maps` — a contained request leaves Linux's VMA whole apart from the
splits, and re-cutting the model's entry would fragment a tracked
allocation that is still one allocation, narrowing `map_contains` on a
later call (the argument is on the Rocq "MAP_FIXED THAT SPANS" section). -/

/-- After a successful contained rw MAP_FIXED: ownership untouched, the
committed slice removed from `vm_noaccess`. -/
def mmap_fixed_rw_next (h : VmMaps) (addr n : word) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps
    (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp

/-- The ledger a DESTRUCTIVE MAP_FIXED failure leaves: the request's range
gone from both ledgers and nothing in its place.  `vms_abort_munmap_vmas`
writes NULL over exactly `[vms->start, vms->end)` (mm/vma.c:2365-2366,
Linux v6.18.46), so the split remnants outside the request survive — which
is why this is `maps_subtract` over the request rather than the removal of
whole entries. -/
def mmap_fixed_destroyed_next (h : VmMaps) (addr n : word) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved
    (maps_subtract h.vm_maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp

/-- After a successful rw MAP_FIXED that SPANS: the request owned and
accessible, every entry it meets re-cut around it. -/
def mmap_fixed_rw_span_next (h : VmMaps) (addr n : word) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved
    ((addr, n) :: maps_subtract h.vm_maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp

/-- …and after a PROT_NONE one: owned and inaccessible.  Ownership can GROW
here where it cannot in the contained arm, but backed accounting can only
fall — the request lands in `vm_noaccess` whole — which is why this shape
carries no budget guard and its rw twin does. -/
def mmap_fixed_noaccess_span_next (h : VmMaps) (addr n : word) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved
    ((addr, n) :: maps_subtract h.vm_maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    ((addr, n) :: maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp

/-! ## Budget gates

A fresh rw grant is charged eagerly against `vm_limit` unless it is
`MAP_NORESERVE`; a replacement is charged as the DELTA the post-state
shows.  The gates sit INSIDE each success resolution, as `choose` guards,
never in the branch-selection tests: over budget the guard is
unsatisfiable, the `alt` collapses onto its errno arm, and the model MUST
answer -ENOMEM — the forced out-of-memory point of issue #131 — where a
gate in the branch test would answer `unmodeled` instead. -/

def mmap_noreserve_backed_ok (flags : word) (m : Model) (nZ : Int) : Bool :=
  if mmap_noreserve_b flags then true
  else vm_backing_used m + nZ ≤ (m_vmmaps m).vm_limit

/-- The contained rw commit's gate, on the whole post-state: over a range
already accounted the delta, and the charge, are zero.  Linux charges the
delta too — `__mmap_region` charges `pglen - vms.nr_accounted` and calls
`security_vm_enough_memory_mm` only when that is nonzero (mm/mmap.c:1406-1413
at Linux v6.12; at v6.18.46 the same charge is `__mmap_prepare`'s,
mm/vma.c:2422-2429). -/
def mmap_fixed_rw_budget_ok (flags : word) (m : Model) (addr n : word) : Bool :=
  vm_backing_within_limit
    (with_mmap_replacement flags addr n
      (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m))

/-- The same gate on the spanning post-state, where the part of the request
that met nothing is newly OWNED as well as newly exposed: `__mmap_prepare`
takes `map->charged = map->pglen - vms->nr_accounted` (mm/vma.c:2422-2429,
Linux v6.18.46), and `nr_accounted` counts only the VM_ACCOUNT pages the
gather detached — the pages already inside the request. -/
def mmap_fixed_rw_span_budget_ok (flags : word) (m : Model) (addr n : word) : Bool :=
  vm_backing_within_limit
    (with_mmap_replacement flags addr n
      (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m))

/-! ## MAP_FIXED_NOREPLACE — placed exactly, refused rather than replaced

The bit asks for MAP_FIXED's placement and refuses where MAP_FIXED
replaces.  `do_mmap` (mm/mmap.c, Linux v6.18.46) decides both halves, and
the Rocq section of the same name carries the argument in full; what
follows is the citation each decision rests on.

- PLACEMENT.  `if (flags & MAP_FIXED_NOREPLACE) flags |= MAP_FIXED;`
  (mm/mmap.c:361-362, Linux v6.18.46) runs before anything else in
  `do_mmap` reads the word, so `__get_unmapped_area` (:406) meets the request as it meets
  MAP_FIXED: both generic searches hand `addr` back (:700-701, :750-751)
  once their `len > mmap_end - mmap_min_addr` -ENOMEM has passed
  (`generic_get_unmapped_area`, mm/mmap.c:697-698, and its top-down twin
  at :747-748, Linux v6.18.46), and the bounds and alignment tests run in
  the MAP_FIXED order (:824-825, :857-858, :859-860, :862-863).  With
  riscv64's `arch_get_mmap_end` at `STACK_TOP_MAX`
  (arch/riscv/include/asm/processor.h:20-23, Linux v6.18.46) that -ENOMEM
  never fires on a request the arms answer under the 4096 default floor or
  a SELinux kernel's 65536; the two forms riscv64 computed from the address
  from v6.6-rc1 until v6.6.111 and v6.10.10 (the generic `TASK_SIZE` stood
  before them) fire it on some misaligned requests, which is
  bugs/mmap-fixed-misaligned-refuses-older-riscv-enomem.md, and so does a
  floor raised far enough (the floor entry below).  The two arms open with
  the MAP_FIXED arms' argument gate verbatim, and it PRECEDES the refusal:
  an unaligned `addr` inside a live mapping is -EINVAL, not -EEXIST.
- REFUSAL.  `if (find_vma_intersection(mm, addr, addr + len)) return
  -EEXIST;` (mm/mmap.c:410-413, Linux v6.18.46), and
  `find_vma_intersection` (mm/mmap.c:885-893, Linux v6.18.46) is `mt_find`
  over `[addr, addr + len - 1]`: ANY mapped page refuses the request,
  before `mmap_region` runs, with nothing changed.  The model asks
  `region_free` of `vm_reserved ++ vm_maps`, the test every fresh grant
  passes, so the image's LOAD reservations — which the MAP_FIXED arms
  decline, having no way to replace them — are an answer here: they are
  VMAs `load_elf_binary` installed, and refusing them changes nothing.
  The ledger is not the VMA tree, though: a brk grow inside one page
  ledgers bytes no VMA backs once the program has unmapped that page, and
  over those bytes both arms refuse the grant Linux gives:
  bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md.
- THE OTHER ANSWERS on an occupied range.  `mm->map_count >
  sysctl_max_map_count` (`do_mmap`, mm/mmap.c:377-378, Linux v6.18.46) is
  the -ENOMEM every arm admits through `mmap_errnos`, hence `alt (errno_from
  mmap_errnos) (err_ret EEXIST)`.  Nothing after the refusal answers here:
  `MAP_LOCKED`'s -EPERM (:415-417) and `mlock_future_ok`'s -EAGAIN
  (:419-420) follow the `return -EEXIST`.  On a free range they are the
  free-range sub-case's to exclude, and each is excluded by shape: the
  first needs a bit outside it, the second VM_LOCKED in `mm->def_flags`,
  which only `mlockall(MCL_FUTURE)` sets and no modeled call does.
- QEMU'S USER-MODE EMULATION refuses an occupied range too, under `-R` or
  on a 4 KiB host.  With `reserved_va`, `target_mmap__locked` answers
  EEXIST when `page_check_range_empty` fails (linux-user/mmap.c:925-931,
  QEMU 11.1.1); without it, on a host whose page is the guest's 4 KiB,
  the bit stays on the host `mmap`, whose own refusal — or, on a host
  without the bit, the `p != want_p` emulation — comes back as EEXIST
  (`mmap_h_eq_g`, linux-user/mmap.c:616-625, QEMU 11.1.1).  On a 16 or
  64 KiB host without `-R`, `mmap_h_gt_g` (:792-912, QEMU 11.1.1) hands
  the part of a request that covers only part of a host page to
  `mmap_frag`, which, when another guest page on that host page is valid,
  zero-fills the requested pages without a host `mmap` and returns
  success (:363-413, QEMU 11.1.1), occupied or not.  That grant over an
  occupied page breaks the contract MAP_FIXED_NOREPLACE exists to keep, a
  deviation of QEMU's from the call it emulates that the arms do not
  allow.  The host path can also answer EEXIST on a range the guest has
  free; it, the vdso/vvar pair the ledger does not carry, and qemu's own
  guest vdso, which a top-down host places below the stack when no gap
  between the guest stack and the host's `mmap_base` fits it, and which
  under `-R` qemu's own search can place below the stack too
  (`load_elf_vdso`, linux-user/elfload.c:1308-1318, QEMU 11.1.1), are the
  section on this bit in bugs/mmap-placement-admits-unreachable-addresses.md.
  So is the stack qemu maps whole before the guest runs (`setup_arg_pages`,
  linux-user/elfload.c:395-436, QEMU 11.1.1): `-s` or `QEMU_STACK_SIZE`
  above 8 MiB carries it below `alloc_top` while the guest's RLIMIT_STACK
  stays the default, and a request there is free in the ledger and EEXIST
  under `-R`, on a 4 KiB host, and on a 16 or 64 KiB host for a request
  covering a whole host page of it:
  bugs/mmap-noreplace-refuses-qemu-user-eexist-on-a-large-stack.md.
  On a host whose own floor is raised, a non-root qemu-user without
  `reserved_va` gets that host's -EPERM below it, and on a 16 or 64 KiB
  host at the default floor too, for a request whose first host page is
  page 0: the floor entry's class reached through the host,
  bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md.  The
  loader reserves an image's whole span before it maps the segments
  (`load_elf_image`, linux-user/elfload.c:1065-1075, QEMU 11.1.1), so a
  gap between two LOAD segments, free in the ledger and on Linux, is
  EEXIST under `-R` and on a 4 KiB host, and on a 16 or 64 KiB host for a
  request covering a whole host page of it:
  bugs/mmap-noreplace-refuses-qemu-user-eexist-in-a-load-gap.md.  In both,
  `mmap_frag` grants one that covers no whole host page while another
  guest page on each host page it touches is still valid, the answer Linux
  gives in a gap.  Once the guest has unmapped EVERY other guest page of
  such a host page, `target_munmap` has kept that host page mapped
  (`mmap_reserve_or_unmap`, linux-user/mmap.c:1046-1075, QEMU 11.1.1), and
  `mmap_frag`'s own host `mmap`, the bit kept, is EEXIST (:363-386, QEMU
  11.1.1). -/

/-- Does `flags` spell a `MAP_FIXED_NOREPLACE` request over the plain
anonymous shape?  Both spellings, deliberately: `do_mmap` folds MAP_FIXED
into the word at mm/mmap.c:361-362 (Linux v6.18.46) and only ADDS it, :410
tests the NOREPLACE bit alone, and `calc_vm_flag_bits`
(include/linux/mman.h:153-162, Linux v6.18.46; riscv defines no
`arch_calc_vm_flag_bits`, so :95-96's 0 stands) turns neither bit into a
VM_ flag — so `MAP_FIXED | MAP_FIXED_NOREPLACE` is the same request, and
letting MAP_FIXED win would accept a replacement Linux refuses.  The bit is
MATCHED, not stripped, for the same reason.  Rocq: `Z.eqb (mmap_flags_core
flags) … || Z.eqb (mmap_flags_core flags) …`. -/
def mmap_noreplace_flags_b (flags : word) : Bool :=
  (mmap_flags_core flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED_NOREPLACE)
  || (mmap_flags_core flags
        == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED + MAP_FIXED_NOREPLACE)

/-- The rw NOREPLACE shape.  A sanitizer runtime opens with its low and
high shadows in this shape, `MAP_NORESERVE` set, before any other mapping,
so that a range some layout already occupies is refused rather than
overwritten. -/
def mmap_noreplace_rw_b (prot flags off : word) : Bool :=
  (bv_unsigned prot == PROT_READ + PROT_WRITE)
  && mmap_noreplace_flags_b flags && w_is0 off

/-- The PROT_NONE NOREPLACE shape: the same runtime's gap between the two
shadows. -/
def mmap_noreplace_noaccess_b (prot flags off : word) : Bool :=
  (bv_unsigned prot == PROT_NONE)
  && mmap_noreplace_flags_b flags && w_is0 off

/-! ## The spec

`mmap addr len prot flags fd off`.  Three things are decided before any
shape is matched, in the kernel's own order:

1. A MISALIGNED `off` is -EINVAL (`riscv_sys_mmap`, see `mmap_off_aligned_b`),
   declined only for a wrapping `len` (`mmap_pglen_ok_b`).
2. `MAP_ANONYMOUS` clear is FILE-BACKED and `unmodeled` whole.  Two
   independent walls, either enough alone: the machine model has no
   readable-but-not-writable page (`RiscvSemantics.ms_mem` is at once the
   only readable source outside the loaded segments and the whole writable
   view), and `VmMaps` records ranges only, so a mapping cannot be tied to
   the file it came from — a `write`, `ftruncate` or `unlinkat` between
   the mmap and the first touch is visible through a private mapping on
   Linux, and a snapshot taken at mmap time would claim stale bytes as
   certain.  The -EBADF a closed fd gets (`ksys_mmap_pgoff`, before the
   length is read) is DELIBERATELY not answered either: qemu-user never
   resolves the fd and answers its own -EINVAL or -ENOMEM on five measured
   argument shapes, so an unconditional -EBADF would fall outside the
   intersection.  The Rocq branch carries the measurements.
3. `len = 0` is -EINVAL for the plain anonymous shape and `unmodeled` for
   the huge-page one (`mmap_plain_anon_b`).

Then the shapes.  The two FRESH-GRANT arms `choose` a placement under
four conditions and nothing else — page-aligned, nonzero, ending at or
below `alloc_top`, disjoint from `vm_reserved ++ vm_maps` — because that is
all `get_unmapped_area` promises for a preference-free request: both
generic searches ask `vm_unmapped_area` for a gap (mm/mmap.c:712-718 and
:763-770, Linux v6.18.46).  The spec used to pin the SEARCH too and was
wrong to — it excluded real placements (the kernel walks VMAs the ledger
does not carry), encoded a layout, and described a kernel that does not
deploy under ASLR; the Rocq PLACEMENT section carries the retreat.  When no
address satisfies the guard the `alt` collapses onto -ENOMEM: an exhausted
address space is modeled, not a gap.

Linux v6.18.46 mm/mmap.c: `do_mmap` rounds the length and checks its
bounds before address selection (:368-370).
`__get_unmapped_area` checks its bounds before alignment (:824-825,
:857-860).  `generic_get_unmapped_area` and
`generic_get_unmapped_area_topdown` first return -ENOMEM when
`len > mmap_end - mmap_min_addr` (:697-698, :747-748).
Otherwise, they return a MAP_FIXED `addr` unchanged (:700-701, :750-751).
Linux can return the address's encoded errno before it tests alignment.

The residual of :857 below `2^64` but above
`alloc_top` is declined; the -EINVAL is committed only below `alloc_top`,
which for a `Run.valid_sp` stack sits under `State.TASK_SIZE`.  -EPERM at
address 0 (`security_mmap_addr`, :862-863, whose baseline `cap_mmap_addr`,
security/commoncap.c:1459-1471, Linux v6.18.46, fires only below
`dac_mmap_min_addr`, whose DEFAULT is 4096 — `CONFIG_DEFAULT_MMAP_MIN_ADDR`,
mm/Kconfig:726-729, initialising `dac_mmap_min_addr` at
security/min_addr.c:11, and the `vm.mmap_min_addr` sysctl over it, :45-53,
with no upper bound; Debian's amd64 config ships 65536, so under
it the same -EPERM covers `[4096, 65536)`, where this arm answers, and
SELinux's `CONFIG_LSM_MMAP_MIN_ADDR` adds an -EACCES of its own —
`bugs/mmap-fixed-below-mmap-min-addr-admits-default-policy-alone.md`) is
declined for both shapes above the containment test.  None of the
four gates branches on `prot`.

Below the gate the split is on the LEDGER, not the flags:

- wholly inside one live mapping: THREE resolutions, because Linux
  produces three (Linux v6.18.46).  `__mmap_prepare` (mm/vma.c:2386-2444)
  tears the old range down at :2441, through `vms_clean_up_area`
  (mm/vma.c:1281-1293), BEFORE `__mmap_new_vma`'s calls to `vm_area_alloc`
  (mm/vma_init.c, Linux v6.18.46) and `vma_iter_prealloc` (mm/vma.h, same
  version) at mm/vma.c:2506-2508 and :2515-2518 can fail; either sends
  `__mmap_region` to `abort_munmap:` (mm/vma.c:2729-2730, Linux v6.18.46)
  with `clear_ptes` false, and `vms_abort_munmap_vmas` (mm/vma.c:2349-2369)
  then leaves a gap (:2360-2366: "Resort to the old failure method of
  leaving a gap where the MAP_FIXED mapping failed").  So: an errno with
  the range preserved (`max_map_count` in `vms_gather_munmap_vmas`,
  mm/vma.c:1389-1393, Linux v6.18.46, and for rw the commit charge in
  `__mmap_prepare`, mm/vma.c:2422-2429, both before :2441), the success,
  and an errno with
  the range DESTROYED.  The rw success emits `eff_zeros` over the whole
  request — fresh anonymous pages read back as zeroes, bytes written a
  moment ago included — which subsumes an unmap.
- meeting nothing at all: an ordinary anonymous grant naming its own
  address, TWO resolutions (with `vms.nr_pages` zero `vms_abort_munmap_vmas`
  returns at its first test, mm/vma.c:2354-2355, Linux v6.18.46).  It adds
  NO reachable transition: its guards are the hint-placed arm's `choose`
  guard conjunct for conjunct.
- meeting live mappings without being contained in one: the SPANNING
  replacement.  `vms_gather_munmap_vmas` (mm/vma.c:1372-1508, Linux v6.18.46) splits the
  first VMA at `addr` (:1401) and the last at the end (:1422), detaches
  everything between, and `__mmap_region` installs one mapping over the
  request; three resolutions again, the destructive boundary again the
  `vms_clean_up_area` call in `__mmap_prepare` (mm/vma.c:2441, Linux
  v6.18.46).
  `vma_is_sealed`'s -EPERM is not
  carried: `mseal` (462) is outside the modeled surface and the model
  tracks no kernel-installed special mapping.
- reaching `vm_reserved`, the image's LOAD reservations: `unmodeled`.  The
  image bytes are `State.Image` segments, not entries of this ledger, so
  replacing part of one here would leave the ledger and the machine
  disagreeing about what the process can execute.

The two MAP_FIXED_NOREPLACE arms take the same argument gate and split
ONCE on the ledger: a range meeting nothing is the free-range MAP_FIXED
sub-case again, resolution for resolution, and a range meeting anything
the ledger holds — the image included — is -EEXIST with nothing changed
(the MAP_FIXED_NOREPLACE section above, whose REFUSAL paragraph names the
ledger bytes no VMA backs).

Any other `prot`/`flags`/`off` combination is `unmodeled` (fail closed).

`fd` is a parameter and is never read: Linux does not read it either on the
one path this file answers (`mmap_fd_none`), and the file-backed path that
would read it is declined before it could.  The linter is told so here
rather than by renaming the argument away from the Rocq signature. -/
set_option linter.unusedVariables false in
def mmap_spec (addr len prot flags fd off : word) : Sys SyscallEffect :=
  if !(mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len then err_ret EINVAL else unmodeled)
  else if !(mmap_anon_b flags) then
    unmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags then err_ret EINVAL else unmodeled)
  else if mmap_modeled_b prot flags off then
    alt
      (e <- errno_from mmap_errnos ;; err_ret e)
      (m <- get_model ;;
       let h := m_vmmaps m
       let nZ := page_round_up_Z (bv_unsigned len)
       let n := Z_to_bv 64 nZ
       a <- choose (fun a => bv_unsigned a % page_size = 0
                             ∧ 0 < bv_unsigned a
                             ∧ bv_unsigned a + nZ ≤ alloc_top h
                             ∧ region_free (h.vm_reserved ++ h.vm_maps) a n = true
                             ∧ mmap_noreserve_backed_ok flags m nZ = true) ;;
       modify (fun _ =>
         with_mmap_backing flags a n
           (with_vmmaps
              (VmMaps.mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
                h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
                h.vm_mmap_base h.vm_init_sp) m)) ;;
       Monad.pure (mkEffect a [] [(a, n)]))
  else if mmap_noaccess_b prot flags off then
    alt
      (e <- errno_from mmap_errnos ;; err_ret e)
      (m <- get_model ;;
       let h := m_vmmaps m
       let nZ := page_round_up_Z (bv_unsigned len)
       let n := Z_to_bv 64 nZ
       a <- choose (fun a => bv_unsigned a % page_size = 0
                             ∧ 0 < bv_unsigned a
                             ∧ bv_unsigned a + nZ ≤ alloc_top h
                             ∧ region_free (h.vm_reserved ++ h.vm_maps) a n = true) ;;
       modify (fun _ =>
         with_mmap_backing flags a n
           (with_vmmaps
             (VmMaps.mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
               ((a, n) :: h.vm_noaccess) h.vm_start_brk
               h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)) ;;
       Monad.pure (SyscallEffect.mkEffectU a [] [] [(a, n)] [] []))
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then err_ret ENOMEM
      else if two_pow_64 - page_size < bv_unsigned addr then
        /- Linux can return the address's encoded errno before it tests alignment.
        Linux v6.18.46 mm/mmap.c: `generic_get_unmapped_area` and `generic_get_unmapped_area_topdown` first return -ENOMEM when `len > mmap_end - mmap_min_addr`.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` tests `IS_ERR_VALUE(addr)` before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` tests alignment before `guest_range_valid_untagged`.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          /- QEMU can pass this exact-end range to the host after address translation.
          Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
          The QEMU source uses version 11.1.1.
          Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` rejects the range before alignment.
          QEMU 11.1.1 linux-user/main.c: `main` sets `guest_addr_max = ~0ul` without `-R`.
          QEMU 11.1.1 include/user/guest-host.h: `guest_range_valid_untagged_vaddr` accepts the exact end.
          QEMU 11.1.1 linux-user/mmap.c: `target_mmap` then translates the address and calls the host.
          A run that reaches this decline cannot satisfy strong equivalence. -/
          unmodeled
        else err_ret ENOMEM
      else
        /- Linux tests range bounds before alignment.
        QEMU tests alignment before range bounds.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` checks the range before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` checks alignment before `guest_range_valid_untagged`.
        PR #1929 carries the Rocq answer.
        A later Lean change replaces this decline after that PR merges.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
    else
      m <- get_model ;;
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then unmodeled
      else if !(bv_unsigned addr % page_size == 0) then err_ret EINVAL
      else if !(0 < bv_unsigned addr) then unmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n
      then
      -- contained: three resolutions
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (modify (fun _ =>
             with_mmap_replacement flags addr n
              (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps
               ((addr, n) :: maps_subtract h.vm_noaccess
                               (bv_unsigned addr)
                               (bv_unsigned addr + bv_unsigned n))
               h.vm_start_brk h.vm_brk h.vm_limit
               h.vm_mmap_base h.vm_init_sp) m)) ;;
           Monad.pure (SyscallEffect.mkEffectU addr [] [] [(addr, n)] [] []))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           Monad.pure (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n
      then
      -- free range: the fresh PROT_NONE reservation naming its own address
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
             ((a, n) :: h.vm_noaccess) h.vm_start_brk
             h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)) ;;
         Monad.pure (SyscallEffect.mkEffectU a [] [] [(a, n)] [] []))
      else if region_free h.vm_reserved addr n
      then
      -- spanning: three resolutions
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (modify (fun _ =>
             with_mmap_replacement flags addr n
               (with_vmmaps (mmap_fixed_noaccess_span_next h addr n) m)) ;;
           Monad.pure (SyscallEffect.mkEffectU addr [] [] [(addr, n)] [] []))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           Monad.pure (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      -- the request meets the image's LOAD reservations
      else unmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then err_ret ENOMEM
      else if two_pow_64 - page_size < bv_unsigned addr then
        /- Linux can return the address's encoded errno before it tests alignment.
        Linux v6.18.46 mm/mmap.c: `generic_get_unmapped_area` and `generic_get_unmapped_area_topdown` first return -ENOMEM when `len > mmap_end - mmap_min_addr`.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` tests `IS_ERR_VALUE(addr)` before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` tests alignment before `guest_range_valid_untagged`.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          /- QEMU can pass this exact-end range to the host after address translation.
          Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
          The QEMU source uses version 11.1.1.
          Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` rejects the range before alignment.
          QEMU 11.1.1 linux-user/main.c: `main` sets `guest_addr_max = ~0ul` without `-R`.
          QEMU 11.1.1 include/user/guest-host.h: `guest_range_valid_untagged_vaddr` accepts the exact end.
          QEMU 11.1.1 linux-user/mmap.c: `target_mmap` then translates the address and calls the host.
          A run that reaches this decline cannot satisfy strong equivalence. -/
          unmodeled
        else err_ret ENOMEM
      else
        /- Linux tests range bounds before alignment.
        QEMU tests alignment before range bounds.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` checks the range before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` checks alignment before `guest_range_valid_untagged`.
        PR #1929 carries the Rocq answer.
        A later Lean change replaces this decline after that PR merges.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
    else
      m <- get_model ;;
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then unmodeled
      else if !(bv_unsigned addr % page_size == 0) then err_ret EINVAL
      else if !(0 < bv_unsigned addr) then unmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n
      then
      -- contained commit: three resolutions, the success budget-gated
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (_ <- choose (fun (_ : Unit) =>
                 mmap_fixed_rw_budget_ok flags m addr n = true) ;;
           modify (fun _ => with_mmap_replacement flags addr n
             (with_vmmaps (mmap_fixed_rw_next h addr n) m)) ;;
           Monad.pure (mkEffect addr [] [(addr, n)]))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           Monad.pure (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n
      then
      -- free range: an ordinary grant naming its own address, budget inside
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr
                               ∧ mmap_noreserve_backed_ok flags m nZ = true) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
             h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
                h.vm_mmap_base h.vm_init_sp) m)) ;;
         Monad.pure (mkEffect a [] [(a, n)]))
      else if region_free h.vm_reserved addr n
      then
      -- spanning: three resolutions, the success budget-gated
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (_ <- choose (fun (_ : Unit) =>
                 mmap_fixed_rw_span_budget_ok flags m addr n = true) ;;
           modify (fun _ => with_mmap_replacement flags addr n
             (with_vmmaps (mmap_fixed_rw_span_next h addr n) m)) ;;
           Monad.pure (mkEffect addr [] [(addr, n)]))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           Monad.pure (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      else unmodeled
  else if mmap_noreplace_noaccess_b prot flags off then
    -- the MAP_FIXED argument gate verbatim, then ONE split on the ledger
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then err_ret ENOMEM
      else if two_pow_64 - page_size < bv_unsigned addr then
        /- Linux can return the address's encoded errno before it tests alignment.
        Linux v6.18.46 mm/mmap.c: `generic_get_unmapped_area` and `generic_get_unmapped_area_topdown` first return -ENOMEM when `len > mmap_end - mmap_min_addr`.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` tests `IS_ERR_VALUE(addr)` before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` tests alignment before `guest_range_valid_untagged`.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          /- QEMU can pass this exact-end range to the host after address translation.
          Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
          The QEMU source uses version 11.1.1.
          Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` rejects the range before alignment.
          QEMU 11.1.1 linux-user/main.c: `main` sets `guest_addr_max = ~0ul` without `-R`.
          QEMU 11.1.1 include/user/guest-host.h: `guest_range_valid_untagged_vaddr` accepts the exact end.
          QEMU 11.1.1 linux-user/mmap.c: `target_mmap` then translates the address and calls the host.
          A run that reaches this decline cannot satisfy strong equivalence. -/
          unmodeled
        else err_ret ENOMEM
      else
        /- Linux tests range bounds before alignment.
        QEMU tests alignment before range bounds.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` checks the range before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` checks alignment before `guest_range_valid_untagged`.
        PR #1929 carries the Rocq answer.
        A later Lean change replaces this decline after that PR merges.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
    else
      m <- get_model ;;
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then unmodeled
      else if !(bv_unsigned addr % page_size == 0) then err_ret EINVAL
      else if !(0 < bv_unsigned addr) then unmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free (h.vm_reserved ++ h.vm_maps) addr n
      then
      -- free range: the MAP_FIXED PROT_NONE free-range sub-case
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
             ((a, n) :: h.vm_noaccess) h.vm_start_brk
             h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)) ;;
         Monad.pure (SyscallEffect.mkEffectU a [] [] [(a, n)] [] []))
      else
      -- occupied, the image included: -EEXIST with nothing changed
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (err_ret EEXIST)
  else if mmap_noreplace_rw_b prot flags off then
    -- the same gate and split; the free range is the rw MAP_FIXED
    -- free-range sub-case, its budget inside the resolution
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then err_ret ENOMEM
      else if two_pow_64 - page_size < bv_unsigned addr then
        /- Linux can return the address's encoded errno before it tests alignment.
        Linux v6.18.46 mm/mmap.c: `generic_get_unmapped_area` and `generic_get_unmapped_area_topdown` first return -ENOMEM when `len > mmap_end - mmap_min_addr`.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` tests `IS_ERR_VALUE(addr)` before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` tests alignment before `guest_range_valid_untagged`.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          /- QEMU can pass this exact-end range to the host after address translation.
          Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
          The QEMU source uses version 11.1.1.
          Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` rejects the range before alignment.
          QEMU 11.1.1 linux-user/main.c: `main` sets `guest_addr_max = ~0ul` without `-R`.
          QEMU 11.1.1 include/user/guest-host.h: `guest_range_valid_untagged_vaddr` accepts the exact end.
          QEMU 11.1.1 linux-user/mmap.c: `target_mmap` then translates the address and calls the host.
          A run that reaches this decline cannot satisfy strong equivalence. -/
          unmodeled
        else err_ret ENOMEM
      else
        /- Linux tests range bounds before alignment.
        QEMU tests alignment before range bounds.
        Linux v6.18.46 uses commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
        The QEMU source uses version 11.1.1.
        Linux v6.18.46 mm/mmap.c: `__get_unmapped_area` checks the range before alignment.
        QEMU 11.1.1 linux-user/mmap.c: `target_mmap` checks alignment before `guest_range_valid_untagged`.
        PR #1929 carries the Rocq answer.
        A later Lean change replaces this decline after that PR merges.
        A run that reaches this decline cannot satisfy strong equivalence. -/
        unmodeled
    else
      m <- get_model ;;
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then unmodeled
      else if !(bv_unsigned addr % page_size == 0) then err_ret EINVAL
      else if !(0 < bv_unsigned addr) then unmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free (h.vm_reserved ++ h.vm_maps) addr n
      then
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr
                               ∧ mmap_noreserve_backed_ok flags m nZ = true) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((a, n) :: h.vm_maps)
             h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
                h.vm_mmap_base h.vm_init_sp) m)) ;;
         Monad.pure (mkEffect a [] [(a, n)]))
      else
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (err_ret EEXIST)
  else unmodeled


/-! ## The budget mark for mmap

See the Rocq `Mmap.brk_budget_refused_b` for what a mark is, and the Rocq
`mmap_budget_refused_b` for this arm's argument in full.  The shape gates
are `mmap_spec`'s, in `mmap_spec`'s order, and each charging branch's
budget gate is the function that branch's `choose` carries —
`mmap_noreserve_backed_ok` for the hint-placed grant, for the free-range
MAP_FIXED grant and for the MAP_FIXED_NOREPLACE rw grant (a MAP_NORESERVE
request is free at grant time and so never budget-refused),
`mmap_fixed_rw_budget_ok` for the contained rw replacement,
`mmap_fixed_rw_span_budget_ok` for the spanning one.  The branches that
consume no backing (PROT_NONE, MAP_FIXED PROT_NONE, MAP_FIXED_NOREPLACE
PROT_NONE) never fire, and neither does anything an argument gate answers:
the -EINVALs, the fixed shapes' overflowing length and ceiling, the
NOREPLACE -EEXIST, and the `unmodeled` shapes.  All three budget gates
read the request and the pre-state and not the placement, so on every
shape but one the mark is exact: `true` iff no success resolution exists
for want of budget.  The exception is
the hint-placed rw shape whenever no placement satisfies the spec's
`choose` — a length past `alloc_top`, whether or not its page rounding
reaches `2^64`, or a ledger with no gap that wide: neither `mmap_spec`'s
`mmap_modeled_b` branch nor this one gates on the placement, so the spec
falls to its errno branch whatever the budget, while the mark, which does
not see the constraint `a + nZ ≤ alloc_top h`, still answers
`!(mmap_noreserve_backed_ok …)`.  So on a budget the request also
exceeds, the mark says `true` for a request the address space refuses: a
run excluded from the budget-parameterised family that need not have
been, never an admitted trace.  Rocq's mark has the same branch, and
`Checks/Cases/Run.lean`'s
`mmap_rw_overflowing_len_on_spent_budget_is_budget_refused` and
`mmap_rw_unplaceable_len_on_spent_budget_is_budget_refused` pin the
over-approximation, in its wrapping and its merely unplaceable instance,
so that a port adding a placement gate to both trees knows which pins
flip.

`tools/check_budget_marks.py` counts each gate's uses in this spec against
its uses here, so a charging branch added to `mmap_spec` without its line
in the mark fails the generated-docs job.

`fd` is a parameter and is never read, exactly as in `mmap_spec`: the mark
keeps the Rocq signature, the arm's, so the dispatcher hands both the same
six registers. -/
set_option linter.unusedVariables false in
def mmap_budget_refused_b (addr len prot flags fd off : word) (m : Model) : Bool :=
  if !(mmap_off_aligned_b off) then false
  else if !(mmap_anon_b flags) then false
  else if w_is0 len then false
  else
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if mmap_modeled_b prot flags off then
      !(mmap_noreserve_backed_ok flags m nZ)
    else if mmap_noaccess_b prot flags off then false
    else if mmap_fixed_noaccess_b prot flags off then false
    else if mmap_fixed_rw_b prot flags off then
      if two_pow_64 ≤ bv_unsigned addr + nZ then false
      else if !(bv_unsigned addr + nZ ≤ alloc_top h) then false
      else if !(bv_unsigned addr % page_size == 0) then false
      else if !(0 < bv_unsigned addr) then false
      else if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n then
        !(mmap_fixed_rw_budget_ok flags m addr n)
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        !(mmap_noreserve_backed_ok flags m nZ)
      else if region_free h.vm_reserved addr n then
        !(mmap_fixed_rw_span_budget_ok flags m addr n)
      else false
    else if mmap_noreplace_noaccess_b prot flags off then false
    else if mmap_noreplace_rw_b prot flags off then
      if two_pow_64 ≤ bv_unsigned addr + nZ then false
      else if !(bv_unsigned addr + nZ ≤ alloc_top h) then false
      else if !(bv_unsigned addr % page_size == 0) then false
      else if !(0 < bv_unsigned addr) then false
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        !(mmap_noreserve_backed_ok flags m nZ)
      else false
    else false

/-! ## munmap (215)

`munmap addr len`.  `SYSCALL_DEFINE2(munmap)` (mm/mmap.c:1077-1081, Linux
v6.18.46) untags `addr` (:1079; on riscv `untagged_addr` sign-extends by
`mm->context.pmlen` under `CONFIG_RISCV_ISA_SUPM`,
arch/riscv/include/asm/uaccess.h:15-45, and is the identity while `pmlen`
is 0, which only `prctl(PR_SET_TAGGED_ADDR_CTRL)` changes — prctl has no
arm here, so every modeled run keeps it 0) and calls `__vm_munmap`
(mm/vma.c:3189-3205, Linux v6.18.46), which takes the killable write lock
and calls `do_vmi_munmap` (mm/vma.c:1604-1627, Linux v6.18.46).  That checks the
arguments first, all -EINVAL and deterministic (:1611-1616):

    if ((offset_in_page(start)) || start > TASK_SIZE || len > TASK_SIZE-start)
            return -EINVAL;
    end = start + PAGE_ALIGN(len);
    if (end == start)
            return -EINVAL;

then finds the first VMA meeting `[start, end)` (`vma_find`, :1619) and
answers 0 when there is none (:1620-1623), else unmaps through
`do_vmi_align_munmap` (:1626; mm/vma.c:1557, Linux v6.18.46).  For a
page-aligned `start` and a nonzero `len` the disjunction `start > TASK_SIZE || len > TASK_SIZE -
start` is exactly `start + PAGE_ALIGN(len) > TASK_SIZE` — the first
disjunct covers the `start` for which the unsigned subtraction would wrap,
and `TASK_SIZE - start` is a page multiple while `PAGE_ALIGN` is the least
multiple at or above `len` (the Rocq header's argument) — which is the
`nZ` test below in `Int`, with `State.TASK_SIZE` the Sv48 top.  The
`end == start` guard's only reachable case is `len = 0`, answered by the
first test.  Which ranges are answered, which are the no-op 0, and why a
free range reaching into the stack band declines, is on the Rocq header of
`munmap_spec`. -/

/-- The free-range no-op arm's guard: nothing recorded in the range, and
the range ending at or below this run's `alloc_top` — the stack band above
it is the one region the ledger does not describe, so a range that is free
by the ledger may be the stack there, which Linux would unmap where a
no-op 0 would leave it mapped (the Rocq header of `munmap_spec`). -/
def munmap_free_ok (h : VmMaps) (addr : word) (nZ : Int) : Bool :=
  region_free (h.vm_reserved ++ h.vm_maps) addr (Z_to_bv 64 nZ)
  && bv_unsigned addr + nZ ≤ alloc_top h

/-- `munmap addr len`, in `do_vmi_munmap`'s order (mm/vma.c:1611-1626,
Linux v6.18.46): an unaligned `addr` or a zero `len` is -EINVAL before the
ledger is read (both are refusals of the same test, so their order is
unobservable); a page-rounded range whose end passes `TASK_SIZE` is
-EINVAL, decided on the `Int` sum so that a range reaching `2^64` is seen
(the errno is -EINVAL and not `Mprotect.mprotect_spec`'s -ENOMEM for the
same shape); then, with `n` the page-rounded length, a range EXACTLY a
recorded mapping is dropped from both ledgers, its backing forgotten and
the range declared in `eff_unmaps`; a range disjoint from everything the
ledger carries and ending at or below `alloc_top` is the no-op 0; anything
else — a partial, spanning or image-touching range, or a free range in the
stack band — is `unmodeled`.  Every range that passes the gate has
`addr + nZ ≤ TASK_SIZE`, so `n` never wraps. -/
def munmap_spec (addr len : word) : Sys SyscallEffect :=
  if !(bv_unsigned addr % page_size == 0) || w_is0 len then err_ret EINVAL
  else
    h <- get_vmmaps ;;
    let nZ := page_round_up_Z (bv_unsigned len)
    if TASK_SIZE < bv_unsigned addr + nZ then err_ret EINVAL
    else
    let n := Z_to_bv 64 nZ
    if map_has h.vm_maps addr n then
      set_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved (map_remove h.vm_maps addr)
                    (maps_subtract h.vm_noaccess (bv_unsigned addr)
                                   (bv_unsigned addr + bv_unsigned n))
                    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) ;;
      forget_vm_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ;;
      Monad.pure (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
    else if munmap_free_ok h addr nZ then ret_only (Z_to_bv 64 0)
    else unmodeled

end LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
