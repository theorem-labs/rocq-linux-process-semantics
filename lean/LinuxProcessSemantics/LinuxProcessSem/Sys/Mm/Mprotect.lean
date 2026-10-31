import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Mm.Mprotect — mprotect (226)

Mirrors `theories/LinuxProcessSem/Sys/Mm/Mprotect.v`, which answers to
Linux `mm/mprotect.c`: it holds what the kernel defines there, and nothing
else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The Rocq file quotes its line numbers from Linux v6.12; every number here
was re-read at v6.18.46 and relabelled, and where the two kernels differ
in more than a line number the docstring says how.

Two spellings differ from Rocq without changing a value: the grows-bit
tests are done on the `word` (`bv_and`) where Rocq does them on
`bv_unsigned` in `Z` (`Z.land`) — the constants are below `2^64`, so the
two agree — and the `Z.leb`/`Z.eqb` Bool tests are Lean's `≤`/`==` on
`Int`.  `Z.modulo` by `page_size` is Lean's `%`, which agrees with Rocq's
floor modulo for a positive divisor. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- ENOMEM only, and only on the branch that turns an inaccessible range
read-write.  The Rocq `mprotect_errnos` comment argues each other errno
away; the argument re-read at Linux v6.18.46:

- ENOMEM is genuine: making a range writable can exceed RLIMIT_AS /
  RLIMIT_DATA (`may_expand_vm`, in `mprotect_fixup`, mm/mprotect.c:801-803)
  or the commit charge (`security_vm_enough_memory_mm`, :807-808), and
  splitting the VMA at the range's edges can fail on the map_count limit
  (`split_vma`, mm/vma.c:590-591, Linux v6.18.46) or on allocation
  (`__split_vma`, mm/vma.c:510-512), both reached through
  `vma_modify_flags` (mm/vma.c, called at mm/mprotect.c:816).  None of that
  is tracked, so it stays injectable.
- EINVAL is unreachable past the argument gates `mprotect_spec` takes
  first: the grows conflict (`do_mprotect_pkey`, mm/mprotect.c:876-877,
  Linux v6.18.46) and the alignment test (:879-880) are decided by the
  spec itself; the
  GROWSDOWN/GROWSUP VMA checks (:909-915, :919-924) need a grows bit that
  `mprotect_modeled_b` excludes; `arch_validate_prot` (:887-888) is the
  generic definition on riscv64 (include/linux/mman.h:106-109, Linux
  v6.18.46; riscv has no arch/riscv/include/asm/mman.h to override it) and
  accepts rw; the pkey
  test (:899-901) is dead because `SYSCALL_DEFINE3(mprotect)` passes
  `pkey = -1` (:1011); `arch_validate_flags` (:971-974) is the generic
  always-true definition (include/linux/mman.h:119-122, Linux v6.18.46).
- EACCES cannot fire for rw: every entry of `vm_maps` carries
  VM_MAYREAD|VM_MAYWRITE|VM_MAYEXEC — `do_mmap` sets them on every
  mapping it creates (mm/mmap.c:400-401, Linux v6.18.46), and
  `do_brk_flags` gives brk memory VM_DATA_DEFAULT_FLAGS (mm/vma.c:2814),
  which on riscv is VM_DATA_FLAGS_NON_EXEC (arch/riscv/include/asm/page.h:209,
  include/linux/mm.h:461-462, Linux v6.18.46) and carries the same three —
  so :960-963
  cannot trip, and `map_deny_write_exec` (:965-968) returns false when
  `new` lacks VM_EXEC (include/linux/mman.h:208-209, Linux v6.18.46), which
  rw does.
- READ_IMPLIES_EXEC, which would add PROT_EXEC to a modeled rw request
  (`do_mprotect_pkey`, :868-869 and :944-946) and route it off the rw
  path, is not set on a modeled run: exec sets the bit only through
  `elf_read_implies_exec` (fs/binfmt_elf.c:1017-1018, Linux v6.18.46),
  whose default is 0 (include/linux/elf.h:9-13) and which arch/riscv does
  not override,
  and `personality` (92) is outside the modeled surface.  What exec does
  NOT do is clear it: riscv's `SET_PERSONALITY` keeps every bit outside
  PER_MASK (arch/riscv/include/asm/elf.h:137-142;
  include/uapi/linux/personality.h:19, :66; Linux v6.18.46), so a launcher
  that set it
  (`setarch -X`) hands it down.  That the process which started the run
  had not is an environmental premise of the same kind as the default
  `RLIMIT_STACK` (#677), and the Rocq Mmap header rests on it too.
- EINTR from `mmap_write_lock_killable` (:892-893) is unobservable: the
  wait is TASK_KILLABLE (`__down_write_killable`,
  kernel/locking/rwsem.c:1329-1331, Linux v6.18.46) and
  `signal_pending_state` (include/linux/sched/signal.h:408-416) aborts such
  a wait only on a
  fatal signal, which kills the task before the -EINTR reaches a register.
- EPERM for a sealed VMA (`vma_is_sealed`, checked in `mprotect_fixup`,
  mm/mprotect.c:766-767, Linux v6.18.46) is unreachable because `mseal`
  (462) is outside
  the modeled surface, so VM_SEALED is never set on a modeled run.
- An LSM may fail `security_file_mprotect` (:976-978), but the default hook
  returns 0 (include/linux/lsm_hook_defs.h:206, Linux v6.18.46). -/
def mprotect_errnos : List Int := [ENOMEM]

/-- The one `prot` the model can answer for at nonzero length: exactly the
rw permissions its anonymous memory already has.  A `prot` with garbage in
its high half is a real -EINVAL on Linux at nonzero length
(`arch_validate_prot`, include/linux/mman.h:106-109, Linux v6.18.46,
called from `do_mprotect_pkey` at mm/mprotect.c:887-888), and comparing
the whole
64-bit word makes it `unmodeled` here — fail closed, since answering 0
would accept a success no kernel produces.  The Rocq
`mprotect_modeled_b` note argues why no 32-bit truncation applies:
`SYSCALL_DEFINE3(mprotect, unsigned long, start, size_t, len, unsigned
long, prot)` (mm/mprotect.c:1008-1009, Linux v6.18.46) takes `prot` as a
full register. -/
def mprotect_modeled_b (prot : word) : Bool :=
  bv_unsigned prot == PROT_READ + PROT_WRITE

/-- Both stack-extension modifiers at once — the ONE argument error the
modeled surface takes from `prot`'s grows bits (`do_mprotect_pkey`,
mm/mprotect.c:867, Linux v6.18.46, reads them, :876-877 rejects the pair,
"can't be both").  Either one alone is legal, and both are masked out of `prot`
(:875) either way; a lone bit goes on to gate the VMA checks at :909 and
:919.  Rocq: `Z.land (bv_unsigned prot) PROT_GROWSDOWN ≠ 0 && …`. -/
def mprotect_grows_conflict_b (prot : word) : Bool :=
  !(bv_unsigned (bv_and prot (Z_to_bv 64 PROT_GROWSDOWN)) == 0)
  && !(bv_unsigned (bv_and prot (Z_to_bv 64 PROT_GROWSUP)) == 0)

/-- Expose one protected range while carrying MAP_NORESERVE provenance and
already-materialized pages across unchanged: `maps_subtract` is
`__split_vma`'s effect on the model's no-access intervals, and the backing
ledgers are not touched.  The post-state budget test therefore charges an
ordinary mapping now and leaves a lazy mapping to first-touch accounting,
which is the split `mprotect_fixup` makes: the commit charge is taken when
a private mapping turns writable, and only when `oldflags` has none of
VM_ACCOUNT|VM_WRITE|VM_HUGETLB|VM_SHARED|VM_NORESERVE (mm/mprotect.c:804-810,
Linux v6.18.46).  The Rocq `mprotect_model_next` note quotes that guard
as `if (!(oldflags & VM_NORESERVE))`, a paraphrase of the same
five-flag test, not a kernel difference. -/
def mprotect_model_next (m : Model) (addr n : word) : Model :=
  let h := m_vmmaps m
  with_vmmaps
    (VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps
      (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
      h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m

/-- Does the backing the exposure creates fit `vm_limit`?  Evaluated on the
post-state, so a lazy (MAP_NORESERVE) range costs nothing here. -/
def mprotect_budget_ok (m : Model) (addr n : word) : Bool :=
  vm_backing_within_limit (mprotect_model_next m addr n)

/-! ## The spec

`mprotect addr len prot`.  Linux decides FOUR things about the arguments
before it ever looks at the address space, and the spec follows that
order because the order is behavior — a zero-length call answers 0 for a
`prot` the model could not otherwise interpret, a grows conflict answers
-EINVAL for a `prot` that is otherwise fine, and a wrapping range answers
-ENOMEM for a `prot` that would itself be -EINVAL.  `do_mprotect_pkey`,
mm/mprotect.c, Linux v6.18.46:

    867  const int grows = prot & (PROT_GROWSDOWN|PROT_GROWSUP);
    873  start = untagged_addr(start);
    875  prot &= ~(PROT_GROWSDOWN|PROT_GROWSUP);
    876  if (grows == (PROT_GROWSDOWN|PROT_GROWSUP))
    877      return -EINVAL;
    879  if (start & ~PAGE_MASK) return -EINVAL;
    881  if (!len) return 0;
    883  len = PAGE_ALIGN(len);
    884  end = start + len;
    885  if (end <= start) return -ENOMEM;
    887  if (!arch_validate_prot(prot, start)) return -EINVAL;

`untagged_addr` is the identity on the modeled surface.  At v6.12 riscv
took the generic identity macro (the Rocq note); at v6.18.46 riscv defines
its own (arch/riscv/include/asm/uaccess.h:31-34) under
CONFIG_RISCV_ISA_SUPM, and it masks `mm->context.pmlen` high bits — but
`pmlen` is reset to 0 at exec (`activate_mm`,
arch/riscv/include/asm/mmu_context.h:24) and set only by
`set_tagged_addr_ctrl` (arch/riscv/kernel/process.c:285-346, Linux
v6.18.46), reached from `prctl(PR_SET_TAGGED_ADDR_CTRL)` and from a
tracer's regset write (`tagged_addr_ctrl_set`,
arch/riscv/kernel/ptrace.c:171-183, same version); neither
happens on a modeled run, which has no tracer and no arm admitting that
`prctl` option.  Without the config the macro is the identity (:44).  So
the alignment test sees the address the program passed.  This stops
being true when a `prctl` arm admits PR_SET_TAGGED_ADDR_CTRL.  (Even a nonzero `pmlen` moves only high bits,
so :879's page test is unaffected; what would move is the VMA lookup.)

A zero `len` returns 0 for EVERY `prot` that clears the grows conflict,
including PROT_EXEC and unknown high bits: `arch_validate_prot` is at :887,
past the `!len` return at :881.  The wrap test at :885 sits in that same
window, so a wrapping range is -ENOMEM for every `prot` too.

NOT LINUX ALONE, THOUGH.  QEMU's user-mode emulation validates the prot
word BEFORE its zero-length return: `target_mprotect` (linux-user/mmap.c:177-279,
QEMU 11.1.1) tests alignment (:188-190), then `validate_prot_to_pageflags`
(:191-194; the function is linux-user/mmap.c:121-151, QEMU 11.1.1), which
answers -EINVAL for any bit of its `int` prot outside
PROT_READ|PROT_WRITE|PROT_EXEC|PROT_SEM — the grows bits included, except
on HPPA (:146-147); AArch64 admits its BTI and MTE bits too (:126-145),
riscv64 neither — and only then tests `len == 0` (:195-197).  The
syscall entry strips PROT_GROWSDOWN first, but only when `start` lies
inside the guest's stack window, and never PROT_GROWSUP
(linux-user/syscall.c:11203-11216, QEMU 11.1.1).  So
`mprotect(x, 0, PROT_GROWSDOWN|rw)` for an `x` outside that window,
`mprotect(x, 0, PROT_GROWSUP|rw)` anywhere, and any zero-length call whose
LOW 32 prot bits hold a bit outside those four (bit 31, say) answer
-EINVAL under qemu-user and 0 under Linux, and the spec proves Linux's 0
as certain there: `bugs/mprotect-zero-length-prot-admits-linux-alone.md`
records it.  Bits at or above 32 are outside the divergence, because
`target_prot` is an `int` and qemu-user drops them before validating —
which is why the `2^40 + 3` zero-length pin in
`Checks/Cases/Mm/Mprotect.lean` is inside the intersection and the
lone-grows-bit pins are not.  The same order reaches the wrap arm: `guest_range_valid_untagged`
(:199-201), and the host `mprotect` behind it (:265-270) that is what
refuses `(2^63, 2^63)` when the guest owns the whole 64-bit space, both
run after the validation, so a wrapping range whose `prot` carries a lone
grows bit or an unknown low bit is -ENOMEM under Linux and -EINVAL under
qemu-user; no pin proves that -ENOMEM as certain (the wrap pins use 3 and
4, -ENOMEM under both), so the entry names it and nothing pins it.  And inside
the stack window the emulation does not merely strip PROT_GROWSDOWN: it
re-aims the call at `[stack_limit, start + len)` — `[stack_limit, start)`
at `len = 0` — (linux-user/syscall.c:11211-11213, QEMU 11.1.1),
so `mprotect(x, 0, PROT_GROWSDOWN)` there answers 0 while changing the
lower stack's protection, which `ret_only 0` does not model — a state
divergence the entry records beside the errno one.

THE FOURTH GATE.  `start`, `len` and `end` are 64 bits wide on riscv64, so
`end` is the WRAPPED sum and `end <= start` is precisely "the sum reached
`2^64`", which is what `two_pow_64 ≤ addr + page_round_up_Z len` says in
`Int`: a `len` in the top 4095 values makes C's `PAGE_ALIGN` wrap to 0 and
`page_round_up_Z` (exact in `Int`) answer `2^64`, so the test holds for
every `addr`; below the gate `len ≠ 0` already holds, so the rounded
length is at least a page and the sum can reach `2^64` no other way.
Passing the gate is what keeps the arithmetic below honest — `Z_to_bv 64
nZ` cannot wrap and the `(addr, n)` pair names the range asked for.  The
Rocq comment on this arm records the narrower test it replaced and the
case (`mprotect(2^63, 2^63, rw)`) that test got wrong.

The supported NONEMPTY operation is exactly PROT_READ|PROT_WRITE over one
tracked anonymous range.  On an already-rw subrange it is a no-op that
CANNOT fail: `mprotect_fixup` short-circuits on `newflags == oldflags`
(mm/mprotect.c:769-772, Linux v6.18.46) before `may_expand_vm` (:801), the
commit charge
(:807) and `vma_modify_flags` (:816), so there is no split, no map_count
test and no accounting to fail.  The equality holds even for a strict
subrange, because `newflags` is computed from `prot` and the VMA's own
flags rather than from the range (`do_mprotect_pkey`, :953-957;
VM_FLAGS_CLEAR is 0 on riscv64 — include/linux/mm.h:508-511,
include/linux/pkeys.h:16, Linux v6.18.46).  On one contained `vm_noaccess` interval it
removes that interval (splitting when necessary) and exposes fresh zeroes
through `eff_zeros`, provided the resulting backing fits `vm_limit`.

Every other `prot` is `unmodeled` at nonzero length, and the Rocq
`mprotect_spec` comment carries the two arguments: PROT_EXEC because the
model cannot fetch from a data page at all, so answering 0 would make
`Run.all_traces_error` free the target; PROT_NONE and the read-only
downgrade because anonymous memory has one representation
(`RiscvSemantics.ms_mem`) that is at once the readable source and the
whole writable view, so a readable-not-writable page has no encoding.
Linux takes the downgrade on the ordinary path (:956-957 clear VM_WRITE
from `newflags`; `mprotect_fixup` keeps the mapping live), so the decline
costs coverage, never soundness.

A range NOT fully contained in the tracked mappings is `unmodeled` rather
than the -ENOMEM Linux returns for a start outside every VMA
(`do_mprotect_pkey`, :905-907 and :917-918): the ledger is not a complete
picture of the address space — the stack carries no entry at all, by the
argument at `State.alloc_top` — so that errno would be a guess wherever
the model's picture is thinner than Linux's.

THE `vm_maps` CONJUNCT of the exposure branch is load-bearing on its own:
`vm_noaccess ⊆ vm_maps` is NOT an invariant of reachable states (the
same-page brk-shrink state the Rocq comment describes reaches a range
`vm_noaccess` contains and `vm_maps` does not).  In that state Linux
answers 0 — a break move inside one page changes no VMA, `PAGE_ALIGN` of
the old and new break agreeing (mm/mmap.c:153-158, Linux v6.18.46), so
the page's VMA stands and the rw `mprotect` is an ordinary exposure of a
fresh PROT_NONE page, which `testing/syscall-check/tests/noaccess_vm.c`'s
`brk-samepage-protect` case asserts — while the byte-granular ledger owns
the page eight bytes short; for a start outside every VMA Linux answers
-ENOMEM, not 0 (:905-907).  The model can name neither answer from its
ledger, so it declines; without the conjunct it would return 0 over a
range whose last eight bytes it does not own — the zeroes would be right,
the page being a fresh anonymous one, but a later store to those bytes
would fault in the model and not under Linux.  The
probe that fails when it is dropped is named on the Rocq arm, whose
comment gives the -ENOMEM as this state's answer; it is the unmapped
shape's. -/
def mprotect_spec (addr len prot : word) : Sys SyscallEffect :=
  if mprotect_grows_conflict_b prot then err_ret EINVAL
  else if !(bv_unsigned addr % page_size == 0) then err_ret EINVAL
  else if w_is0 len then ret_only (Z_to_bv 64 0)
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then
    err_ret ENOMEM
  else if mprotect_modeled_b prot then
    m <- get_model ;;
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
      alt
        (e <- errno_from mprotect_errnos ;; err_ret e)
        (_ <- choose (fun (_ : Unit) => mprotect_budget_ok m addr n = true) ;;
         modify (fun _ => mprotect_model_next m addr n) ;;
         Monad.pure (mkEffect (Z_to_bv 64 0) [] [(addr, n)]))
    else if map_contains h.vm_maps addr n && region_free h.vm_noaccess addr n then
      ret_only (Z_to_bv 64 0)
    else unmodeled
  else unmodeled

/-! ## The budget mark for mprotect

See the Rocq `Mmap.brk_budget_refused_b` for what a mark is.  The one
charging branch is the exposure of a PROT_NONE range inside a live
mapping, gated by `mprotect_budget_ok` on the post-state; its `choose` is
over `Unit`, so the gate reads nothing but the request and the pre-state
and the mark is exact.  The four argument gates, the already-rw no-op and
the `unmodeled` shapes never fire it.  The grows-conflict test is here
for shape alone: `mprotect_modeled_b` refuses every word with a grows
bit, so dropping it changes no value and no pin can tell it apart; the
zero-length, wrap, alignment and `vm_maps` tests CAN be told apart — each
would read a spent budget as refused on a call Linux returns from before
`mprotect_fixup`'s charge — and each has a pin in
`Checks/Cases/Mm/Mprotect.lean`. -/
def mprotect_budget_refused_b (addr len prot : word) (m : Model) : Bool :=
  if mprotect_grows_conflict_b prot then false
  else if !(bv_unsigned addr % page_size == 0) then false
  else if w_is0 len then false
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then false
  else if mprotect_modeled_b prot then
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
      !(mprotect_budget_ok m addr n)
    else false
  else false

end LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
