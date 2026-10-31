import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness

/-! # Checks.Cases.Checks.VmMapsDisjoint.Witness — the lies the counterexample's steps refuse (ticket K9)

Pins over `Checks.VmMapsDisjoint.Witness`, the part of the
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v` twin that runs PART 1's
steps through `check_syscall`.  The Rocq tree has no check file for it, so
this file mirrors nothing.  Not part of the trusted specification.

WHAT THE TWINS LEAVE OPEN.  Each step example states that the checker
ADMITS one answer at one state; beside them Rocq refuses only three mmap
placements.  So each step whose decision is its own gets here, at its own
state, the refusal of the lie a kernel could tell there, and each brk step
whose requested break the chain takes, where the kernel may answer the old
break instead, the admission of that answer.  Step 1's grow ends on a page
boundary, and its lie is pinned already as
`brk_grow_zeros_shifted_a_page_rejected`, the same request on a fixture
with `wit_s0`'s ledger; steps 7 and 8 are the overlap step's same-page
grow; none gets a second pin.  Step 5's placement refusals are Rocq's own,
twinned in the part, and its pin here refuses the unmap its grant does not
make.

WHAT THE COPIES ADD.  Most rules pinned here are pinned already, at other
states, in `Checks/Cases/Checks/Sys/Mm/Mmap.lean`; each such pin names its
generic twin there.  The copies hold the rules at the counterexample's own
states, which the generic pins do not reach, so each ported step has its
refusal beside its admission.  Three are new at checker level, and each
names the spec-level pin in `Checks/Cases/Mm/Mmap.lean` that holds its
rule: step 5's refused unmap; the contrast's page-crossing grow refused
because a mapping covers the page the grow would install, where the
generic pin's mapping sits on the guard page above it; and the contrast's
grow granted from a break inside a mapping, the one pin that holds where
the grow's address-space test starts.

EVIDENCE.  A pin stated `= CheckReject` is POSITIVE to
`tools/check_lean_pin_evidence.py` (no `¬`, no `Unmodeled`), so it cites
the kernel function whose answer the refused lie contradicts; where a probe
tells the same lie to the Rocq checker, its `reject --mutate` case is
named in prose.  The pins close as the twin's steps do, and for the
reasons that file's header gives; the last section pins those reasons.
`Checks/Cases/Tactic.lean`'s `sys_norm` is not the closer: on these
`check_syscall` statements it makes no progress on the munmap step and
exceeds `maxRecDepth` on a brk step, and the dispatch closers of
`Checks/Cases/Checks/Sys/Mm/Mmap.lean` match that file's own `brk_in` and
`munmap_in`, which these statements do not use. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.VmMapsDisjoint.Witness

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

section K9

/-! ## K9 — the same-page grow that makes the overlap

`SYSCALL_DEFINE1(brk)` (mm/mmap.c:115-213, Linux v6.18.46) returns in three
ways: `-EINTR` when the wait for the lock is killed (:125-126), `brk` from
`success:` (:207), and `origbrk` from `out:`, which every refusal takes
(:209-212).  It rounds both breaks (:153-154) and on `oldbrk == newbrk`
sets `mm->brk = brk` and goes to `success:` with no address-space test
(:155-158).  From `wit_s5`, brk(0x10834) rounds 67536 and 67636 to the same
page boundary, 69632. -/

/-- A break neither requested nor old is refused at the overlap step: 67600
is none of the three returns (mm/mmap.c:125-126, :207, :212, Linux
v6.18.46).  Generic twin: `brk_grow_to_a_third_value_rejected`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem wit_overlap_step_refuses_a_third_break :
    check_syscall (brk_in 67636) (mkEffect 67600 [] []) wit_s5 = CheckReject := by
  rfl

/-- …and the OLD break is admitted there, the ledger unchanged.  The
data-limit test (mm/mmap.c:149-151, Linux v6.18.46) sits above the
same-page exit and refuses by `goto out`, which answers `origbrk`
(:209-212); the test is `check_data_rlimit` in include/linux/mm.h, which
answers `-ENOSPC` once the new data size passes `RLIMIT_DATA`.  On this
trace step 2 passed the same test at a higher break, 69732, and the test
only tightens as the break rises, so refusing here needs the limit lowered
in between; another process can lower it with `prlimit64`, which looks its
target up by pid (kernel/sys.c:1751, Linux v6.18.46).  The model sees no
such change: its `prlimit64` arm declines every pid but the caller's and
every resource but `RLIMIT_CORE` (`prlimit64_spec`, Sys/Kernel/Sys.lean),
so no arm lowers `RLIMIT_DATA` — the reason `brk_r_ok`'s docstring gives.
That stops holding the day either decline is widened.  Generic twin:
`brk_grow_may_fail`.
kernel: mm/mmap.c:brk; include/linux/mm.h:check_data_rlimit; kernel/sys.c:prlimit64@v6.18.46 -/
theorem wit_overlap_step_admits_the_old_break :
    check_syscall (brk_in 67636) (mkEffect 67536 [] []) wit_s5 = CheckOk wit_s5 [] := by
  rfl

/-- The overlap step's grant zeroes nothing: the same-page exit
(mm/mmap.c:155-158, Linux v6.18.46) sets `mm->brk` and installs no page, so
the 100 bytes keep what the step-5 mapping holds there.  An effect zeroing
`[old, new)` is the lie the `reject --mutate brk#6:smuggle-zeros:a0+-8:8`
case of `testing/syscall-check/tests/brk_shrink_frees.c` tells the Rocq
checker.  Generic twin: `brk_same_page_regrow_smuggled_zeros_rejected`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem wit_overlap_step_refuses_a_zero_fill :
    check_syscall (brk_in 67636) (mkEffect 67636 [] [(67536, 100)]) wit_s5 = CheckReject := by
  rfl

/-! ## K9 — the same-page shrink of step 6 -/

/-- Step 6 frees no page: 67526 and 67536 round to the same page boundary,
69632, and the exit at mm/mmap.c:155-158 (Linux v6.18.46) is taken before
the shrink block (:160-178), so nothing is unmapped.  The lie declares
`[a0, a0 + 4096)` freed, `a0` the requested break: the
`reject --mutate brk#5:smuggle-unmap:a0:4096` case of
`testing/syscall-check/tests/brk_shrink_frees.c`, told at this state.
Generic twin: `brk_subpage_shrink_smuggled_unmap_rejected`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem wit_step6_refuses_a_freed_page :
    check_syscall (brk_in 67526) (SyscallEffect.mkEffectU 67526 [] [] [(67526, 4096)] [] [])
        wit_s5
      = CheckReject := by
  rfl

/-- …and the OLD break is admitted there, the ledger unchanged: the step-6
request passes `min_brk` (mm/mmap.c:140-141, Linux v6.18.46) and rounds to
the break's own page, so only the data-limit test above the same-page exit
(:149-151, :155-158) can refuse it, by `goto out`, which answers `origbrk`
(:209-212).  `check_data_rlimit` (include/linux/mm.h, Linux v6.18.46) passed
step 4 at a higher break, 67536, and only tightens as the break rises, so
refusing here needs the limit lowered in between by another process's
`prlimit64` (kernel/sys.c:1751, Linux v6.18.46), as at the overlap step.
No checker-level twin; the spec-level one is `brk_r_ok_grown_subpage`.
kernel: mm/mmap.c:brk; include/linux/mm.h:check_data_rlimit; kernel/sys.c:prlimit64@v6.18.46 -/
theorem wit_step6_admits_the_old_break :
    check_syscall (brk_in 67526) (mkEffect 67536 [] []) wit_s5 = CheckOk wit_s5 [] := by
  rfl

/-! ## K9 — the shrink into the hole of step 4 -/

/-- Step 4's shrink really unmaps the second heap page: `newbrk` is 69632
and `oldbrk` 73728 (mm/mmap.c:153-154, Linux v6.18.46), `vma_find` from
`newbrk` below `oldbrk` meets what step 3 left of the heap VMA,
`[69632, 73728)` (:163-166), and `do_vmi_align_munmap` removes
`[newbrk, oldbrk)` (:173-174).  An effect declaring no unmap is the lie of
the `reject --mutate brk#3:drop-unmaps` case of
`testing/syscall-check/tests/brk_shrink_frees.c`.  Generic twin:
`brk_shrink_must_declare_unmaps`.
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem wit_step4_refuses_an_undeclared_unmap :
    check_syscall (brk_in 67536) (mkEffect 67536 [] []) wit_s3 = CheckReject := by
  rfl

/-- …and the OLD break is admitted there, the ledger unchanged and nothing
unmapped: a shrink refuses by `goto out`, which answers `origbrk`
(mm/mmap.c:149-151, :173-175, :209-212, Linux v6.18.46).  Here `newbrk` and
`oldbrk` are the ends of the heap VMA `[69632, 73728)`, so
`do_vmi_align_munmap` splits nothing and fails only on an allocation
(mm/vma.c:1428-1430, :1573-1575, Linux v6.18.46); the data-limit test passed
step 2 at a higher break, 69732, so it refuses only once another process has
lowered the limit with `prlimit64` (kernel/sys.c:1751, Linux v6.18.46).
Generic twin: `brk_shrink_may_fail`.
kernel: mm/mmap.c:brk; mm/vma.c:do_vmi_align_munmap,vms_gather_munmap_vmas; include/linux/mm.h:check_data_rlimit; kernel/sys.c:prlimit64@v6.18.46 -/
theorem wit_step4_admits_the_old_break :
    check_syscall (brk_in 67536) (mkEffect 69732 [] []) wit_s3 = CheckOk wit_s3 [] := by
  rfl

/-! ## K9 — the munmap of step 3 -/

/-- Step 3's munmap really unmaps the first heap page:
`SYSCALL_DEFINE2(munmap)` (mm/mmap.c:1077-1081, Linux v6.18.46) calls
`__vm_munmap` (mm/vma.c:3189-3205), whose `do_vmi_munmap` finds the heap
VMA `[65536, 73728)` overlapping `[65536, 69632)` (:1618-1624) and hands it
to `do_vmi_align_munmap` (:1626).  An effect declaring nothing unmapped is
refused.  Generic twin: `munmap_without_unmap_rejected`.  It closes by
`whnf` for the reason the part's munmap step does.
kernel: mm/mmap.c:munmap; mm/vma.c:__vm_munmap,do_vmi_munmap@v6.18.46 -/
theorem wit_step3_refuses_an_undeclared_unmap :
    check_syscall
        (SyscallInput.mkInput 215 [65536, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (SyscallEffect.mkEffectU 0 [] [] [] [] []) wit_s2
      = CheckReject := by
  conv => lhs; whnf

/-! ## K9 — the page-crossing grow of step 2 -/

/-- Step 2 zeroes the whole new page, not the 100 bytes the ledger records:
`do_brk_flags(&vmi, brkvma, oldbrk, newbrk - oldbrk, 0)` (mm/mmap.c:194,
Linux v6.18.46) extends the heap VMA over `[69632, 73728)` (mm/vma.c:2829-2836),
and a first touch of that page reads zeros: `do_anonymous_page`
(mm/memory.c:5149) maps the zero page for a read (:5169-5172) and otherwise
a folio from `alloc_anon_folio` (:5198), which zeroes a large folio
(:5122-5131) and falls back to `folio_prealloc` with `need_zero` (:5141,
:1200-1206).  An effect zeroing `[69632, 69732)` alone, from the aligned
old break over part of the installed page, is the lie refused.  The
`reject --mutate brk#8:drop-zeros,smuggle-zeros:a0+-16:16` case of
`testing/syscall-check/tests/brk_shrink_frees.c` tells a neighbouring one,
a zero-fill of `[a0 - 16, a0)` straddling the page boundary from an
unaligned break (`brk_cross_page_grow_byte_zeros_rejected`).  Generic
twin: `brk_grow_partial_zeros_rejected`.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags; mm/memory.c:do_anonymous_page,alloc_anon_folio@v6.18.46 -/
theorem wit_step2_refuses_the_logical_zero_range :
    check_syscall (brk_in 69732) (mkEffect 69732 [] [(69632, 100)]) wit_s1 = CheckReject := by
  rfl

/-- …and the OLD break is admitted there, the ledger unchanged: every
refusal on the grow path is a `goto out` answering `origbrk`
(mm/mmap.c:149-151, :180-181, :187-190, :194-195, :209-212, Linux
v6.18.46).  No other process is needed: an `RLIMIT_AS` one page above the
task's `total_vm` before step 1, set before `execve` and inherited
(`copy_signal`, kernel/fork.c:1693, Linux v6.18.46), passes step 1's
`may_expand_vm` test (mm/mmap.c:1326-1327, Linux v6.18.46) and refuses this
one's, which `do_brk_flags` returns as -ENOMEM (mm/vma.c:2816-2817, Linux
v6.18.46).  Generic twin: `brk_grow_may_fail`.
kernel: mm/mmap.c:brk,may_expand_vm; mm/vma.c:do_brk_flags; kernel/fork.c:copy_signal@v6.18.46 -/
theorem wit_step2_admits_the_old_break :
    check_syscall (brk_in 69732) (mkEffect 69632 [] []) wit_s1 = CheckOk wit_s1 [] := by
  rfl

/-! ## K9 — the grant of step 5 -/

/-- Step 5's grant unmaps nothing.  Without `MAP_FIXED`, `do_mmap` maps
where `__get_unmapped_area` says (mm/mmap.c:406, :558, Linux v6.18.46):
the hint itself only when `[65536, 69632)` meets no VMA or guard gap
(`generic_get_unmapped_area_topdown`, :754-761; `generic_get_unmapped_area`,
:703-710, for the legacy layout), and otherwise a gap found free.  Either
way `__mmap_prepare` finds no VMA over `[addr, end)` (mm/vma.c:2393, Linux
v6.18.46), `init_vma_munmap` leaves `nr_pages` zero (:1527-1536), and the
gather that would detach one is skipped (:2398-2415).  qemu-user's
`target_mmap` unmaps no guest page there either (linux-user/mmap.c,
QEMU 11.1.1): the host `mmap` gets the hint without `MAP_FIXED`, or, under
`reserved_va`, `MAP_FIXED` over a range found empty of guest pages.  An
effect declaring `[65536, 69632)` unmapped beside the zero-fill is the lie.
No checker-level twin; the spec-level one is `rw_grant_iff`, whose
admitted effects carry no unmap.
kernel: mm/mmap.c:do_mmap,generic_get_unmapped_area_topdown,generic_get_unmapped_area; mm/vma.c:__mmap_prepare,init_vma_munmap@v6.18.46 -/
theorem wit_step5_refuses_an_unmap :
    check_syscall
        (SyscallInput.mkInput 222 [65536, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (SyscallEffect.mkEffectU 65536 [] [(65536, 4096)] [(65536, 4096)] [] []) wit_s4
      = CheckReject := by
  rfl

/-! ## K9 — the contrast: a page-crossing grow into a mapping

The overlap is granted because a same-page grow meets no address-space
test.  A grow that crosses a page boundary meets one: after
`check_brk_limits` (:180-181) the kernel runs `next = vma_find(&vmi, newbrk
+ PAGE_SIZE + stack_guard_gap)` from `oldbrk` and refuses by `goto out`
when `newbrk + PAGE_SIZE > vm_start_gap(next)` (mm/mmap.c:187-190, Linux
v6.18.46).  The state is `wit_s4` with one page mapped at 0x11000, the page
above the one the break sits in. -/

/-- `wit_s4` with a page mapped at 0x11000: the break 67536 is mid-page and
the mapping starts at the next page boundary. -/
def wit_page_above : Model :=
  with_vmmaps (wit_vm [(69632, 4096)] 65536 67536 wit_limit) wit_s0

/-- The state is one a process reaches: the step-5 request with its hint one
page up is granted there.  A hint is returned as it is when it is at or
above `mmap_min_addr`, leaves room for `len` below `mmap_end`, and its range
meets no VMA or guard gap (`generic_get_unmapped_area_topdown`,
mm/mmap.c:754-761, Linux v6.18.46; the same test in
`generic_get_unmapped_area`, :703-710, for the legacy layout).  Nothing is
mapped at 0x11000 in `wit_s4`, and `mmap_min_addr` is what
`update_mmap_min_addr` (security/min_addr.c:17-24, Linux v6.18.46) makes
it: the larger of `dac_mmap_min_addr`, 4096 by `DEFAULT_MMAP_MIN_ADDR`'s
default (mm/Kconfig:726-729, read at security/min_addr.c:11), and, where
`SECURITY_SELINUX` is configured, `LSM_MMAP_MIN_ADDR`'s default of 65536
(security/Kconfig:171-175, v6.18.46).  Both are below it: the pin is an
existence claim, true of a kernel on its defaults.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,generic_get_unmapped_area; security/min_addr.c:update_mmap_min_addr@v6.18.46 -/
theorem wit_page_above_is_reached_from_wit_s4 :
    check_syscall
        (SyscallInput.mkInput 222 [69632, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 69632 [] [(69632, 4096)]) wit_s4
      = CheckOk wit_page_above [] := by
  conv => lhs; whnf
  rw [show Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg
      (SyscallInput.mkInput 222 [69632, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none)) 1))) = 4096 by decide]
  rfl

/-- brk(0x11001) crosses into the mapped page and is refused when the
kernel claims it granted: `oldbrk` is 69632 and `newbrk` 73728
(mm/mmap.c:153-154, Linux v6.18.46), `vma_find` from 69632 meets the mapping
at 69632, and `73728 + PAGE_SIZE > 69632` takes `goto out` (:187-190).  The
lie carries the zero-fill such a grant would imply, so the refusal is the
address-space test's and not the effect comparison's.  No checker-level
twin: `brk_grow_flush_against_neighbour_rejected` puts its mapping on the
guard page, and a checker testing only that page admits this one.  The
spec-level twin is `brk_grow_into_live_page_rejected`
(`Checks/Cases/Mm/Mmap.lean`).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem page_crossing_grow_into_a_mapping_refused :
    check_syscall (brk_in 69633) (mkEffect 69633 [] [(69632, 4096)]) wit_page_above
      = CheckReject := by
  rfl

/-- …while the same answer from `wit_s4`, where 0x11000 is free, is granted:
`vma_find` from 69632 meets nothing below `newbrk + PAGE_SIZE +
stack_guard_gap` (mm/mmap.c:187-190, Linux v6.18.46), `do_brk_flags`
installs `[69632, 73728)` (:194) and `success:` returns `brk` (:207).  The
two states differ in that mapping alone, so the refusal above is the
next-mapping test's.
kernel: mm/mmap.c:brk; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem page_crossing_grow_granted_where_the_page_is_free :
    ∃ m', check_syscall (brk_in 69633) (mkEffect 69633 [] [(69632, 4096)]) wit_s4
      = CheckOk m' [] :=
  ⟨_, rfl⟩

/-- …and so is the same grow from `wit_s5`, where the break 67536 lies
inside the step-5 mapping `[65536, 69632)`: the next-mapping test starts
at the rounded old break, not at the break.  `oldbrk` is 69632, the
mapping's end, and `newbrk` 73728 (mm/mmap.c:153-154, Linux v6.18.46);
`check_brk_limits` (:180-181) hands a `MAP_FIXED` address back untested
(`generic_get_unmapped_area`, :700-701), and `vma_iter_init(&vmi, mm,
oldbrk)` then `vma_find` (:187-188) is `mas_find` from index 69632
(include/linux/mm.h:1024-1027, Linux v6.18.46), which the step-5 VMA,
stored over `[65536, 69631]`, does not meet.  Nothing else lies below
`newbrk + PAGE_SIZE`, so `do_brk_flags` (mm/vma.c:2805-2873, Linux
v6.18.46) maps `[69632, 73728)` and `success:` returns `brk` (:207).
QEMU's user-mode `do_brk` (linux-user/syscall.c:868-913, QEMU 11.1.1)
maps `[old_brk, new_brk)` with `MAP_FIXED_NOREPLACE` (:898-900), which the
step-5 page does not meet either.  A region test started at the raw break
meets the step-5 mapping and refuses this grant.
kernel: mm/mmap.c:brk; include/linux/mm.h:vma_find; mm/vma.c:do_brk_flags@v6.18.46 -/
theorem page_crossing_grow_from_inside_a_mapping_granted :
    ∃ m', check_syscall (brk_in 69633) (mkEffect 69633 [] [(69632, 4096)]) wit_s5
      = CheckOk m' [] :=
  ⟨_, rfl⟩

/-- …and the old break is the answer there, the ledger unchanged: `out:`
returns `origbrk` (mm/mmap.c:187-190, :209-212, Linux v6.18.46).
kernel: mm/mmap.c:brk@v6.18.46 -/
theorem page_crossing_grow_into_a_mapping_answers_the_old_break :
    check_syscall (brk_in 69633) (mkEffect 67536 [] []) wit_page_above
      = CheckOk wit_page_above [] := by
  rfl

/-! ## K9 — the part's elaborator claim, pinned both ways

`Checks/VmMapsDisjoint/Witness.lean`'s header says that at the default
`maxRecDepth` plain `rfl` exceeds the depth on the munmap gate alone and on
a grant's page-rounded length alone, that `whnfCore`'s projection setting
`.yesWithDeltaI` is why, and that raising the depth is a fourth route.
The three `#guard_msgs` commands hold the failures — the gate, the rounded
length, and the munmap step they sit in — and fail this file the day any
of them closes; the examples after them close the gate, the rounded length
and the part's munmap and step-5 theorems by plain `rfl`, first with the
setting off and then at `maxRecDepth 32768`, where the NULL-hint grant
closes too.  The steps are named by
`type_of%`, so a change to the part's statement moves the pin with it.
When any of them moves, the part's header is what to reread. -/

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
/-- `check_munmap`'s `TASK_SIZE < addr + nZ` gate at the munmap step, the
rounded length already the literal, by plain `rfl` under the default
setting: the error above, on the gate alone.
model: `check_munmap`'s range gate on `(65536, 4096)`, elaborated under `.yesWithDeltaI` -/
example : decide (TASK_SIZE < bv_unsigned (65536 : word) + 4096) = false := by
  rfl

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
/-- The grant's page-rounded length against its literal, by plain `rfl`
under the default setting: the same error, on the term alone.
model: `page_round_up_Z` of one page, elaborated under `.yesWithDeltaI` -/
example : Z_to_bv 64 (page_round_up_Z (bv_unsigned (4096 : word))) = (4096 : word) := by
  rfl

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
/-- `Witness.wit_step3` by plain `rfl` under the default setting: the
recursion-depth error above is the whole of what the build prints.
model: `check_munmap` on `wit_s2`, elaborated under `.yesWithDeltaI` -/
example : type_of% LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness.wit_step3 := by
  rfl

set_option backward.isDefEq.lazyWhnfCore false in
/-- …and the gate by plain `rfl` with the setting off.
model: `check_munmap`'s range gate on `(65536, 4096)`, elaborated without `.yesWithDeltaI` -/
example : decide (TASK_SIZE < bv_unsigned (65536 : word) + 4096) = false := rfl

set_option backward.isDefEq.lazyWhnfCore false in
/-- …and the rounded length by plain `rfl` with the setting off.
model: `page_round_up_Z` of one page, elaborated without `.yesWithDeltaI` -/
example : Z_to_bv 64 (page_round_up_Z (bv_unsigned (4096 : word))) = (4096 : word) := rfl

set_option backward.isDefEq.lazyWhnfCore false in
/-- `Witness.wit_step3` by plain `rfl`, under the option that turns the
projection setting off.
model: `check_munmap` on `wit_s2`, elaborated without `.yesWithDeltaI` -/
example : type_of% LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness.wit_step3 := rfl

set_option backward.isDefEq.lazyWhnfCore false in
/-- `Witness.wit_step5` by plain `rfl`, under the same option.
model: `check_mmap`'s anonymous grant on `wit_s4`, elaborated without `.yesWithDeltaI` -/
example : type_of% LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness.wit_step5 := rfl

set_option maxRecDepth 32768 in
/-- The fourth route: the gate by plain `rfl` under the default setting,
with the depth raised.
model: `check_munmap`'s range gate on `(65536, 4096)`, elaborated under `.yesWithDeltaI` -/
example : decide (TASK_SIZE < bv_unsigned (65536 : word) + 4096) = false := rfl

set_option maxRecDepth 32768 in
/-- …the rounded length the same way.
model: `page_round_up_Z` of one page, elaborated under `.yesWithDeltaI` -/
example : Z_to_bv 64 (page_round_up_Z (bv_unsigned (4096 : word))) = (4096 : word) := rfl

set_option maxRecDepth 32768 in
/-- …`Witness.wit_step3` the same way.
model: `check_munmap` on `wit_s2`, elaborated under `.yesWithDeltaI` -/
example : type_of% LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness.wit_step3 := rfl

set_option maxRecDepth 32768 in
/-- …`Witness.wit_step5`…
model: `check_mmap`'s anonymous grant on `wit_s4`, elaborated under `.yesWithDeltaI` -/
example : type_of% LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness.wit_step5 := rfl

set_option maxRecDepth 32768 in
/-- …and the part's other grant, `Witness.wit_step5_null_hint_also_admitted`.
model: `check_mmap`'s NULL-hint anonymous grant on `wit_s4`, elaborated under `.yesWithDeltaI` -/
example :
    type_of% LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Witness.wit_step5_null_hint_also_admitted :=
  rfl

end K9

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.VmMapsDisjoint.Witness
