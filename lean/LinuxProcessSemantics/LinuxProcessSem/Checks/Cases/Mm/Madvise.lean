import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Mm.Madvise — what `madvise` admits, read off against Linux

Worked examples over `Sys.Mm.Madvise.madvise_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Mm/Madvise.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it.

HOW THESE ARE STATED.  As `Checks/Cases/Mm/Mmap.lean`'s header says: the
Lean tree has no executable checker, so a check is stated on the relation
itself, as an `iff` over EVERY outcome `o` — which for `madvise` pins the
whole admitted set every time, the arm being deterministic — and closed by
`sys_norm` (`Checks/Cases/Tactic.lean`); a forged outcome is refuted by
`sys_refute`.  The two `mmap` calls the charge scenario needs are stated
on `mmap_spec` in the same way; each such statement names one spec.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux agree.

Rocq's `madvise_scenario_grant`, the input of that scenario's two `mmap`
calls, is inlined into the two `mmap_spec` statements rather than named. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Madvise

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The spec in the `sys_simp` set

The spec and its post-state builder, at the priority
`Checks/Cases/Tactic.lean` gives every unfolding.  The gates
(`madvise_dontneed_b`, `madvise_dontneed_ok`) are decided, never unfolded,
so they are not registered — the rule that file states for `mmap`'s. -/

attribute [sys_simp low] madvise_spec.eq_1 madvise_dontneed_next.eq_1

/-- The madvise input for `addr`, `len` and `advice`; the three registers
the kernel reads (`SYSCALL_DEFINE3(madvise, …)`, mm/madvise.c:1990-1993,
Linux v6.18.46) and nothing else. -/
def madvise_in (addr len advice : word) : SyscallInput :=
  SyscallInput.mkInput 233 [addr, len, advice, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The advice values these checks spell out as numerals
(include/uapi/asm-generic/mman-common.h:45-52, Linux v6.18.46): `MADV_NORMAL`
is 0, `MADV_DONTNEED` 4, `MADV_FREE` 8; 99 is no advice value at all.
kernel: include/uapi/asm-generic/mman-common.h:MADV_DONTNEED@v6.18.46 -/
example : MADV_DONTNEED = 4 := by decide

/-! ## The argument gates, in the kernel's order

`do_madvise` (mm/madvise.c:1967-1988, Linux v6.18.46) runs
`madvise_should_skip` (mm/madvise.c:1830-1842) before anything else: the
four -EINVAL refusals of `is_valid_madvise` (mm/madvise.c:1798-1817), then
the zero-length exit that answers 0 (:1837-1840). -/

/-- A misaligned address is -EINVAL (`is_valid_madvise`,
mm/madvise.c:1805-1806, Linux v6.18.46), and the `iff` refuses every other
answer — a forged 0, a decline.
probe: testing/syscall-check/tests/madvise_dontneed.c#conform -- misaligned -/
theorem unaligned_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65537 4096 4 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- …and it is -EINVAL for EVERY advice value: the alignment test is one of
four refusals that all answer the same errno (mm/madvise.c:1802-1814, Linux
v6.18.46), so
whether the advice is `MADV_NORMAL` (0) or no value at all (99) is never
observable — the advice gate that would decline 99 sits behind it.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem unaligned_normal_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65537 4096 0 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- Nor for a value `madvise_behavior_valid` does not know (99): the
advice test comes first in `is_valid_madvise` (mm/madvise.c:1802-1803,
Linux v6.18.46) and answers the same -EINVAL as the alignment test.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem unaligned_unknown_advice_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65537 4096 99 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- A forged 0 on a misaligned address is rejected: the errno is the
kernel's only answer there (`madvise_should_skip` returns it before the
walk, mm/madvise.c:1833-1836, Linux v6.18.46).
probe: testing/syscall-check/tests/madvise_dontneed.c#reject --mutate madvise:ret=0 -- misaligned -/
theorem unaligned_forged_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65537 4096 4 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The alignment test precedes the zero-length exit: `is_valid_madvise`
refuses the address (mm/madvise.c:1805-1806, Linux v6.18.46) inside
`madvise_should_skip`'s first test (:1833-1836), before its second test
answers 0 to `len = 0` (:1837-1840).  A spec that tested `len = 0` first
would answer 0 here and keep every other pin in this file.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem unaligned_len_zero_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65537 0 4 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- …and the 0 a spec testing `len = 0` first would answer there is
refused (mm/madvise.c:1833-1840, Linux v6.18.46).
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem unaligned_len_zero_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65537 0 4 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and the wrap test: a misaligned address with a `len` whose rounding
wraps is -EINVAL from either refusal, so the answer is the same whichever
fires first (mm/madvise.c:1805-1811, Linux v6.18.46).
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem unaligned_wrapping_len_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65537 (Z_to_bv 64 (two_pow_64 - 1)) 4 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- Every advice value other than `MADV_DONTNEED` declines, including the
ones Linux answers 0 with no effect — `MADV_NORMAL` clears `VM_RAND_READ`
and `VM_SEQ_READ` (mm/madvise.c:1372-1374, Linux v6.18.46), neither set on
an anonymous grant, and `madvise_update_vma` answers 0 to unchanged flags
(mm/madvise.c:161-163) — and the ones whose effect the model could not state
(`MADV_FREE`, mm/madvise.c:1358).  A decline, never a guess: which values
are even valid is `madvise_behavior_valid`'s list under `CONFIG_KSM`,
`CONFIG_TRANSPARENT_HUGEPAGE` and `CONFIG_MEMORY_FAILURE`
(mm/madvise.c:1518-1558, Linux v6.18.46): for a value one of those
options gates — `MADV_MERGEABLE`/`MADV_UNMERGEABLE` (:1535-1538),
`MADV_HUGEPAGE`/`MADV_NOHUGEPAGE`/`MADV_COLLAPSE` (:1539-1543),
`MADV_SOFT_OFFLINE`/`MADV_HWPOISON` (:1550-1553) — one configuration
answers -EINVAL from the `default` (:1556-1557) and another acts, so no
answer is inside the intersection; for `MADV_NORMAL`, valid on every
configuration (:1523), the answer above IS in the intersection — qemu-user
answers it 0 as well (`target_madvise`, linux-user/mmap.c:1311-1320,
QEMU 11.1.1) — and the decline is a coverage cost, not a soundness one:
the arm answers one advice and declines the rest rather than carry the
configuration list.
probe: testing/syscall-check/tests/madvise_dontneed.c#fail-closed --expect-unmodeled madvise -- normal -/
theorem normal_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4096 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `MADV_FREE` (8) declines with the class: its effect, a lazily freed
page whose old contents may survive, is not one the model can state
(`madvise_free_single_vma`, reached from `madvise_dontneed_free` at
mm/madvise.c:961-962, Linux v6.18.46).
kernel: mm/madvise.c:madvise_behavior_valid,madvise_free_single_vma@v6.18.46 -/
theorem free_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4096 8 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the 0 Linux really answers `MADV_NORMAL` with is not admitted
either: nothing is, on that call.
probe: testing/syscall-check/tests/madvise_dontneed.c#fail-closed --expect-unmodeled madvise -- normal -/
theorem normal_success_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4096 0 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and -EINVAL, the answer a model carrying `madvise_behavior_valid`'s
list under the wrong configuration would give, is refused outright:
`MADV_NORMAL` is valid on every configuration (mm/madvise.c:1523, Linux
v6.18.46), so no Linux answers it with an errno.
kernel: mm/madvise.c:madvise_behavior_valid@v6.18.46 -/
theorem normal_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4096 0 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- An advice that is a NEGATIVE `int` once narrowed (`0x80000004`) falls
to `madvise_behavior_valid`'s `default` (mm/madvise.c:1556-1557, Linux
v6.18.46), -EINVAL on every configuration; the model declines it with the
rest of the class rather than carry the list, an honest decline.
kernel: mm/madvise.c:madvise_behavior_valid@v6.18.46 -/
theorem negative_advice_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4096 (Z_to_bv 64 0x80000004) i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `MADV_DONTNEED_LOCKED` (24, include/uapi/asm-generic/mman-common.h:78,
Linux v6.18.46) is the one advice `madvise_dontneed_free_valid_vma` tells
apart from `MADV_DONTNEED`: on a non-hugetlb VMA it lifts the `VM_LOCKED`
refusal (mm/madvise.c:884-885) and on hugetlb it is let through beside
`MADV_DONTNEED` (:890).  The model can build neither a locked VMA (no
`mlock` arm) nor a hugetlb one (`mmap_spec` declines `MAP_HUGETLB`), so on
every shape it reaches the two advices act alike and Linux answers 0 with
the range zapped; the value is declined with the rest of the class all
the same — the arm answers one advice — a coverage cost, not a guess.
kernel: mm/madvise.c:madvise_dontneed_free_valid_vma@v6.18.46 -/
theorem dontneed_locked_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4096 24 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the 0 Linux really answers it with over the live page is not
admitted: nothing is, on that call.
kernel: mm/madvise.c:madvise_dontneed_free_valid_vma@v6.18.46 -/
theorem dontneed_locked_success_not_admitted (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ madvise_spec 65536 4096 24 i one_map_model
        (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- The advice gate precedes the wrap test too: an unknown advice with a
wrapping `len` is -EINVAL on Linux from the advice refusal
(mm/madvise.c:1802-1803, Linux v6.18.46) and declined here — the wrap
-EINVAL is never
reached, and admitting it would guess at the advice list.
kernel: mm/madvise.c:is_valid_madvise,madvise_behavior_valid@v6.18.46 -/
theorem unknown_advice_wrapping_len_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 (Z_to_bv 64 (two_pow_64 - 1)) 99 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- The advice is read through `Syscall.int32`, in the table's arm: the
kernel's parameter is `int` (`SYSCALL_DEFINE3(madvise, unsigned long,
start, size_t, len_in, int, behavior)`, mm/madvise.c:1990-1993, Linux
v6.18.46), so the register's high half is discarded before
`madvise_behavior_valid`'s switch sees it and `2^32 + 4` IS
`MADV_DONTNEED`.  Stated through the dispatcher, where the narrowing
happens.
kernel: mm/madvise.c:madvise,madvise_dontneed_single_vma; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem advice_is_read_as_int (o : outcome SyscallEffect) :
    syscall_spec (madvise_in 65536 4096 (Z_to_bv 64 (2 ^ 32 + 4))) one_map_model o ↔
      o = Ok (mkEffect 0 [] [(65536, 4096)]) one_map_model [] := by
  sys_norm

/-- …and a model reading the whole register would decline it as an unknown
value; that decline is refused.
kernel: mm/madvise.c:madvise,madvise_should_skip; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem advice_high_half_not_read (m' : Model) (evs : List event) :
    ¬ syscall_spec (madvise_in 65536 4096 (Z_to_bv 64 (2 ^ 32 + 4))) one_map_model Unmodeled
    ∧ ¬ syscall_spec (madvise_in 65536 4096 (Z_to_bv 64 (2 ^ 32 + 4))) one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  constructor <;> sys_refute

/-- `len = 0` is 0 at an aligned address — `madvise_should_skip`'s second
exit, `start + PAGE_ALIGN(len_in) == start` (mm/madvise.c:1837-1840, Linux
v6.18.46) — with no effect and no state change.
probe: testing/syscall-check/tests/madvise_dontneed.c#conform -- zero-len -/
theorem len_zero_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 0 4 i one_map_model o ↔
      o = Ok (mkEffect 0 [] []) one_map_model [] := by
  sys_norm

/-- An errno there is rejected: -EINVAL is what `is_valid_madvise` refuses
with, and a zero `len_in` passes every one of its tests
(mm/madvise.c:1810, Linux v6.18.46, tests `len_in && !len`, which a zero
`len_in` skips).
probe: testing/syscall-check/tests/madvise_dontneed.c#reject --mutate madvise:ret=-EINVAL -- zero-len -/
theorem len_zero_errno_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 0 4 i one_map_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `len = 0` at the LARGEST page-aligned address, `2^64 - 4096`, is 0
too, and the address is what this pins.  `PAGE_ALIGN(len_in)` of a zero
`len_in` is zero (mm/madvise.c:1807, Linux v6.18.46), so `end` IS `start`:
the `len_in && !len` test is skipped because `len_in` is zero (:1810),
`start + len < start` is false (:1813) — for EVERY start, since adding
zero carries nothing — and the zero-length exit answers 0 (:1837-1840).
It is also why the wrap test and the zero-length exit may be written in
either order: Linux runs the wrap test first and this spec runs the
zero-length exit first, and `zero_len_never_wraps` below is that
agreement, proved rather than asserted.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem len_zero_at_the_last_page_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 0 4 i one_map_model o ↔
      o = Ok (mkEffect 0 [] []) one_map_model [] := by
  sys_norm

/-- …and the wrap -EINVAL is refused there: a kernel answering it read
`end` as something other than `start + PAGE_ALIGN(0)`, or tested
`end <= start` where mm/madvise.c:1813 tests `end < start` (Linux
v6.18.46).
kernel: mm/madvise.c:is_valid_madvise@v6.18.46 -/
theorem len_zero_at_the_last_page_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 0 4 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- THE TWO ORDERS AGREE AT `len = 0`, and here is the proof: once the
rounded length is zero the wrap test's condition is false for every
address, so the zero-length exit is reached whichever of the two checks
runs first.  Not a claim about Linux — closed arithmetic over the model's
own definitions — but it is the argument the `check-swap` mutant of those
two checks rests on, the one survivor of the madvise mutation sweep that
no pin can kill (`tools/lean_mutation/allowlist.Mm.Madvise.json`): no call
tells the two orders apart, so nothing observable fixes their order.
model: page_round_up_Z 0 = 0 and every word is below 2^64, so the wrap
test cannot fire on a zero length -/
theorem zero_len_never_wraps (a len : word) (h : w_is0 len = true) :
    ¬ (two_pow_64 ≤ bv_unsigned a + page_round_up_Z (bv_unsigned len)) := by
  unfold w_is0 at h
  have hlen : len = Z_to_bv 64 0 := (bv_eqb_eq _ _).mp h
  subst hlen
  have h0 : page_round_up_Z (bv_unsigned (Z_to_bv 64 0)) = 0 := by decide
  rw [h0]
  unfold two_pow_64 bv_unsigned
  have := a.isLt
  omega

/-- THE ORDER OF THE TWO GATES is what this pins: the zero-length exit sits
BEHIND the advice gate, because `is_valid_madvise` (mm/madvise.c:1802-1803,
Linux v6.18.46) runs `madvise_behavior_valid` (defined at :1517-1559)
before `madvise_should_skip` reaches its zero-length exit (:1837).  Linux answers
-EINVAL there for an invalid value and 0 for a valid one; which values are
valid is a configuration question, and `MADV_NORMAL`, valid in every
configuration (mm/madvise.c:1523, Linux v6.18.46), is outside the one
advice value the arm
answers, so `len = 0` with any other advice declines rather than
answering 0.  A spec that tested `len = 0` first
would answer 0 for every value and keep every other pin in this file.
kernel: mm/madvise.c:is_valid_madvise,madvise_behavior_valid,madvise_should_skip@v6.18.46 -/
theorem len_zero_unknown_advice_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 0 99 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- `MADV_NORMAL` with `len = 0`: Linux answers 0, `MADV_NORMAL` being valid
on every configuration (mm/madvise.c:1523, Linux v6.18.46), and the arm
declines, for the order the pin above gives.
probe: testing/syscall-check/tests/madvise_dontneed.c#fail-closed --expect-unmodeled madvise -- zero-len-normal -/
theorem len_zero_normal_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 0 0 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 a spec testing `len = 0` first would answer for an unknown
value is refused: Linux answers -EINVAL there from the advice test
(mm/madvise.c:1802-1803, Linux v6.18.46), and the arm declines.
kernel: mm/madvise.c:is_valid_madvise,madvise_behavior_valid,madvise_should_skip@v6.18.46 -/
theorem len_zero_unknown_advice_success_not_admitted (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ madvise_spec 65536 0 99 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A range whose page-rounded end reaches `2^64` is -EINVAL —
`is_valid_madvise`'s `start + len < start` (mm/madvise.c:1813-1814, Linux
v6.18.46) — as is a `len` whose rounding wraps to zero (`len_in && !len`,
:1810-1811).  Both are the one test `two_pow_64 ≤ addr + PAGE_ALIGN(len)`
in `Int`.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem wrapping_start_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 8192 4 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- …the wrapping `len`, the shape the probe's `wrap-len` case
(testing/syscall-check/tests/madvise_dontneed.c) sends the pinned kernel.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem wrapping_len_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 (Z_to_bv 64 (two_pow_64 - 1)) 4 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- The errno is -EINVAL and not `mprotect`'s -ENOMEM for the same shape
(`do_mprotect_pkey`, mm/mprotect.c:885-886, Linux v6.18.46, answers -ENOMEM
to `end <= start`):
errno choice is behavior, and a kernel reporting -ENOMEM here is lying;
the probe's `wrap-len` case forges it (`reject --mutate madvise:ret=-ENOMEM`).
probe: testing/syscall-check/tests/madvise_dontneed.c#reject --mutate madvise:ret=-ENOMEM -- wrap-len -/
theorem wrapping_len_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 (Z_to_bv 64 (two_pow_64 - 1)) 4 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- THE BOUNDARY OF THE WRAP TEST.  `start + len < start` (`is_valid_madvise`,
mm/madvise.c:1813-1814, Linux v6.18.46) is computed in `unsigned long`:
with `start = 2^64 - 4096` and `len = 4096` the sum wraps to exactly 0,
`0 < start` holds, and the answer is -EINVAL, written by
`madvise_should_skip` (:1834) before `do_madvise` takes the lock
(:1977-1979) — the range's page-rounded end reaching `2^64` EXACTLY is
inside the refusal, which is why the spec's test is `≤` and not `<`.
QEMU's user-mode emulation does NOT refuse this input: its range test
`guest_range_valid_untagged` (linux-user/mmap.c:1271, QEMU 11.1.1) is the
wrapper at include/user/guest-host.h:116-119 over
`guest_range_valid_untagged_vaddr` (:63-66), `start <= guest_addr_max -
len + 1`, inclusive of a range whose last byte is `guest_addr_max`, and
for a riscv64 guest run without `-R` that is `~0ul` (linux-user/main.c:847-852,
QEMU 11.1.1; `TARGET_VIRT_ADDR_SPACE_BITS` is 48, target/riscv/cpu-param.h:12,
QEMU 11.1.1), so `target_madvise` passes its gates (linux-user/mmap.c:1264-1273,
QEMU 11.1.1), reaches the `MADV_DONTNEED` arm's `page_check_range(start,
len, PAGE_PASSTHROUGH)` (:1334-1341), false for a range no guest page
occupies, and returns 0 — the path its own comment calls "(wrongly!)
return success, which is broken" (:1303-1307).  AGENTS.md
does not accept a deviation an implementation itself calls a bug, so Linux's
-EINVAL stays the answer; the intersection of what the two REALLY return
here is nonetheless empty, and `bugs/madvise-wrap-boundary-qemu-user-answers-zero.md`
records it.  The two pins above sit one and sixteen pages PAST the
boundary; this one sits ON it, so a test shifted or flipped by one —
`2^64 + 1 ≤ …`, `2^64 < …` — no longer agrees with the kernel here and is
refused below.  The probe (`wrap-boundary` in
testing/syscall-check/tests/madvise_dontneed.c) needs no mapping: Linux
refuses before it reads a VMA.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem wrap_boundary_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 4 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- The mistake the boundary pin exists for: a wrap test that lets the
exact boundary through falls to the ledger gate, where `2^64 - 4096` is
in no mapping and the arm DECLINES — but Linux refuses before it reads
the VMAs, so a decline here would drop Linux's -EINVAL (`is_valid_madvise`
returns false at :1813-1814 and `madvise_should_skip` writes the errno at
:1834, so `do_madvise` never reaches the walk).  Refused outright, beside
the two shapes of 0 refused below.  This is the pin that locks the spec to
Linux alone at the boundary: qemu-user answers 0 here by a path its own
source calls broken (the docstring above and the `bugs/` entry it names),
so if Rocq's `madvise_spec` ever declines the exact boundary instead, this
pin and every `iff` in this file proving -EINVAL for a sum of exactly
`2^64` with a rounded length below it — `wrap_boundary_is_einval`, its
twin on `last_page_model` below, and the `wrap_edge_*` `iff`s further
down — are the pins to flip; the refusals of 0 hold under either stance.
kernel: mm/madvise.c:madvise_should_skip@v6.18.46 -/
theorem wrap_boundary_unmodeled_rejected (i : SyscallInput) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 4 i one_map_model Unmodeled := by
  sys_refute

/-- qemu-user's exact answer at the boundary — 0 with NOTHING zapped:
`target_madvise` skips the host call when `page_check_range` is false and
returns the `ret = 0` set at linux-user/mmap.c:1262 (:1334-1341, :1363,
QEMU 11.1.1) — refused, on the reading the `bugs/` entry records: Linux
writes -EINVAL in `madvise_should_skip` (mm/madvise.c:1834, Linux
v6.18.46) and no implementation zaps here.  The harness twin, the probe's
`reject --mutate madvise:ret=0 -- wrap-boundary` case, forges the same 0
on the pinned kernel's trace and the checker must refuse it.
kernel: mm/madvise.c:madvise_should_skip@v6.18.46 -/
theorem wrap_boundary_qemu_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 4 i one_map_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and the model's own success shape — 0 with the boundary page
zero-filled — is refused too: the answer an arm would give if its wrap
test let the boundary through to a ledger holding the top page.  On
`one_map_model` no ledger does, so a mutant of the test declines here
rather than answering; `last_page_model` below is where this shape is the
mutant's answer.
kernel: mm/madvise.c:madvise_should_skip@v6.18.46 -/
theorem wrap_boundary_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 4 i one_map_model
        (Ok (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 4096), 4096)]) m' evs) := by
  sys_refute

/-- The last page of the word, live: `[2^64 - 4096, 2^64)` mapped rw.  No
real run holds it — every range Linux hands back sits below
`State.alloc_top`, and the page is above `TASK_SIZE` on every
address-space size — so only a hand-built model can put a mapping under
the boundary and ask which fires first, the wrap test or the ledger
(the `near_ceiling_sum_model` note in the Prelude). -/
def last_page_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (two_pow_64 - 4096), 4096)] [] 0 0 demo_limit 0 demo_sp)

/-- ORDER IS BEHAVIOUR: the wrap test fires before the ledger is read.  Over
a live top page the answer is still -EINVAL, because Linux refuses in
`madvise_should_skip` (mm/madvise.c:1834, Linux v6.18.46) before
`do_madvise` takes the lock (:1979) or walks a VMA (:1983); no zap, no 0.
This is the fixture on which a shifted or flipped test ANSWERS instead of
declining — `2^64 + 1 ≤ …` or `2^64 < …` lets the boundary through to the
live page and zero-fills it — so the refusal below kills it there, where
`wrap_boundary_unmodeled_rejected` cannot (as `wrap_edge_at_two_pow_64_zap_rejected`
does on its own ledger further down).
kernel: mm/madvise.c:madvise_should_skip,do_madvise@v6.18.46 -/
theorem wrap_boundary_over_live_page_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 4 i last_page_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) last_page_model [] := by
  sys_norm

/-- …the zero-filled success a late wrap test would answer over the live
top page, refused: Linux never reaches the VMA (`do_madvise` returns at
mm/madvise.c:1977-1978, Linux v6.18.46).
kernel: mm/madvise.c:do_madvise@v6.18.46 -/
theorem wrap_boundary_over_live_page_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 4096)) 4096 4 i last_page_model
        (Ok (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 4096), 4096)]) m' evs) := by
  sys_refute

/-- …and the page BELOW the boundary is not -EINVAL: `start + len` is
`2^64 - 4096`, above `start`, so `is_valid_madvise` passes (mm/madvise.c:1813-1814,
Linux v6.18.46) and the walk answers -ENOMEM for the hole (:1651-1652) —
which the model does not carry, so the arm declines: the wrap test does
not fire early.  The intersection is empty here too — Linux -ENOMEM,
qemu-user 0 by the passthrough path the `bugs/` entry records — and the
model proves neither; the probe's `below-wrap` case records the kernel's
-ENOMEM beside the decline.
kernel: mm/madvise.c:is_valid_madvise,madvise_walk_vmas@v6.18.46 -/
theorem below_wrap_boundary_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- -EINVAL is nobody's answer one page below the boundary — Linux passes
the wrap test (mm/madvise.c:1813-1814, Linux v6.18.46) and answers -ENOMEM
from the walk (:1651-1652), qemu-user answers 0 — so an arm whose wrap
test fired a page early would answer what no implementation does.
kernel: mm/madvise.c:is_valid_madvise,madvise_walk_vmas@v6.18.46 -/
theorem below_wrap_boundary_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4 i one_map_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and Linux's own -ENOMEM is not admitted either, as
`free_range_enomem_not_admitted` says of every hole: the arm answers one
shape and declines the rest (`madvise_walk_vmas`, mm/madvise.c:1651-1652,
Linux v6.18.46).
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem below_wrap_boundary_enomem_not_admitted (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- …nor qemu-user's 0 (the passthrough path, linux-user/mmap.c:1334-1341
and :1363, QEMU 11.1.1): nothing is, on that call.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem below_wrap_boundary_qemu_success_not_admitted (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4 i one_map_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- One page below the boundary over a LIVE page the arm answers: the wrap
test does not fire early even where the ledger would let a success
through (`is_valid_madvise` passes, mm/madvise.c:1813-1814, Linux
v6.18.46), which the hole decline above cannot show — it declines for the
hole whatever the test did.  `near_ceiling_sum_model` maps exactly that
page.
kernel: mm/madvise.c:is_valid_madvise@v6.18.46 -/
theorem below_wrap_boundary_over_live_page_answers (i : SyscallInput)
    (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4 i near_ceiling_sum_model o ↔
      o = Ok (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)]) near_ceiling_sum_model [] := by
  sys_norm

/-! ### The wrap test at its own edge

`is_valid_madvise` rounds `len = PAGE_ALIGN(len_in)` and refuses
`start + len < start` (mm/madvise.c:1807 and :1813-1814, Linux v6.18.46);
that sum is what `madvise_do_behavior` later forms again as `range->end`
(:1884, from the untagged `start` of :1883 — `start` itself on a modeled
run, by the `pmlen` argument in `Sys/Mm/Mprotect.lean`'s header), and
`is_valid_madvise` itself never names it.  It is computed in
`unsigned long`, so the refusal's edge is exactly `2^64`: a sum of `2^64`
wraps to 0 and is refused, a sum of `2^64 - 4096` — the last page of the
address space left out — is not.  The `iff` pins below share the start
and the ledger and differ in `len` alone: 8192 sums to the edge, 4096
stops a page short, 4097 rounds up to 8192 and reaches the edge through
the rounding.  No Linux places a mapping this high (`TASK_SIZE` is far
below `2^64` on every riscv64 layout), so the ledger that owns the last
two pages is hand-built, as `Prelude.near_ceiling_sum_model` is, and it is
built so that the wrap test is the ONLY thing separating the two answers:
the range each call names is wholly owned, so a spec that let the call
past the test would answer with the zap.

QEMU'S USER-MODE EMULATION DOES NOT AGREE AT THE EDGE, and the spec header's
"QEMU agrees on both refusals" was measured a page past it (the Rocq
`Sys/Mm/Madvise.v` note; `wrapping_start_is_einval` is that call).
`guest_range_valid_untagged` (include/exec/cpu_ldst.h, QEMU 8.2.2) tests
`start <= GUEST_ADDR_MAX - len + 1` with no wrap, and `GUEST_ADDR_MAX` is
`~0ul` for a 64-bit guest run without `-R` (include/exec/cpu-all.h;
`reserved_va` stays 0 by default when `TARGET_VIRT_ADDR_SPACE_BITS`
exceeds 32, linux-user/main.c, QEMU 8.2.2), so a range ending exactly at
`2^64` passes the check that refuses `2^64 + 4096`; `target_madvise`
(linux-user/mmap.c, QEMU 8.2.2) then answers 0 to `MADV_DONTNEED` over
pages that are not `PAGE_PASSTHROUGH` — every unmapped page — and its own
comment calls that "(wrongly!) return success, which is broken".  A
deviation an implementation declares against its own semantics is not a
real behavior under AGENTS.md's bug clause, so that 0 stays outside the
admitted set and the -EINVAL below is the intersection's answer.  This
stops holding if QEMU's emulation is fixed to answer anything but -EINVAL
here; a run under `-R` with a `reserved_va` below the edge refuses the
range and agrees already. -/

/-- The last two pages of the address space, `[2^64 - 8192, 2^64)`, owned
as one live rw mapping.  Not a reachable state (see above). -/
def madvise_top_two_pages : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (two_pow_64 - 8192), 8192)] [] 0 0 demo_limit 0
    demo_sp)

/-- A sum of exactly `2^64` is -EINVAL: `start + len` wraps to 0, so
`start + len < start` holds and `madvise_should_skip` reports the errno
(mm/madvise.c:1813-1814
and :1833-1836, Linux v6.18.46) before `do_madvise` takes a lock or walks
a VMA at all (:1977 runs before :1979 and :1983).  That the range is
wholly owned changes nothing — the test is arithmetic on the arguments.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip,do_madvise@v6.18.46 -/
theorem wrap_edge_at_two_pow_64_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 8192 4 i madvise_top_two_pages o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) madvise_top_two_pages [] := by
  sys_norm

/-- …so the zap of that range is not admitted.  It is the answer an
off-by-one in the model's ceiling test would give — a strict `<` where a
sum of exactly `2^64` must still be refused, or a ceiling one higher —
while the kernel refuses it through `start + len < start` on the wrapped
sum.  That is why the edge owes a pin of its own: `wrapping_start_is_einval` above sums to
`2^64 + 4096` and is answered the same way under either mistake.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem wrap_edge_at_two_pow_64_zap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 8192 4 i madvise_top_two_pages
        (Ok (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 8192), 8192)]) m' evs) := by
  sys_refute

/-- One page below the edge the sum is `2^64 - 4096`, which does not wrap,
so `is_valid_madvise` passes the call — and then, GIVEN a VMA covering the
range, which this ledger supplies and no real Linux does,
`madvise_dontneed_single_vma` zaps the page and answers 0
(mm/madvise.c:859-872, Linux v6.18.46).  Over a hole the walk would answer
-ENOMEM instead (:1651-1652), which is the `map_contains` conjunct's own
pin, `free_range_is_unmodeled`; what this pin fixes is the wrap test.
Same start, same ledger, `len` 4096 where the pin above has 8192.
kernel: mm/madvise.c:is_valid_madvise,madvise_dontneed_single_vma@v6.18.46 -/
theorem wrap_edge_one_page_below_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4 i madvise_top_two_pages o ↔
      o = Ok (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)])
          madvise_top_two_pages [] := by
  sys_norm

/-- …and -EINVAL there is refused: a kernel answering the wrap errno one
page below the edge put the refusal's ceiling a page too low — refused an
`end` at or above the last page, `2^64 - 4096` — where
mm/madvise.c:1813-1814 (Linux v6.18.46) refuses only a sum that wrapped
past `2^64`.  NOT the `end <= start` mistake: here `end = 2^64 - 4096`
lies above `start = 2^64 - 8192`, so `end <= start` is false exactly as
`end < start` is, and a kernel with that mistake answers 0 on this call
too.  `<=` is told apart from `<` only where `end = start`, a zero rounded
length, which is `len_zero_at_the_last_page_einval_rejected`'s call.
kernel: mm/madvise.c:is_valid_madvise@v6.18.46 -/
theorem wrap_edge_one_page_below_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4 i madvise_top_two_pages
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The ROUNDED length is what reaches the wrap test: a `len_in` of 4097 is
rounded by `PAGE_ALIGN` to 8192 (mm/madvise.c:1807, Linux v6.18.46) before
`start + len < start` (:1813-1814) sees it, so at `2^64 - 8192` it sums to
the edge and is refused, where an unrounded 4097 would sum to `2^64 - 4095`
and pass.  Same start and ledger as the pins above; `len` 4097 where they
have 8192 and 4096.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem wrap_edge_rounded_len_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4097 4 i madvise_top_two_pages o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) madvise_top_two_pages [] := by
  sys_norm

/-- …so the zap a spec summing the UNROUNDED length would answer with — its
zero-fill still page-rounded to 8192, the rounding downstream being fixed
by `len_rounds_up_to_the_page` — is refused: Linux never reaches
`madvise_dontneed_single_vma` (mm/madvise.c:859-872, Linux v6.18.46) on
this call.  No mutation operator forms that spec, so this pin is the only
thing fixing WHERE the rounding sits.
kernel: mm/madvise.c:is_valid_madvise,madvise_dontneed_single_vma@v6.18.46 -/
theorem wrap_edge_unrounded_zap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec (Z_to_bv 64 (two_pow_64 - 8192)) 4097 4 i madvise_top_two_pages
        (Ok (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 8192), 8192)]) m' evs) := by
  sys_refute

/-- The edge reached through the LENGTH alone: at `start = 0` a `len_in` of
`2^64 - 1` rounds to a `PAGE_ALIGN(len_in)` of 0, so `len_in && !len`
(mm/madvise.c:1810-1811, Linux v6.18.46) refuses it — `start + len < start`
at :1813 is `0 < 0`, false, and would not.  In the spec's one `Int` test the
rounded length is exactly `2^64` and so is the sum; the address contributes
nothing, so this is the wrapped-length refusal at ITS edge, where
`wrapping_len_is_einval` sums past it.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem wrapped_len_at_addr_zero_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 0 (Z_to_bv 64 (two_pow_64 - 1)) 4 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model [] := by
  sys_norm

/-- …and the decline is refused there: a spec whose ceiling test let a sum
of exactly `2^64` through would round `len` to a zero-length word, find
address 0 in no mapping of the ledger, and decline — an `unmodeled` where
Linux answers -EINVAL from `len_in && !len` (mm/madvise.c:1810-1811, Linux
v6.18.46) without reading a VMA.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip@v6.18.46 -/
theorem wrapped_len_at_addr_zero_decline_rejected (i : SyscallInput) :
    ¬ madvise_spec 0 (Z_to_bv 64 (two_pow_64 - 1)) 4 i one_map_model Unmodeled := by
  sys_refute

/-! ## The answered shape, and the three ways to leave it

Past the gates `madvise_walk_vmas` (mm/madvise.c:1624-1697, Linux v6.18.46)
applies `madvise_vma_behavior` to each VMA the range meets; for
`MADV_DONTNEED` that is `madvise_dontneed_free` (:906) and, on an ordinary
anonymous VMA, `madvise_dontneed_single_vma` (:859-872): the range is
zapped and the answer is 0. -/

/-- Over a whole live rw grant: 0 and the zero-fill of the range, and
nothing else — no errno, no decline.  With nothing lazy in the ledger the
post-model is the pre-model: `madvise_dontneed_single_vma` touches no
accounting and unmaps nothing (mm/madvise.c:868-871, Linux v6.18.46).
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem dontneed_whole_grant (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4096 4 i one_map_model o ↔
      o = Ok (mkEffect 0 [] [(65536, 4096)]) one_map_model [] := by
  sys_norm

/-- The zero-fill is load-bearing: a 0 that keeps the bytes is a kernel
that did not zap the range (`madvise_dontneed_single_vma`,
mm/madvise.c:868-870, Linux v6.18.46; the zap itself is
`zap_page_range_single_batched`, mm/memory.c:2138, Linux v6.18.46), and is
rejected.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem without_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4096 4 i one_map_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- No errno is injectable on the answered shape: `madvise_lock` takes no
killable lock for `MADV_DONTNEED` (`get_lock_mode` gives it
`MADVISE_VMA_READ_LOCK`, mm/madvise.c:1720-1723, Linux v6.18.46, and only
`MADVISE_MMAP_WRITE_LOCK` can answer -EINTR, :1737-1739), and the walk's
-ENOMEM needs a hole (:1662).  -ENOMEM, -EINTR and a return of 1 are each
rejected.
kernel: mm/madvise.c:get_lock_mode,madvise_lock,madvise_walk_vmas@v6.18.46 -/
theorem enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4096 4 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- -EINTR: `MADV_DONTNEED` takes `MADVISE_VMA_READ_LOCK`, never the killable
write lock (mm/madvise.c:1720-1723 and :1737-1739, Linux v6.18.46).
kernel: mm/madvise.c:get_lock_mode,madvise_lock@v6.18.46 -/
theorem eintr_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4096 4 i one_map_model
        (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  sys_refute

/-- A return of 1: `madvise_dontneed_single_vma` returns 0 after the zap
(mm/madvise.c:868-871, Linux v6.18.46), so a positive return over a
whole live grant is no kernel's.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem nonzero_return_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4096 4 i one_map_model
        (Ok (mkEffect 1 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-- The answered shape never declines.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem dontneed_never_unmodeled (i : SyscallInput) :
    ¬ madvise_spec 65536 4096 4 i one_map_model Unmodeled := by
  sys_refute

/-- `len` is page-rounded before the walk: `is_valid_madvise` rounds it
(mm/madvise.c:1807, Linux v6.18.46) and `madvise_do_behavior` zaps
`[start, start + PAGE_ALIGN(len_in))` (:1884), so `len = 4095` zaps the
whole page and the zero-fill covers it; a zero-fill of 4095 bytes is
rejected.
kernel: mm/madvise.c:is_valid_madvise,madvise_do_behavior@v6.18.46 -/
theorem len_rounds_up_to_the_page (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4095 4 i one_map_model o ↔
      o = Ok (mkEffect 0 [] [(65536, 4096)]) one_map_model [] := by
  sys_norm

/-- …so a zero-fill of the unrounded 4095 bytes is refused: the zap covers
`[start, start + PAGE_ALIGN(len_in))` (mm/madvise.c:1807 and :1884,
Linux v6.18.46).
kernel: mm/madvise.c:is_valid_madvise,madvise_do_behavior@v6.18.46 -/
theorem len_unrounded_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4095 4 i one_map_model (Ok (mkEffect 0 [] [(65536, 4095)]) m' evs) := by
  sys_refute

/-- …and the rounded length is what the containment gate sees: `len = 4097`
over a one-page grant reaches into the next page, which the ledger does not
own, and declines like `partial_grant_is_unmodeled` below (the walk's
-ENOMEM for the hole, mm/madvise.c:1662 and :1696, Linux v6.18.46).
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem len_4097_over_one_page_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4097 4 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- A range with a page outside the grant declines.  Linux applies the
advice to the mapped page and reports -ENOMEM for the hole
(`madvise_walk_vmas` sets `unmapped_error` at mm/madvise.c:1662 and
carries on, returning it at :1696, Linux v6.18.46): a state change AND an
errno at once, over pages the ledger cannot name, so the model does not
answer — the `map_contains` conjunct of `madvise_dontneed_ok`.  Neither
the kernel's own answer nor a plain 0 is admitted.
probe: testing/syscall-check/tests/madvise_dontneed.c#fail-closed --expect-unmodeled madvise -- hole -/
theorem partial_grant_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 8192 4 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so neither the kernel's own answer over the hole (-ENOMEM with the
mapped page zapped, mm/madvise.c:1662 and :1696, Linux v6.18.46) nor a
plain 0 is admitted.
probe: testing/syscall-check/tests/madvise_dontneed.c#fail-closed --expect-unmodeled madvise -- hole -/
theorem partial_grant_answers_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 8192 4 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] [(65536, 4096)]) m' evs)
    ∧ ¬ madvise_spec 65536 8192 4 i one_map_model
        (Ok (mkEffect 0 [] [(65536, 8192)]) m' evs) := by
  constructor <;> sys_refute

/-- A range the ledger holds nothing of declines, whether below the run's
`alloc_top` (a hole: the walk answers -ENOMEM, mm/madvise.c:1645-1662
and :1696, Linux v6.18.46) or at the bottom of the stack band above it,
where Linux answers the same -ENOMEM unless the stack has already grown
down to that page — `madvise` walks the VMAs there are and grows none,
`expand_stack_locked` (mm/mmap.c, Linux v6.18.46) being the fault path's —
and zaps it with 0 if it has.  The ledger carries neither the hole nor
the stack, so both fall on the same `map_contains` test; the second is the
same pin at the one address a reader would ask about.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem free_range_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 131072 4096 4 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- The same decline at the bottom of the stack band (`demo_top`): Linux
answers -ENOMEM there unless the stack has grown down to the page, and
zaps it with 0 if it has (`madvise_walk_vmas`, mm/madvise.c:1662 and
:1696, Linux v6.18.46); the ledger carries the stack in neither case.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem stack_band_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec (Z_to_bv 64 demo_top) 4096 4 i one_map_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the -ENOMEM Linux answers for the hole (mm/madvise.c:1645-1662 and :1696,
Linux v6.18.46) is not admitted: the arm declines rather than answer.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem free_range_enomem_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 131072 4096 4 i one_map_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- The image's LOAD pages decline even on a ledger that also lists them in
`vm_maps` — the `vm_reserved` conjunct.  Linux zaps a private file-backed
page like any other and it reads back FILE CONTENTS afterwards, which the
model cannot state (the Rocq header's argument).  No reachable state has
such a ledger, so this pins the conjunct on the one fixture that can reach
it.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem image_range_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 4096 4096 4 i noaccess_image_overlap o ↔ o = Unmodeled := by
  sys_norm

/-- …so the 0 and zero-fill of an anonymous page is not admitted over an
image page, which `madvise_dontneed_single_vma` (mm/madvise.c:859-872,
Linux v6.18.46) zaps back to its file contents.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem image_range_zeros_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 4096 4096 4 i noaccess_image_overlap
        (Ok (mkEffect 0 [] [(4096, 4096)]) m' evs) := by
  sys_refute

/-- A `PROT_NONE` range declines: Linux answers 0 there
(`madvise_dontneed_free_valid_vma`, mm/madvise.c:875-904, Linux v6.18.46,
refuses `VM_PFNMAP`, `VM_LOCKED` under plain `MADV_DONTNEED`, and a
hugetlb VMA only for another advice or an unaligned start — never a
protection),
but the machine overlay holds no bytes for a protected page to zap, and
re-exposing one is `mprotect`'s zero-fill, not this arm's — the
`vm_noaccess` conjunct.  The 0 is not admitted either.
probe: testing/syscall-check/tests/madvise_dontneed.c#fail-closed --expect-unmodeled madvise -- noaccess -/
theorem noaccess_range_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 4096 4 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 Linux answers over the `PROT_NONE` page is not admitted.
probe: testing/syscall-check/tests/madvise_dontneed.c#fail-closed --expect-unmodeled madvise -- noaccess -/
theorem noaccess_range_zeros_not_admitted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ madvise_spec 65536 4096 4 i noaccess_three_pages
        (Ok (mkEffect 0 [] [(65536, 4096)]) m' evs) := by
  sys_refute

/-! ## What the arm is for: giving first-touch charges back

A two-page budget and a two-page `MAP_NORESERVE` grant.  Flags 16418 is
`MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE`. -/

/-- `MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE`, the lazy grant's flags.
kernel: include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS; include/uapi/asm-generic/mman.h:MAP_NORESERVE@v6.18.46 -/
example : MAP_PRIVATE + MAP_ANONYMOUS + MAP_NORESERVE = 16418 := by decide
/-- `MAP_PRIVATE|MAP_ANONYMOUS`, the eager grant's flags.
kernel: include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS@v6.18.46 -/
example : MAP_PRIVATE + MAP_ANONYMOUS = 34 := by decide

/-- An empty ledger under a two-page budget. -/
def madvise_lazy_base : Model :=
  fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 8192 0 demo_sp)

/-- The two-page grant at 65536, lazily backed. -/
def madvise_lazy_granted : Model :=
  vm_add_lazy 65536 8192 (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp))

/-- A `MAP_NORESERVE` grant placed at 65536 lands in the ledger as
`madvise_lazy_granted`: the mapping owned, its interior lazy, nothing
charged.  `do_mmap` turns the bit into `VM_NORESERVE` outside strict
overcommit (mm/mmap.c, Linux v6.18.46; the argument is on
`Mmap.MAP_NORESERVE`), and the placement at 65536 is one the kernel may
make.
no-row: madvise_dontneed records this call at seq 0 of traces 001-006 and 012-014, but its effect zero-fills the grant and the oracle-pin corpus scan keeps no row for an effect that zeroes; the placement at 65536 is the fixture's choice.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem lazy_grant (i : SyscallInput) :
    mmap_spec 0 8192 3 16418 mmap_fd_none 0 i madvise_lazy_base
      (Ok (mkEffect 65536 [] [(65536, 8192)]) madvise_lazy_granted []) := by
  sys_norm

/-- The same grant placed by `MAP_FIXED_NOREPLACE` at the address a
sanitizer runtime names (flags 1064994, MAP_PRIVATE|MAP_ANONYMOUS
|MAP_NORESERVE|MAP_FIXED_NOREPLACE) lands as the same lazy entry: the
post-model IS `madvise_lazy_granted`, so every madvise pin below holds of
a NOREPLACE-placed shadow mapping unchanged.  Rocq:
`madvise_lazy_grant_by_noreplace`.
no-row: madvise_dontneed records this shape at seq 2 of traces 004-006, at the address its seq-0 grant returned rather than 65536, and that effect zero-fills the grant, which the oracle-pin corpus scan keeps no row for.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem lazy_grant_by_noreplace (i : SyscallInput) :
    mmap_spec 65536 8192 3 1064994 mmap_fd_none 0 i madvise_lazy_base
      (Ok (mkEffect 65536 [] [(65536, 8192)]) madvise_lazy_granted []) := by
  sys_norm

/-- The grant costs nothing until a page is touched; the first touch
charges that page and no other (`State.materialize_model_accesses`, the
model's reading of a first fault on a `VM_NORESERVE` page). -/
def madvise_lazy_touched : Model :=
  with_vm_backing (m_vm_lazy madvise_lazy_granted) [65536] madvise_lazy_granted

/-- The grant costs nothing, the first touch charges one page, and the
budget reads that page back: the model's reading of a first fault, not
a claim about `madvise`.
model: the model's own first-touch accounting over `State.materialize_model_accesses`, closed over fixtures; no spec and no Linux line -/
theorem lazy_first_touch_charges :
    vm_backing_used madvise_lazy_granted = 0
    ∧ materialize_model_accesses madvise_lazy_granted [(65536, 1)] = some madvise_lazy_touched
    ∧ vm_backing_used madvise_lazy_touched = 4096 := by
  refine ⟨by decide, rfl, by decide⟩

/-- `MADV_DONTNEED` over the grant returns the charge: the post-model IS
the pre-touch model — same mapping, same lazy provenance, no materialized
page.  Linux frees the zapped page (`madvise_dontneed_single_vma`,
mm/madvise.c:868-870, Linux v6.18.46; the zap itself is
`zap_page_range_single_batched`, mm/memory.c:2138, Linux v6.18.46) and
faults it in fresh on the next touch, which is what "lazy again" models.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem dontneed_returns_the_charge (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 8192 4 i madvise_lazy_touched o ↔
      o = Ok (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_granted [] := by
  sys_norm

/-- A 0 that KEEPS the charge — the post-model still holding the
materialized page — is a kernel that did not free the page, and is
rejected.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem dontneed_kept_charge_rejected (i : SyscallInput) (evs : List event) :
    ¬ madvise_spec 65536 8192 4 i madvise_lazy_touched
        (Ok (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_touched evs) := by
  intro h
  sys_refute at h

/-- Read off the post-state function directly: the budget is back to its
pre-touch value, the lazy provenance and the ledger are untouched, and only
the materialized list moved.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem dontneed_budget_back_to_pre_touch :
    vm_backing_used (madvise_dontneed_next madvise_lazy_touched 65536 8192) = 0
    ∧ m_vm_lazy (madvise_dontneed_next madvise_lazy_touched 65536 8192) = [(65536, 8192)]
    ∧ m_vm_materialized (madvise_dontneed_next madvise_lazy_touched 65536 8192) = []
    ∧ m_vmmaps (madvise_dontneed_next madvise_lazy_touched 65536 8192)
        = m_vmmaps madvise_lazy_touched := by
  refine ⟨by decide, by decide, by decide, rfl⟩

/-- The pages are lazy again, not free: the next touch charges the page
exactly as the first one did.  Documentary rather than a pin —
`materialize_model_accesses` is idempotent on a page still charged, so a
spec that never gave the page back passes this too; the pin is
`dontneed_returns_the_charge` above.
model: documentary; `materialize_model_accesses` over the arm's post-state, pinned by `dontneed_returns_the_charge` -/
theorem dontneed_next_touch_recharges :
    materialize_model_accesses (madvise_dontneed_next madvise_lazy_touched 65536 8192)
      [(65536, 1)] = some madvise_lazy_touched := by
  sys_norm

/-- Only the pages IN the range are given back — `zap_page_range_single_batched`
is called over `[range->start, range->end)` and nothing wider
(mm/madvise.c:868-870, Linux v6.18.46).  Both pages touched, `DONTNEED`
over the second: the first keeps its charge. -/
def madvise_lazy_both_touched : Model :=
  with_vm_backing (m_vm_lazy madvise_lazy_granted) [69632, 65536] madvise_lazy_granted

/-- Over the second page only: the first page keeps its charge and only
the second's comes back (mm/madvise.c:868-870, Linux v6.18.46).
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem dontneed_only_the_range (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 69632 4096 4 i madvise_lazy_both_touched o ↔
      o = Ok (mkEffect 0 [] [(69632, 4096)]) madvise_lazy_touched [] := by
  sys_norm

/-- What the two fixtures above cost: two charged pages before the call and
one after.
model: the budgets of the two fixtures `dontneed_only_the_range` relates, read off `vm_backing_used` -/
theorem dontneed_only_the_range_budgets :
    vm_backing_used madvise_lazy_both_touched = 8192
    ∧ vm_backing_used madvise_lazy_touched = 4096 := by
  refine ⟨by decide, by decide⟩

/-- …and giving back BOTH pages for a one-page call is rejected.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem dontneed_wider_than_the_range_rejected (i : SyscallInput) (evs : List event) :
    ¬ madvise_spec 69632 4096 4 i madvise_lazy_both_touched
        (Ok (mkEffect 0 [] [(69632, 4096)]) madvise_lazy_granted evs) := by
  intro h
  sys_refute at h

/-! ### The scenario from issue #683, end to end

Two pages granted lazily and both touched fill the two-page budget: a
further one-page eager grant (flags 34 = `MAP_PRIVATE|MAP_ANONYMOUS`) cannot
be admitted, only its -ENOMEM can.  After `MADV_DONTNEED` over the two
pages the same grant fits.  Without the arm the model has no way back from
the first state, and a program that recycles its pages runs out of the
budget where Linux does not. -/

/-- With the budget spent the grant is forced to -ENOMEM: no placement is
admissible (the budget gate sits inside `mmap_spec`'s success guard, so
the `alt` collapses onto the errno arm; `Checks/Cases/Mm/Mmap.lean`'s
budget section cites the kernel's own commit charge).
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem scenario_grant_refused_while_charged (i : SyscallInput) (o : outcome SyscallEffect) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i madvise_lazy_both_touched o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) madvise_lazy_both_touched [] := by
  sys_norm

/-- After `MADV_DONTNEED` over both pages the model is the untouched grant
again — stated as that independently written model, not as the arm's own
post-state function, so the content is what is pinned.
probe: testing/syscall-check/tests/madvise_dontneed.c#conform --alloc-limit 0x2000 -- budget -/
theorem scenario_dontneed (i : SyscallInput) (o : outcome SyscallEffect) :
    madvise_spec 65536 8192 4 i madvise_lazy_both_touched o ↔
      o = Ok (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_granted [] := by
  sys_norm

/-- …and the same grant now fits: a placement at 131072 is admitted with
the ledger extended and the lazy backing untouched.
probe: testing/syscall-check/tests/madvise_dontneed.c#conform --alloc-limit 0x2000 -- budget -/
theorem scenario_grant_fits_after_dontneed (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i madvise_lazy_granted
      (Ok (mkEffect 131072 [] [(131072, 4096)])
          (with_vmmaps (VmMaps.mkVmMapsFull [] [(131072, 4096), (65536, 8192)] [] 0 0 8192 0 demo_sp)
            madvise_lazy_granted) []) := by
  sys_norm

/-- An EAGERLY charged grant keeps its charge across the call, as Linux
keeps the VMA's commit (`madvise_dontneed_single_vma` touches no
accounting, mm/madvise.c:859-872, Linux v6.18.46): the budget does not
move.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem eager_grant_keeps_its_charge :
    vm_backing_used one_map_model = 4096
    ∧ vm_backing_used (madvise_dontneed_next one_map_model 65536 4096) = 4096 := by
  refine ⟨by decide, by decide⟩

/-! ## The dispatcher -/

/-- Syscall 233 reaches `madvise_spec` with a0, a1 and the narrowed a2:
the alignment -EINVAL is decided before the model is read, so this holds
of every model.
probe: testing/syscall-check/tests/madvise_dontneed.c#conform -- misaligned -/
theorem sysno_233_is_madvise (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (madvise_in 65537 4096 4) m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Madvise
