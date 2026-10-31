import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Madvise
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Mm.Madvise — the madvise checker, read off against Linux

Pins over `Checks.Sys.Mm.Madvise`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Mm/Madvise.v` and of
`theories/LinuxProcessSem/Checks/Witness/Mm/Madvise.v`.  The Rocq tree
states its worked examples over `madvise` in
`theories/LinuxProcessSem/Checks/Cases/Mm/Madvise.v`, through the
dispatcher (`check_syscall (madvise_in …)`).  The Lean `check_syscall`
(`Checks/ExecutableSpecs.lean`, K3) reads `checked_table`, and that table
has no madvise row until the V ticket's registration, so through it every
madvise input declines here; each example is therefore restated on
`check_madvise` itself, with the one narrowing the dispatcher would apply —
`int32` on the advice register — written where Rocq relied on the
dispatcher for it.  The restatement through `check_syscall` goes with the
row, as the C-ticket acceptance says.
Placed at `Checks/Cases/<mirror path>` like every other pin in this tree,
so the checker file holds only definitions and their Rocq-twin lemmas.
Not part of the trusted specification: this file is QA on the checker,
written to be READ.

Each example of the Rocq file whose subject is the madvise CHECKER is
here under the Rocq name.  Not here, and why: the four examples over the
mmap arm (`madvise_lazy_grant`, `madvise_lazy_grant_by_noreplace`,
`madvise_scenario_grant_refused_while_charged`,
`madvise_scenario_grant_fits_after_dontneed`) call `check_syscall` on an
mmap input, which this file's imports do not reach, so their
checker-level twins belong with the mmap checker's pins in
`Checks/Cases/Checks/Sys/Mm/Mmap.lean`, which carries
`madvise_lazy_grant_by_noreplace` and none of the other three yet, while
their relation-level
twins are already `Checks/Cases/Mm/Madvise.lean`'s `lazy_grant`,
`lazy_grant_by_noreplace`,
`scenario_grant_refused_while_charged` and
`scenario_grant_fits_after_dontneed`; and the four over the ledger alone
(`madvise_lazy_first_touch_charges`,
`madvise_dontneed_budget_back_to_pre_touch`,
`madvise_dontneed_next_touch_recharges`, `madvise_eager_grant_keeps_its_charge`)
name no checker and are twinned on the relation in the same file, whose
fixtures this file reuses.

What the pins are for.  The proofs in the checker file say the checker and
the spec agree with EACH OTHER; nothing there says either agrees with
Linux, and a gate moved the same wrong way on both sides leaves every
proof closing.  So each answer below is a concrete one — this input, this
effect, this verdict — with the kernel line it comes from, and the
rejections are the lies a kernel cannot tell: a success on a misaligned
address, an errno on a zero length, a zap that left the bytes, a return
other than 0 on the answered shape.  A decline is pinned as a decline
whatever the trace offered, because the modeled surface is the spec's
question and not the trace's.

No probe reaches anything here: the syscall-check harness runs the
extracted Rocq model, never a Lean definition.  The probe that states the
same facts of the Rocq checker is
`testing/syscall-check/tests/madvise_dontneed.c`: its `dontneed` conform
case is `madvise_dontneed_whole_grant`'s answer, its
`--mutate madvise:drop-zeros` and `madvise:ret=-ENOMEM` rejects are
`madvise_without_zeros_rejected` and `madvise_nonzero_return_rejected`,
its `misaligned` and `zero-len` cases with their `ret=0` and
`ret=-EINVAL` rejects are `madvise_unaligned_forged_success_rejected` and
`madvise_len_zero_errno_rejected`, and its `zero-len-normal` fail-closed
case is `madvise_len_zero_other_advice_is_unmodeled`.  The kernel line is
the evidence either way; the spec-level twins in
`Checks/Cases/Mm/Madvise.lean` carry no `probe:` line and neither does
this file.

How the concrete answers close.  Where Rocq has `check_eq` (`vm_compute`,
then `reflexivity`; `Checks/Cases/Prelude.v`), a pin that stops at one of
the first three gates on literal arguments is `rfl` here.  A pin that
reaches the wrap gate, `two_pow_64 ≤ addr + page_round_up_Z len`, or
whose input names `two_pow_64` or `2 ^ 32`, is not: the elaborator's
`rfl` exhausts `maxRecDepth` on it, for a reason that is Lean's and not
the checker's — under `rfl`'s projection setting `BitVec.toNat` of a
def-built word is a stuck projection, and the `Int` order against `2 ^ 64`
is then decided through `Int.subNatNat`, whose `Nat.sub` recurses on the
literal.  The mechanism is written out and pinned in
`Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean` (the setting is
`backward.isDefEq.lazyWhnfCore`; with it off such goals close by `rfl`).
Those pins close by the two macros below, `check_norm` and
`witness_norm`: the checker, or the witness, is unfolded, each closed gate
is decided, and what is left is evaluated by ground rewriting, whose proof
terms the kernel checks by its own reduction as it checks a `decide`.
`check_norm` also opens `check_ret_only`: past the wrap gate the ground
pass reduces its first alternative but leaves the fall-through to
`CheckReject` standing on an effect that misses the return-only shape, and
with the name in the set that residue is decided too; on every other pin
the name goes unused.  The verdict a pin states is unchanged by the
choice of tactic; only the route to it is. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Madvise

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude (ret_outcome)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Madvise
  (madvise_lazy_granted madvise_lazy_touched madvise_lazy_both_touched madvise_top_two_pages)

/-- Evaluate a closed call of the checker: open it and `check_ret_only`,
decide every closed gate, and evaluate what is left by ground rewriting.
The header says why this and not `rfl`. -/
macro "check_norm" : tactic =>
  `(tactic| simp +ground +decide only [check_madvise, check_ret_only, ↓reduceIte])

/-- Evaluate a closed call of the witness the same way. -/
macro "witness_norm" : tactic =>
  `(tactic| simp +ground +decide only [madvise_witness, ret_outcome, ↓reduceIte])

section ArgumentGates

/-! ## The argument gates, in the kernel's order

`do_madvise` (mm/madvise.c:1967-1988, Linux v6.18.46) opens with
`madvise_should_skip` (mm/madvise.c:1830-1842), which returns -EINVAL when
`is_valid_madvise` (mm/madvise.c:1798-1817) refuses — the advice, the
alignment of `start`, a `len` whose page rounding wrapped to zero, a
range whose end wrapped — and 0 when the page-rounded length is zero.
Every refusal is the same errno, so the order among the four is
unobservable and only their place before the zero-length exit is. -/

/-- A misaligned address is -EINVAL, and a 0 there is a lie.  Twin of the
Rocq `madvise_unaligned_einval`.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_einval :
    check_madvise 65537 4096 4 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] := rfl

/-- …for EVERY advice value: the alignment refusal is one of four that all
answer -EINVAL, so the advice is never consulted — 0 is `MADV_NORMAL`, 99
no advice value at all, and both answer the same.  Twin of the Rocq
`madvise_unaligned_einval_for_any_advice`.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_einval_for_any_advice :
    check_madvise 65537 4096 0 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_madvise 65537 4096 99 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] :=
  ⟨rfl, rfl⟩

/-- A forged 0 on a misaligned address is rejected: the errno is the
kernel's only answer there.  Twin of the Rocq
`madvise_unaligned_forged_success_rejected`.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_forged_success_rejected :
    check_madvise 65537 4096 4 (mkEffect 0 [] []) one_map_model = CheckReject := rfl

/-- …and so is the walk's errno: -ENOMEM beside a misaligned address is
rejected, because `is_valid_madvise` refuses the arguments before
`do_madvise` walks a VMA (`madvise_walk_vmas`), so the alignment refusal
is the only answer.  Which errno stands at a gate is behaviour too.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise,madvise_walk_vmas@v6.18.46 -/
theorem madvise_unaligned_enomem_rejected :
    check_madvise 65537 4096 4 (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckReject := rfl

/-- The alignment refusal reads `start` alone: a misaligned address with a
zero length is still -EINVAL, not the zero-length 0, because
`is_valid_madvise` runs before `madvise_should_skip`'s second exit.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_len_zero_einval :
    check_madvise 65537 0 4 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_madvise 65537 0 4 (mkEffect 0 [] []) one_map_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- A return-only answer hands the model back UNCHANGED, on fixtures where
a change would show: the alignment -EINVAL over a grant with both pages
touched, and the wrap -EINVAL over a range starting at a touched page,
keep every materialized page, and the zap beside the misaligned address
is rejected.  Linux refuses the arguments before it looks at a VMA
(`is_valid_madvise`), so no page is zapped and no charge moves; the
`one_map_model` pins above cannot see this, having nothing materialized
to lose.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_return_only_keeps_the_ledger :
    check_madvise 65537 8192 4 (mkEffect (errno_ret EINVAL) [] []) madvise_lazy_both_touched
      = CheckOk madvise_lazy_both_touched []
    ∧ check_madvise 65537 8192 4 (mkEffect 0 [] [(65537, 8192)]) madvise_lazy_both_touched
      = CheckReject
    ∧ check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 65536)) 4
        (mkEffect (errno_ret EINVAL) [] []) madvise_lazy_touched
      = CheckOk madvise_lazy_touched [] :=
  by refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Every advice value other than `MADV_DONTNEED` declines, including the
one Linux answers 0 with no effect (`MADV_NORMAL`, 0) and the one whose
effect the model could not state (`MADV_FREE`, 8).  Both are valid under
every configuration — `madvise_behavior_valid` lists them unconditionally,
and only `MADV_MERGEABLE`/`MADV_UNMERGEABLE` (12/13, `CONFIG_KSM`),
`MADV_HUGEPAGE`/`MADV_NOHUGEPAGE`/`MADV_COLLAPSE` (14/15/25,
`CONFIG_TRANSPARENT_HUGEPAGE`) and `MADV_SOFT_OFFLINE`/`MADV_HWPOISON`
(100/101, `CONFIG_MEMORY_FAILURE`) sit under an `#ifdef` — so the decline
is not for want of an answer: `MADV_NORMAL` over a live mapping clears
read hints the model does not carry and returns 0 (`madvise_vma_behavior`
masks `VM_READHINTMASK` off and `madvise_update_vma` returns 0 for
unchanged flags), and the model states no advice but `MADV_DONTNEED`.
Twin of the Rocq `madvise_normal_is_unmodeled`; `madvise_free_is_unmodeled`
below is the second of Rocq's pair.
kernel: mm/madvise.c:madvise_behavior_valid,madvise_vma_behavior,madvise_update_vma@v6.18.46 -/
theorem madvise_normal_is_unmodeled :
    check_madvise 65536 4096 0 (mkEffect 0 [] []) one_map_model = CheckUnmodeled := rfl

/-- `MADV_FREE` (8) declines by the same gate: the value is one Linux
answers, and the model does not state its effect.
kernel: mm/madvise.c:madvise_behavior_valid@v6.18.46 -/
theorem madvise_free_is_unmodeled :
    check_madvise 65536 4096 8 (mkEffect 0 [] []) one_map_model = CheckUnmodeled := rfl

/-- `MADV_DONTNEED_LOCKED` (24) declines too, with the very zap
`MADV_DONTNEED` would be answered with beside it: valid under every
configuration and routed with `MADV_DONTNEED` to `madvise_dontneed_free`
by `madvise_vma_behavior`, it differs only in zapping `VM_LOCKED` pages
(`madvise_dontneed_free_valid_vma` forbids them for `MADV_DONTNEED`
alone), and the model states neither `mlock` nor the value.  The advice
gate is an equality on 4, not a family.
kernel: mm/madvise.c:madvise_behavior_valid,madvise_vma_behavior,madvise_dontneed_free_valid_vma@v6.18.46 -/
theorem madvise_dontneed_locked_is_unmodeled :
    check_madvise 65536 4096 24 (mkEffect 0 [] [(65536, 4096)]) one_map_model
      = CheckUnmodeled := rfl

/-- The decline is a decline whatever the trace offers: an errno beside
`MADV_NORMAL` is neither accepted nor rejected, although Linux never
answers one there — the value is valid under every configuration, and the
-EINVAL of `madvise_should_skip` is for the values `madvise_behavior_valid`
refuses.  A checker that answered `MADV_NORMAL` would reject this trace;
a decline is no verdict on it.
kernel: mm/madvise.c:madvise_should_skip,madvise_behavior_valid@v6.18.46 -/
theorem madvise_normal_errno_is_unmodeled :
    check_madvise 65536 4096 0 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckUnmodeled := rfl

/-- The advice is read through `Syscall.int32`, as the dispatcher applies
it: garbage in the register's high half is discarded before the switch
sees it, as the kernel's `int behavior` parameter discards it
(`SYSCALL_DEFINE3(madvise, unsigned long, start, size_t, len_in, int,
behavior)`).  Twin of the Rocq `madvise_advice_is_read_as_int`, with the
narrowing written out because it is the dispatcher's and not the
checker's.
kernel: mm/madvise.c:madvise@v6.18.46 -/
theorem madvise_advice_is_read_as_int :
    check_madvise 65536 4096 (int32 (Z_to_bv 64 (2 ^ 32 + 4)))
        (mkEffect 0 [] [(65536, 4096)]) one_map_model
      = CheckOk one_map_model [] := by check_norm

/-- …and the narrowing is load-bearing: handed the raw register, the
checker sees an advice that is not `MADV_DONTNEED` and declines.  A
dispatcher that forgot `int32` would turn the accepted trace above into a
decline; this is the half the positive pin cannot see.
model: the checker reads its `advice` argument as given; the 32-bit
narrowing is the dispatcher's, and this pins that the checker does not
repeat it -/
theorem madvise_advice_raw_register_is_unmodeled :
    check_madvise 65536 4096 (Z_to_bv 64 (2 ^ 32 + 4))
        (mkEffect 0 [] [(65536, 4096)]) one_map_model
      = CheckUnmodeled := rfl

/-- A negative advice, and one whose narrowed value is `MADV_NORMAL`.  The
register holding -1 narrows to 2^32 - 1, which the kernel's `int behavior`
reads as -1; `madvise_behavior_valid` is false for it under every
configuration (its `#ifdef`s gate 12/13, 14/15/25 and 100/101, and no
configuration admits -1), so the kernel answers -EINVAL, and the model
declines rather than answering because it states no advice but
`MADV_DONTNEED`.  A register holding 2^32 narrows to 0, `MADV_NORMAL`, and
declines by the same gate.
kernel: mm/madvise.c:madvise_behavior_valid,madvise_should_skip@v6.18.46 -/
theorem madvise_other_advice_values_are_unmodeled :
    check_madvise 65536 4096 (int32 (Z_to_bv 64 (two_pow_64 - 1)))
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckUnmodeled
    ∧ check_madvise 65536 4096 (int32 (Z_to_bv 64 (2 ^ 32))) (mkEffect 0 [] []) one_map_model
      = CheckUnmodeled :=
  by refine ⟨?_, ?_⟩ <;> check_norm

/-- The advice gate is read BEFORE the wrap gate: an unknown advice over a
range whose rounded end wraps declines rather than answering the wrap's
-EINVAL.  Linux answers -EINVAL there for 99 by `madvise_behavior_valid`,
the first test of `is_valid_madvise`, and never reaches the wrap test
after it; the model declines the value, whatever the trace offers.  A
checker that tested the wrap first would answer this input and keep every
other pin in this file green.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip,madvise_behavior_valid@v6.18.46 -/
theorem madvise_unknown_advice_before_the_wrap_gate :
    check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 1)) 99
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckUnmodeled := by check_norm

/-- `len = 0` is 0 at an aligned address (`madvise_should_skip`'s second
exit), with no effect.  Twin of the Rocq `madvise_len_zero_is_zero`.
kernel: mm/madvise.c:madvise_should_skip@v6.18.46 -/
theorem madvise_len_zero_is_zero :
    check_madvise 65536 0 4 (mkEffect 0 [] []) one_map_model = CheckOk one_map_model [] := rfl

/-- An errno there is rejected: the zero-length exit returns 0 before any
VMA is looked at, so there is nothing to fail.  Twin of the Rocq
`madvise_len_zero_errno_rejected`.
kernel: mm/madvise.c:madvise_should_skip@v6.18.46 -/
theorem madvise_len_zero_errno_rejected :
    check_madvise 65536 0 4 (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckReject := rfl

/-- A zero-fill beside the zero-length 0 is rejected too: `do_madvise`
returns from `madvise_should_skip` without walking a VMA, so no page was
zapped.
kernel: mm/madvise.c:madvise_should_skip,do_madvise@v6.18.46 -/
theorem madvise_len_zero_zeros_rejected :
    check_madvise 65536 0 4 (mkEffect 0 [] [(65536, 4096)]) one_map_model = CheckReject := rfl

/-- THE ORDER OF THE TWO GATES: the zero-length exit sits BEHIND the
advice gate, so `len = 0` with any other advice value declines rather
than answering 0.  Linux answers -EINVAL there for 99, a value
`madvise_behavior_valid` refuses under every configuration
(`is_valid_madvise` runs it before `madvise_should_skip`'s zero-length
exit), and 0 for `MADV_NORMAL`; a checker that tested the length first
would answer 0 for both and keep every other pin in this file green.
Twin of the Rocq `madvise_len_zero_other_advice_is_unmodeled`.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip,madvise_behavior_valid@v6.18.46 -/
theorem madvise_len_zero_other_advice_is_unmodeled :
    check_madvise 65536 0 99 (mkEffect 0 [] []) one_map_model = CheckUnmodeled
    ∧ check_madvise 65536 0 0 (mkEffect 0 [] []) one_map_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- A range whose page-rounded end reaches 2^64 is -EINVAL
(`is_valid_madvise`'s `start + len < start`), as is a `len` whose rounding
wraps to zero (`len_in && !len`).  Twin of the Rocq
`madvise_wrapping_range_einval`.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_wrapping_range_einval :
    check_madvise (Z_to_bv 64 (two_pow_64 - 4096)) 8192 4
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 1)) 4
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model [] :=
  by refine ⟨?_, ?_⟩ <;> check_norm

/-- The wrapping refusal is not a hole to decline on and not a place to
answer -ENOMEM: the range never reaches the VMA walk
(`madvise_walk_vmas`) that would report one, so the only admissible
answer is the -EINVAL above.
kernel: mm/madvise.c:madvise_walk_vmas,madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_wrapping_range_enomem_rejected :
    check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 1)) 4
        (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckReject := by check_norm

/-- The boundary itself.  With `len = 2^64 - addr` the C sum `start + len`
is exactly 0, which is `< start` (`is_valid_madvise`), so -EINVAL — and a
checker that tested `<` where the spec has `≤` would answer this input
from the ledger instead.  Both wrap pins above overshoot 2^64 by a page or
more, so this is the input that tells the two apart.  A 0 there is
rejected: qemu-user answers one, and
`bugs/madvise-wrap-boundary-qemu-user-answers-zero.md` says why that 0 is
QEMU's own declared bug and not an admitted behaviour.  One page shorter
the sum does not wrap and the walk runs: over a whole address space it
meets holes (-ENOMEM, `madvise_walk_vmas`) and, on riscv64, the vvar
page's `VM_PFNMAP` VMA (-EINVAL, `madvise_dontneed_free_valid_vma`,
returned at once by the walk); whichever it answers, the ledger cannot say
which pages the walk zapped on the way, so the model declines rather than
answering.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip,madvise_walk_vmas,madvise_dontneed_free_valid_vma@v6.18.46 -/
theorem madvise_wrap_boundary :
    check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 65536)) 4
        (mkEffect (errno_ret EINVAL) [] []) one_map_model
      = CheckOk one_map_model []
    ∧ check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 65536)) 4
        (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckReject
    ∧ check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 65536)) 4
        (mkEffect 0 [] []) one_map_model
      = CheckReject
    ∧ check_madvise 65536 (Z_to_bv 64 (two_pow_64 - 65536 - 4096)) 4
        (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckUnmodeled :=
  by refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Address 0 is page-aligned and has no special case in `is_valid_madvise`:
the kernel walks from 0, meets no VMA, and answers -ENOMEM
(`madvise_walk_vmas`).  The ledger holds nothing there, so the model
declines — neither side invents an -EINVAL for NULL.
kernel: mm/madvise.c:is_valid_madvise,madvise_walk_vmas@v6.18.46 -/
theorem madvise_null_address_is_unmodeled :
    check_madvise 0 4096 4 (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckUnmodeled := by check_norm

/-- The wrap gate reads the PAGE-ROUNDED length, on the one fixture where
the two readings part: the last two pages of the address space, owned as
one mapping.  Over both pages the rounded end is exactly 2^64 and the
answer is -EINVAL (`is_valid_madvise`: `len = PAGE_ALIGN(len_in)` before
`start + len < start`), the zap rejected; over the first page alone the
range fits and the zap is the answer, the -EINVAL rejected; over 4097
bytes the rounding carries the end to 2^64 again, so -EINVAL and not the
two-page zap.  A checker that summed the unrounded `len` would pass 4097
to the ledger gate and accept that zap; no pin on `one_map_model` can
tell, no range there ending within a page of 2^64 being owned.  The
spec-level twin is `wrap_edge_at_two_pow_64_is_einval` in
`Checks/Cases/Mm/Madvise.lean`, whose header says why the fixture is not
a reachable state.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_wrap_edge_on_a_live_top_page :
    check_madvise (Z_to_bv 64 (two_pow_64 - 8192)) 8192 4
        (mkEffect (errno_ret EINVAL) [] []) madvise_top_two_pages
      = CheckOk madvise_top_two_pages []
    ∧ check_madvise (Z_to_bv 64 (two_pow_64 - 8192)) 8192 4
        (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 8192), 8192)]) madvise_top_two_pages
      = CheckReject
    ∧ check_madvise (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4
        (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)]) madvise_top_two_pages
      = CheckOk madvise_top_two_pages []
    ∧ check_madvise (Z_to_bv 64 (two_pow_64 - 8192)) 4096 4
        (mkEffect (errno_ret EINVAL) [] []) madvise_top_two_pages
      = CheckReject
    ∧ check_madvise (Z_to_bv 64 (two_pow_64 - 8192)) 4097 4
        (mkEffect (errno_ret EINVAL) [] []) madvise_top_two_pages
      = CheckOk madvise_top_two_pages []
    ∧ check_madvise (Z_to_bv 64 (two_pow_64 - 8192)) 4097 4
        (mkEffect 0 [] [(Z_to_bv 64 (two_pow_64 - 8192), 8192)]) madvise_top_two_pages
      = CheckReject :=
  by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

end ArgumentGates

section AnsweredShape

/-! ## The answered shape, and the three ways to leave it

Past the gates, over a range inside one live anonymous mapping of the
ledger with every page read-write, the kernel's answer is forced:
`madvise_dontneed_single_vma` (mm/madvise.c:859-872, Linux v6.18.46) zaps
the range and returns 0.  The pins below are that answer and the lies
beside it. -/

/-- Over a whole live rw grant: 0 and the zero-fill of the range.  With
nothing lazy in the ledger the post-model is the pre-model.  Twin of the
Rocq `madvise_dontneed_whole_grant`.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_whole_grant :
    check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 4096)]) one_map_model
      = CheckOk one_map_model [] := by check_norm

/-- The zero-fill is load-bearing: a 0 that keeps the bytes is a kernel
that did not zap the range, and is rejected.  Twin of the Rocq
`madvise_without_zeros_rejected`.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_without_zeros_rejected :
    check_madvise 65536 4096 4 (mkEffect 0 [] []) one_map_model = CheckReject := by check_norm

/-- No errno is injectable on the answered shape, and no other return is
admissible: -ENOMEM and 1 are both rejected.  The -ENOMEM the walk can
report is for a hole (`madvise_walk_vmas`), and the containment gate has
already excluded one.  Twin of the Rocq `madvise_nonzero_return_rejected`.
kernel: mm/madvise.c:madvise_walk_vmas,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_nonzero_return_rejected :
    check_madvise 65536 4096 4 (mkEffect (errno_ret ENOMEM) [] []) one_map_model = CheckReject
    ∧ check_madvise 65536 4096 4 (mkEffect 1 [] [(65536, 4096)]) one_map_model = CheckReject :=
  by refine ⟨?_, ?_⟩ <;> check_norm

/-- No errno stands beside the zap either, and no other return does.
-ENOMEM is the walk's answer for a hole (`madvise_walk_vmas`), and the
containment gate has excluded one; -EINTR is `madvise_lock`'s under
`MADVISE_MMAP_WRITE_LOCK`, and `get_lock_mode` gives `MADV_DONTNEED` the
per-VMA read lock, so the arm cannot answer it; and 2^32, a return whose
low half is 0, is not the 0 of `madvise_dontneed_single_vma` — the return
is compared whole.
kernel: mm/madvise.c:madvise_walk_vmas,madvise_lock,get_lock_mode,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_errno_beside_the_zap_rejected :
    check_madvise 65536 4096 4 (mkEffect (errno_ret ENOMEM) [] [(65536, 4096)]) one_map_model
      = CheckReject
    ∧ check_madvise 65536 4096 4 (mkEffect (errno_ret EINTR) [] []) one_map_model
      = CheckReject
    ∧ check_madvise 65536 4096 4 (mkEffect (Z_to_bv 64 (2 ^ 32)) [] [(65536, 4096)]) one_map_model
      = CheckReject :=
  by refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The zero-fill must be the WHOLE page-rounded range and nothing else:
a fill short of it, one past it, and one over the page-rounded length of
an unrounded `len` written unrounded, are each a kernel that zapped
something other than what `madvise_dontneed_single_vma` zaps — the range
`madvise_do_behavior` rounds (`range->end = range->start +
PAGE_ALIGN(len_in)`) and `madvise_walk_vmas` hands it, clipped to the VMA.
kernel: mm/madvise.c:madvise_dontneed_single_vma,madvise_do_behavior,madvise_walk_vmas@v6.18.46 -/
theorem madvise_wrong_extent_zeros_rejected :
    check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 2048)]) one_map_model = CheckReject
    ∧ check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 8192)]) one_map_model = CheckReject
    ∧ check_madvise 65536 1 4 (mkEffect 0 [] [(65536, 1)]) one_map_model = CheckReject
    ∧ check_madvise 65536 1 4 (mkEffect 0 [] [(65536, 4096)]) one_map_model
      = CheckOk one_map_model [] :=
  by refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The one zero-fill is over THIS range, once: a fill of the neighbouring
page, the range in two halves, and the range listed twice are each
rejected.  `madvise_dontneed_single_vma` zaps `[start, end)` of the range
`madvise_walk_vmas` hands it, in one call for a range inside one VMA; the
two split shapes describe the same bytes and are refused because the
answered shape is the spec's one pair `(addr, n)`, as Rocq refuses them.
kernel: mm/madvise.c:madvise_dontneed_single_vma,madvise_walk_vmas@v6.18.46 -/
theorem madvise_zero_fill_elsewhere_rejected :
    check_madvise 65536 4096 4 (mkEffect 0 [] [(69632, 4096)]) one_map_model = CheckReject
    ∧ check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 2048), (67584, 2048)]) one_map_model
      = CheckReject
    ∧ check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 4096), (65536, 4096)]) one_map_model
      = CheckReject :=
  by refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Nothing but the return and the zero-fill: a write, an unmap, a copy or
a copy-in beside the right answer is rejected, one ledger at a time, so
the accepted shape cannot be widened a field at a time.  `madvise` has no
`copy_to_user`, no `copy_from_user`, and unmaps nothing.
kernel: mm/madvise.c:madvise_dontneed_single_vma,do_madvise@v6.18.46 -/
theorem madvise_other_ledgers_rejected :
    check_madvise 65536 4096 4
        (SyscallEffect.mkEffectU 0 [(65536, [0])] [(65536, 4096)] [] [] []) one_map_model
      = CheckReject
    ∧ check_madvise 65536 4096 4
        (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [] []) one_map_model
      = CheckReject
    ∧ check_madvise 65536 4096 4
        (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [] [MemCopy.mkCopy 65536 65536 4096] []) one_map_model
      = CheckReject
    ∧ check_madvise 65536 4096 4
        (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [] [] [(65536, 4096)]) one_map_model
      = CheckReject :=
  by refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The same at the return-only gates: a copy-in beside the alignment
-EINVAL, an unmap beside the zero-length 0, a write beside the wrap
-EINVAL, each rejected.  `do_madvise` reads no user memory on any of those
paths and unmaps nothing.
kernel: mm/madvise.c:do_madvise,madvise_should_skip@v6.18.46 -/
theorem madvise_gate_ledgers_rejected :
    check_madvise 65537 4096 4
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(65537, 1)]) one_map_model
      = CheckReject
    ∧ check_madvise 65536 0 4
        (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) one_map_model
      = CheckReject
    ∧ check_madvise (Z_to_bv 64 (two_pow_64 - 4096)) 8192 4
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [(65536, [0])] [] [] [] []) one_map_model
      = CheckReject :=
  by refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A range with a page outside the grant declines.  Linux applies the
advice to the mapped page and reports -ENOMEM for the hole
(`madvise_walk_vmas`); the ledger cannot say which pages that is, so the
model does not answer.  This is `map_contains`'s conjunct of
`madvise_dontneed_ok`.  Twin of the Rocq `madvise_partial_grant_is_unmodeled`.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem madvise_partial_grant_is_unmodeled :
    check_madvise 65536 8192 4 (mkEffect 0 [] [(65536, 8192)]) one_map_model
      = CheckUnmodeled := by check_norm

/-- …and the decline holds whatever the trace offers, the kernel's own
-ENOMEM included: a decline is not a verdict on the trace.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem madvise_partial_grant_enomem_is_unmodeled :
    check_madvise 65536 8192 4 (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckUnmodeled := by check_norm

/-- A range the ledger holds nothing of declines, whether below the run's
`alloc_top` (a hole, -ENOMEM on Linux) or at the bottom of the stack band
above it (`demo_top`).  Linux answers -ENOMEM there too unless the stack
has grown down to that page — `madvise` walks the VMAs there are and
never grows one, `expand_stack` in mm/mmap.c being the fault path's — and
zaps it with 0 if it has; the ledger carries neither the hole nor the
stack, so both fall on the same `map_contains` test and there is no
separate stack-band gate to pin.  Twin of the Rocq
`madvise_free_range_is_unmodeled`.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem madvise_free_range_is_unmodeled :
    check_madvise 131072 4096 4 (mkEffect 0 [] []) one_map_model = CheckUnmodeled
    ∧ check_madvise (Z_to_bv 64 demo_top) 4096 4
        (mkEffect 0 [] [(Z_to_bv 64 demo_top, 4096)]) one_map_model
      = CheckUnmodeled :=
  by refine ⟨?_, ?_⟩ <;> check_norm

/-- The image's LOAD pages decline even on a ledger that also lists them
in `vm_maps` — the `vm_reserved` conjunct.  No reachable state has such a
ledger (grants are placed clear of the image), so this pins the conjunct
on the one fixture that can reach it.  Twin of the Rocq
`madvise_image_range_is_unmodeled`.
model: the `vm_reserved` conjunct of `madvise_dontneed_ok`; nothing is
claimed of what Linux does to an image page, the model declines it -/
theorem madvise_image_range_is_unmodeled :
    check_madvise 4096 4096 4 (mkEffect 0 [] [(4096, 4096)]) noaccess_image_overlap
      = CheckUnmodeled := by check_norm

/-- A PROT_NONE range declines.  Linux zaps it and answers 0 —
`madvise_dontneed_free_valid_vma` forbids `VM_PFNMAP` and, for
`MADV_DONTNEED`, `VM_LOCKED`, and a protection is neither, so
`madvise_dontneed_single_vma` runs — but the machine overlay holds no
bytes for a protected page to zap, and re-exposing one is `mprotect`'s
zero-fill, not this arm's: the `vm_noaccess` conjunct of
`madvise_dontneed_ok`.  Twin of the Rocq
`madvise_noaccess_range_is_unmodeled`.
kernel: mm/madvise.c:madvise_dontneed_free_valid_vma,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_noaccess_range_is_unmodeled :
    check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 4096)]) noaccess_three_pages
      = CheckUnmodeled := by check_norm

/-- The checker is not the lazy one: `CheckUnmodeled` is an answer it gives
on the declined shapes above and nowhere else, and on the answered shape it
commits.  It is proved from `madvise_dontneed_whole_grant`, the `= CheckOk`
pin that already refuses a checker declining everything; this restates that
refusal in the shape a reader looks for.
model: `check_madvise`'s answered arm; the claim is about the checker's
shape, and the kernel line for the answer is on `madvise_dontneed_whole_grant` -/
theorem madvise_checker_is_not_lazy :
    check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 4096)]) one_map_model
      ≠ CheckUnmodeled := by
  intro h
  rw [madvise_dontneed_whole_grant] at h
  cases h

end AnsweredShape

section Charges

/-! ## What the arm is for: giving first-touch charges back

The fixtures are `Checks/Cases/Mm/Madvise.lean`'s: a two-page budget, a
two-page `MAP_NORESERVE` grant at 65536 (`madvise_lazy_granted`), the
same with its first page touched and so charged (`madvise_lazy_touched`),
and with both pages touched (`madvise_lazy_both_touched`).  Linux keeps
the commit charge of a `VM_ACCOUNT` VMA across a zap
(`madvise_dontneed_single_vma`, mm/madvise.c:859-872, Linux v6.18.46,
touches no accounting), and the model's first-touch charge is what the
zap gives back. -/

/-- MADV_DONTNEED over the grant returns the charge: the post-model IS the
pre-touch model — same mapping, same lazy provenance, no materialized
page.  This is the pin a checker that handed the model back unchanged
would fail, which no `one_map_model` pin can be, there being nothing lazy
in that fixture.  Twin of the Rocq `madvise_dontneed_returns_the_charge`.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_returns_the_charge :
    check_madvise 65536 8192 4 (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_touched
      = CheckOk madvise_lazy_granted [] := by check_norm

/-- …and the unchanged model is refused as the post-state, by the
materialized ledger the two fixtures differ in.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_kept_charge_refused :
    check_madvise 65536 8192 4 (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_touched
      ≠ CheckOk madvise_lazy_touched [] := by
  intro h
  rw [madvise_dontneed_returns_the_charge] at h
  simp only [check_result.CheckOk.injEq, and_true] at h
  exact absurd (congrArg m_vm_materialized h) (by decide)

/-- Only the pages IN the range are given back.  Both pages touched,
DONTNEED over the second: the first keeps its charge, and the post-model is
the one-page-touched fixture.  Twin of the Rocq
`madvise_dontneed_only_the_range`'s first conjunct; its two budget
conjuncts name no checker and are `dontneed_only_the_range_budgets` in
`Checks/Cases/Mm/Madvise.lean`.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_only_the_range :
    check_madvise 69632 4096 4 (mkEffect 0 [] [(69632, 4096)]) madvise_lazy_both_touched
      = CheckOk madvise_lazy_touched [] := by check_norm

/-- After MADV_DONTNEED over both pages the model is the untouched grant
again — stated as that independently written model, not as the arm's own
post-state function, so the content is what is pinned.  Twin of the Rocq
`madvise_scenario_dontneed`.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_scenario_dontneed :
    check_madvise 65536 8192 4 (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_both_touched
      = CheckOk madvise_lazy_granted [] := by check_norm

/-- The charge given back is over the PAGE-ROUNDED range: 4097 bytes from
the grant's start give both pages back, as `madvise_do_behavior`'s
`range->end = range->start + PAGE_ALIGN(len_in)` has both zapped.  The
zero-fill beside it is the rounded one too
(`madvise_wrong_extent_zeros_rejected` pins the unrounded fill's refusal
on `one_map_model`).
kernel: mm/madvise.c:madvise_do_behavior,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_unrounded_len_rounds_the_charge :
    check_madvise 65536 4097 4 (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_both_touched
      = CheckOk madvise_lazy_granted [] := by check_norm

/-- The range's upper bound is EXCLUSIVE: DONTNEED over the first page of a
grant with both pages touched gives the first page's charge back and
keeps the second's, whose address is the range's end.  With
`madvise_dontneed_only_the_range` above, which keeps the page below the
range, this pins both ends of `madvise_dontneed_next`'s filter; a filter
that read `≤` at the top would give both pages back here and pass every
other pin.  `madvise_dontneed_single_vma` zaps `[start, end)`.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_first_page_keeps_the_second :
    check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 4096)]) madvise_lazy_both_touched
      = CheckOk (with_vm_backing (m_vm_lazy madvise_lazy_granted) [69632] madvise_lazy_granted) []
      := by check_norm

/-- …and the pre-touch model, both charges given back, is refused as the
post-state there, by the materialized page the two differ in.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_first_page_both_charges_refused :
    check_madvise 65536 4096 4 (mkEffect 0 [] [(65536, 4096)]) madvise_lazy_both_touched
      ≠ CheckOk madvise_lazy_granted [] := by
  intro h
  rw [madvise_dontneed_first_page_keeps_the_second] at h
  simp only [check_result.CheckOk.injEq, and_true] at h
  exact absurd (congrArg m_vm_materialized h) (by decide)

end Charges

section Witness

/-! ## The witness

`madvise_witness` is the one outcome the arm offers at every input; the
checker file proves the spec accepts it.  These pins read it at the
concrete inputs above, so a witness that took a different gate from the
checker is caught on an input a reader can compute. -/

/-- The witness's outcome at each gate: the -EINVAL of the alignment and
of the wrap, the advice and ledger declines, the zero-length 0, and on the
answered shape the 0 with the zero-fill and the charge given back.
kernel: mm/madvise.c:madvise_should_skip,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_witness_at_the_gates :
    madvise_witness 65537 4096 4 one_map_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model []
    ∧ madvise_witness 65536 4096 0 one_map_model = Unmodeled
    ∧ madvise_witness 65536 0 4 one_map_model = Ok (mkEffect 0 [] []) one_map_model []
    ∧ madvise_witness (Z_to_bv 64 (two_pow_64 - 4096)) 8192 4 one_map_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model []
    ∧ madvise_witness 65536 8192 4 one_map_model = Unmodeled
    ∧ madvise_witness 65536 8192 4 madvise_lazy_touched
      = Ok (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_granted [] :=
  by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- The witness's gates in the checker's ORDER and at the checker's
BOUNDARIES: alignment before advice (a misaligned `MADV_NORMAL` is
-EINVAL, not a decline), advice before the zero-length exit (`len = 0`
with `MADV_NORMAL` declines), alignment before the zero-length exit; the
wrap gate at `≤` (a rounded end of exactly 2^64 is -EINVAL, one page
shorter a decline of the ledger) and over the rounded length (4097 bytes
from the second-to-last page); and on the answered shape the zero-fill
over the rounded length with the charge given back, while a return-only
answer keeps the touched page.  Each is the witness's half of a checker
pin above; a witness that took the gates in another order, or read the
unrounded length, would still be accepted by the spec at every input
where the two agree, so the checker pins alone cannot see it.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_witness_gate_order_and_boundary :
    madvise_witness 65537 4096 0 one_map_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model []
    ∧ madvise_witness 65536 0 0 one_map_model = Unmodeled
    ∧ madvise_witness 65537 0 4 one_map_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model []
    ∧ madvise_witness 65536 (Z_to_bv 64 (two_pow_64 - 65536)) 4 one_map_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) one_map_model []
    ∧ madvise_witness 65536 (Z_to_bv 64 (two_pow_64 - 65536 - 4096)) 4 one_map_model = Unmodeled
    ∧ madvise_witness (Z_to_bv 64 (two_pow_64 - 8192)) 4097 4 madvise_top_two_pages
      = Ok (mkEffect (errno_ret EINVAL) [] []) madvise_top_two_pages []
    ∧ madvise_witness 65536 4097 4 madvise_lazy_both_touched
      = Ok (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_granted []
    ∧ madvise_witness 65537 4096 4 madvise_lazy_touched
      = Ok (mkEffect (errno_ret EINVAL) [] []) madvise_lazy_touched [] :=
  by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- Whatever the witness offers as an `Ok`, the checker accepts with the
same post-model and events: the two are one reading of the spec, through
`madvise_witness_ok` and `check_madvise_complete_ok`.
model: a consequence of the checker file's own lemmas; no kernel behaviour
is claimed beyond what those state -/
theorem madvise_witness_is_checked (addr len advice : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : madvise_witness addr len advice m = Ok eff m' evs) :
    check_madvise addr len advice eff m = CheckOk m' evs :=
  check_madvise_complete_ok addr len advice eff m m' evs i
    (h ▸ madvise_witness_ok addr len advice i m)

/-- …and a decline of the witness is a decline of the checker on every
effect, through `check_madvise_complete_unmodeled`.
model: a consequence of the checker file's own lemmas; no kernel behaviour
is claimed beyond what those state -/
theorem madvise_witness_decline_is_checked (addr len advice : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (h : madvise_witness addr len advice m = Unmodeled) :
    check_madvise addr len advice eff m = CheckUnmodeled :=
  check_madvise_complete_unmodeled addr len advice m i eff
    (h ▸ madvise_witness_ok addr len advice i m)

end Witness

section Frame

/-! ## The frame -/

/-- The arm moves the materialized ledger and nothing in `vm_maps`, read
off the checker's own answer on the lazy fixture: whatever post-model the
checker hands back there, its maps are the pre-model's.  The statement
over every input is the checker file's `check_madvise_frame`; this is the
one input a reader can compute, so that the frame is seen and not only
proved.  `madvise_dontneed_single_vma` zaps pages and leaves the VMA
where it is.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_frame_on_the_answered_shape (m' : Model) (evs : List event)
    (h : check_madvise 65536 8192 4 (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_touched
      = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps madvise_lazy_touched := by
  rw [madvise_dontneed_returns_the_charge] at h
  simp only [check_result.CheckOk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

end Frame

-- lean-port sentinel: ticket V-Mm-Madvise appends below this line

section V_Mm_Madvise

open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap (mmap_fd_none)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Madvise (madvise_in madvise_lazy_base)

/-! ## V-Mm-Madvise — `madvise` over the real table

WHAT IS TWINNED HERE.  The sections above state each Rocq example on
`check_madvise` itself, because `checked_table` carried no row for 233
when they were written, and leave the restatement through
`check_syscall` to the registration; `Checks/Arms/Mm/Madvise.lean` is the
registration.  The examples of
`theories/LinuxProcessSem/Checks/Cases/Mm/Madvise.v` stated through
`check_syscall` are restated here through the Lean `check_syscall`, over
`checked_table` itself, bar the one named below.  Each keeps its Rocq
input and its Rocq name with `_over_the_real_table` after it (K6b's
convention), at Rocq's own fixture — or at every model, where the answer
is decided before the checker reads one, which says more.  Three of them
are `mmap` calls, the charge scenario's grants: they are here because
their Rocq examples are in the madvise file, and no other Lean file
states them through the dispatcher.  The one not here,
`madvise_lazy_grant_by_noreplace`, is stated through the dispatcher in
`Checks/Cases/Checks/Sys/Mm/Mmap.lean`, with the mmap checker's other
`MAP_FIXED_NOREPLACE` pins.

WHAT A PIN HERE ADDS to its checker-level twin above is the ARM's claim:
that the lookup at 233 finds `arm_madvise` rather than the dispatcher's
own decline, and that the arm hands the checker `a0`, `a1` and
`int32 a2`, in that order.  The narrowing is carried by
`madvise_advice_is_read_as_int_over_the_real_table`, whose advice register
holds `2^32 + 4`: an arm handing the checker the whole register would
decline it (`madvise_advice_raw_register_is_unmodeled`, above), so the
`CheckOk` fails.  The register order is carried by the answered-shape
acceptances: `madvise_in 65536 4096 4` read with `a0` and `a1` swapped is
a range at 4096 the ledger holds nothing of, which declines.

POLARITY is the sections' above, each pin carrying its checker-level
twin's evidence line: `kernel:` on every pin about the kernel's answer,
`CheckOk`, `CheckReject` and a decline alike, and `model:` on the
lookups, which are the table's own contents, and on the image-range
decline, which claims nothing of Linux. -/

set_option maxRecDepth 4096 in
/-- The lookup the dispatcher performs on a `madvise_in`, computed once:
`in_sysno` is `233` whatever the three registers hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_madvise_in (addr len advice : word) :
    lookup_ca checked_table (bv_unsigned (madvise_in addr len advice).in_sysno)
      = some arm_madvise :=
  lookup_ca_checked_table_madvise

set_option maxRecDepth 4096 in
/-- The lookup on the scenario's `mmap` input, `a7 = 222`.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_scenario_mmap_in (addr len prot flags : word) :
    lookup_ca checked_table
        (bv_unsigned (SyscallInput.mkInput 222 [addr, len, prot, flags, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none)).in_sysno)
      = some arm_mmap :=
  lookup_ca_checked_table_mmap

/-- Read a concrete `check_syscall` at a `madvise_in` off: the lookup, the
arm's `arm_unfold`, the three registers, then `check_norm`. -/
scoped macro "madvise_dispatch_norm" : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [lookup_madvise_in];
             simp only [arm_unfold, madvise_in, in_arg]; check_norm))

/-- Read a concrete `syscall_spec_witness` at a `madvise_in` off. -/
scoped macro "madvise_dispatch_witness_norm" : tactic =>
  `(tactic| (unfold syscall_spec_witness table_witness; rw [lookup_madvise_in];
             simp only [arm_unfold, madvise_in, in_arg]; witness_norm))

/-- Read a concrete `check_syscall` at the scenario's `mmap` input off:
the lookup, the arm's `arm_unfold`, then `check_mmap` by `sys_norm`, as
`Checks/Cases/Checks/Sys/Mm/Mmap.lean`'s `dispatch_norm` does (its macros
are scoped to that file's namespace). -/
scoped macro "scenario_mmap_dispatch_norm" : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [lookup_scenario_mmap_in];
             simp only [arm_unfold];
             unfold LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_mmap check_ret_only;
             sys_norm))

/-! ### The argument gates, through `check_syscall`

These hold at every model: `madvise_should_skip` (mm/madvise.c, Linux
v6.18.46) refuses the arguments before `do_madvise` looks at a VMA. -/

/-- `madvise_unaligned_einval` over the real table: a misaligned `start`
is -EINVAL, the model untouched.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_einval_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65537 4096 4) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  madvise_dispatch_norm

/-- `madvise_unaligned_einval_for_any_advice` over the real table:
`MADV_NORMAL` (0) and 99, no advice value at all, answer the same -EINVAL.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_einval_for_any_advice_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65537 4096 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (madvise_in 65537 4096 99) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> madvise_dispatch_norm

/-- `madvise_unaligned_forged_success_rejected` over the real table: a 0
on a misaligned address is a lie.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_forged_success_rejected_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65537 4096 4) (mkEffect 0 [] []) m = CheckReject := by
  madvise_dispatch_norm

/-- `madvise_normal_is_unmodeled` over the real table: `MADV_NORMAL` is
valid under every configuration and the model states no advice but
`MADV_DONTNEED`, so the arm declines where Linux answers 0.
kernel: mm/madvise.c:madvise_behavior_valid,madvise_vma_behavior,madvise_update_vma@v6.18.46 -/
theorem madvise_normal_is_unmodeled_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65536 4096 0) (mkEffect 0 [] []) m = CheckUnmodeled := by
  madvise_dispatch_norm

/-- `madvise_free_is_unmodeled` over the real table: `MADV_FREE` (8)
declines by the same gate.
kernel: mm/madvise.c:madvise_behavior_valid@v6.18.46 -/
theorem madvise_free_is_unmodeled_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65536 4096 8) (mkEffect 0 [] []) m = CheckUnmodeled := by
  madvise_dispatch_norm

/-- `madvise_advice_is_read_as_int` over the real table: `a2` holds
`2^32 + 4`, and `int behavior` is 4.  riscv64's `__SYSCALL_DEFINEx` hands
the parameter to `__do_sys_madvise` through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), so bit 32 is
not a bit of the argument, and the call is `MADV_DONTNEED` over the live
page: 0 and the zero-fill.  An arm handing the checker the raw register
declines here (`madvise_advice_raw_register_is_unmodeled`, above).
kernel: include/linux/syscalls.h:__SC_CAST; mm/madvise.c:madvise,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_advice_is_read_as_int_over_the_real_table :
    check_syscall (madvise_in 65536 4096 (Z_to_bv 64 (2 ^ 32 + 4)))
        (mkEffect 0 [] [(65536, 4096)]) one_map_model
      = CheckOk one_map_model [] := by
  madvise_dispatch_norm

/-- `madvise_len_zero_is_zero` over the real table: `len = 0` at an
aligned address is 0 with no effect (`madvise_should_skip`'s second exit).
kernel: mm/madvise.c:madvise_should_skip@v6.18.46 -/
theorem madvise_len_zero_is_zero_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65536 0 4) (mkEffect 0 [] []) m = CheckOk m [] := by
  madvise_dispatch_norm

/-- `madvise_len_zero_errno_rejected` over the real table: the zero-length
exit returns 0 before any VMA is looked at, so an -EINVAL there is a lie.
kernel: mm/madvise.c:madvise_should_skip@v6.18.46 -/
theorem madvise_len_zero_errno_rejected_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65536 0 4) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckReject := by
  madvise_dispatch_norm

/-- `madvise_len_zero_other_advice_is_unmodeled` over the real table: the
zero-length exit sits behind the advice gate, so `len = 0` with 99 or
`MADV_NORMAL` declines.  Linux answers -EINVAL for 99, which
`madvise_behavior_valid` refuses under every configuration, and 0 for
`MADV_NORMAL`; a checker testing the length first would answer 0 for both.
kernel: mm/madvise.c:is_valid_madvise,madvise_should_skip,madvise_behavior_valid@v6.18.46 -/
theorem madvise_len_zero_other_advice_is_unmodeled_over_the_real_table (m : Model) :
    check_syscall (madvise_in 65536 0 99) (mkEffect 0 [] []) m = CheckUnmodeled
    ∧ check_syscall (madvise_in 65536 0 0) (mkEffect 0 [] []) m = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> madvise_dispatch_norm

/-- `madvise_wrapping_range_einval` over the real table: a range whose
page-rounded end passes 2^64, and a `len` whose rounding wraps, are
-EINVAL (`is_valid_madvise`), the model untouched.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_wrapping_range_einval_over_the_real_table (m : Model) :
    check_syscall (madvise_in (Z_to_bv 64 (two_pow_64 - 4096)) 8192 4)
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m []
    ∧ check_syscall (madvise_in 65536 (Z_to_bv 64 (two_pow_64 - 1)) 4)
        (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> madvise_dispatch_norm

/-! ### The answered shape, through `check_syscall` -/

/-- `madvise_dontneed_whole_grant` over the real table: over the whole
live rw grant, 0 and the zero-fill of the range.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_whole_grant_over_the_real_table :
    check_syscall (madvise_in 65536 4096 4) (mkEffect 0 [] [(65536, 4096)]) one_map_model
      = CheckOk one_map_model [] := by
  madvise_dispatch_norm

/-- `madvise_without_zeros_rejected` over the real table: a 0 that keeps
the bytes is a kernel that did not zap the range.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_without_zeros_rejected_over_the_real_table :
    check_syscall (madvise_in 65536 4096 4) (mkEffect 0 [] []) one_map_model = CheckReject := by
  madvise_dispatch_norm

/-- `madvise_nonzero_return_rejected` over the real table: -ENOMEM is the
walk's answer for a hole (`madvise_walk_vmas`), and the range is one live
grant; a return of 1 beside the zero-fill is not the 0 of
`madvise_dontneed_single_vma`.
kernel: mm/madvise.c:madvise_walk_vmas,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_nonzero_return_rejected_over_the_real_table :
    check_syscall (madvise_in 65536 4096 4) (mkEffect (errno_ret ENOMEM) [] []) one_map_model
      = CheckReject
    ∧ check_syscall (madvise_in 65536 4096 4) (mkEffect 1 [] [(65536, 4096)]) one_map_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> madvise_dispatch_norm

/-- `madvise_partial_grant_is_unmodeled` over the real table: a range with
a page outside the grant declines; Linux zaps the mapped page and reports
-ENOMEM for the hole (`madvise_walk_vmas`), and the ledger cannot say which
pages that is.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem madvise_partial_grant_is_unmodeled_over_the_real_table :
    check_syscall (madvise_in 65536 8192 4) (mkEffect 0 [] [(65536, 8192)]) one_map_model
      = CheckUnmodeled := by
  madvise_dispatch_norm

/-- `madvise_free_range_is_unmodeled` over the real table: a range the
ledger holds nothing of declines, below `alloc_top` and at the bottom of
the stack band alike.
kernel: mm/madvise.c:madvise_walk_vmas@v6.18.46 -/
theorem madvise_free_range_is_unmodeled_over_the_real_table :
    check_syscall (madvise_in 131072 4096 4) (mkEffect 0 [] []) one_map_model = CheckUnmodeled
    ∧ check_syscall (madvise_in (Z_to_bv 64 demo_top) 4096 4)
        (mkEffect 0 [] [(Z_to_bv 64 demo_top, 4096)]) one_map_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> madvise_dispatch_norm

/-- `madvise_image_range_is_unmodeled` over the real table: the image's
LOAD page declines even on a ledger that also lists it as live.
model: the `vm_reserved` conjunct of `madvise_dontneed_ok`; nothing is
claimed of what Linux does to an image page, the model declines it -/
theorem madvise_image_range_is_unmodeled_over_the_real_table :
    check_syscall (madvise_in 4096 4096 4) (mkEffect 0 [] [(4096, 4096)]) noaccess_image_overlap
      = CheckUnmodeled := by
  madvise_dispatch_norm

/-- `madvise_noaccess_range_is_unmodeled` over the real table: a
`PROT_NONE` range declines, the `vm_noaccess` conjunct; Linux zaps it and
answers 0 (`madvise_dontneed_free_valid_vma` forbids neither).
kernel: mm/madvise.c:madvise_dontneed_free_valid_vma,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_noaccess_range_is_unmodeled_over_the_real_table :
    check_syscall (madvise_in 65536 4096 4) (mkEffect 0 [] [(65536, 4096)]) noaccess_three_pages
      = CheckUnmodeled := by
  madvise_dispatch_norm

/-! ### The charges, and the scenario from issue #683, through `check_syscall` -/

/-- `madvise_lazy_grant` over the real table: a two-page
`MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE` grant placed at 65536 lands as
`madvise_lazy_granted`, its interior lazy and nothing charged; `do_mmap`
turns the bit into `VM_NORESERVE` outside strict overcommit.
kernel: mm/mmap.c:do_mmap; mm/vma.c:accountable_mapping@v6.18.46 -/
theorem madvise_lazy_grant_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 222 [0, 8192, 3, 16418, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 65536 [] [(65536, 8192)]) madvise_lazy_base
      = CheckOk madvise_lazy_granted [] := by
  scenario_mmap_dispatch_norm

/-- `madvise_dontneed_returns_the_charge` over the real table: the
post-model IS the pre-touch model.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_returns_the_charge_over_the_real_table :
    check_syscall (madvise_in 65536 8192 4) (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_touched
      = CheckOk madvise_lazy_granted [] := by
  madvise_dispatch_norm

/-- `madvise_dontneed_only_the_range` over the real table (its first
conjunct; the two budget conjuncts name no checker): both pages touched,
`MADV_DONTNEED` over the second gives back only its charge.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_dontneed_only_the_range_over_the_real_table :
    check_syscall (madvise_in 69632 4096 4) (mkEffect 0 [] [(69632, 4096)])
        madvise_lazy_both_touched
      = CheckOk madvise_lazy_touched [] := by
  madvise_dispatch_norm

/-- `madvise_scenario_grant_refused_while_charged` over the real table:
with both lazy pages touched the two-page budget is spent, so a one-page
eager grant (flags 34, `MAP_PRIVATE|MAP_ANONYMOUS`) is a lie and its
-ENOMEM the answer, the model untouched.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem madvise_scenario_grant_refused_while_charged_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 131072 [] [(131072, 4096)]) madvise_lazy_both_touched
      = CheckReject
    ∧ check_syscall
        (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect (errno_ret ENOMEM) [] []) madvise_lazy_both_touched
      = CheckOk madvise_lazy_both_touched [] := by
  refine ⟨?_, ?_⟩ <;> scenario_mmap_dispatch_norm

/-- `madvise_scenario_dontneed` over the real table: after
`MADV_DONTNEED` over both pages the model is the untouched grant again.
kernel: mm/madvise.c:madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_scenario_dontneed_over_the_real_table :
    check_syscall (madvise_in 65536 8192 4) (mkEffect 0 [] [(65536, 8192)])
        madvise_lazy_both_touched
      = CheckOk madvise_lazy_granted [] := by
  madvise_dispatch_norm

/-- `madvise_scenario_grant_fits_after_dontneed` over the real table: the
same grant now fits, at 131072, the ledger extended and the lazy backing
untouched.
kernel: mm/vma.c:__mmap_prepare@v6.18.46 -/
theorem madvise_scenario_grant_fits_after_dontneed_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
          (fun _ => none) (fun _ => none))
        (mkEffect 131072 [] [(131072, 4096)]) madvise_lazy_granted
      = CheckOk
          (with_vmmaps (VmMaps.mkVmMapsFull [] [(131072, 4096), (65536, 8192)] [] 0 0 8192 0
            demo_sp) madvise_lazy_granted) [] := by
  scenario_mmap_dispatch_norm

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 233; the witness pins above fix
`madvise_witness` at bare words, these fix that the arm hands it the
reading the checker gets. -/

/-- `a2 = 2^32 + 4` narrowed: the witness exhibits the zap's 0 and
zero-fill over the live page.
kernel: include/linux/syscalls.h:__SC_CAST; mm/madvise.c:madvise,madvise_dontneed_single_vma@v6.18.46 -/
theorem madvise_narrowed_advice_witnesses_the_zap_over_the_real_table :
    syscall_spec_witness (madvise_in 65536 4096 (Z_to_bv 64 (2 ^ 32 + 4))) one_map_model
      = Ok (mkEffect 0 [] [(65536, 4096)]) one_map_model [] := by
  madvise_dispatch_witness_norm

/-- A misaligned `a0`: the witness exhibits the alignment -EINVAL, the
model untouched, at every model — the arm hands the witness `a0` as the
address, as it hands the checker.
kernel: mm/madvise.c:madvise_should_skip,is_valid_madvise@v6.18.46 -/
theorem madvise_unaligned_witnesses_einval_over_the_real_table (m : Model) :
    syscall_spec_witness (madvise_in 65537 4096 4) m
      = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  madvise_dispatch_witness_norm

end V_Mm_Madvise

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Madvise
