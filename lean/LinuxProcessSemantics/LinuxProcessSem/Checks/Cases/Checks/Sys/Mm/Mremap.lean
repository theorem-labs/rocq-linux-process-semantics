import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mremap
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mremap

/-! # Checks.Cases.Checks.Sys.Mm.Mremap — what the mremap CHECKER answers

Pins over `Checks.Sys.Mm.Mremap.check_mremap`, the checker-level half of
`theories/LinuxProcessSem/Checks/Cases/Mm/Mremap.v`.  Not part of the
trusted specification: this file is QA on the checker, written to be READ.
Line numbers are Linux v6.18.46 (commit 1f99e9ab748f), read in a checkout
at that commit, in `mm/mremap.c` unless another file is named.

TWO LEAN FILES COVER ONE ROCQ FILE, and the split is by what is being
tested.  Rocq states every worked example of `Checks/Cases/Mm/Mremap.v`
through `check_syscall`, so each fixes two things at once: what the SPEC
admits, and that the CHECKER's verdict on a concrete effect is `CheckOk`,
`CheckReject` or `CheckUnmodeled`.  `Checks/Cases/Mm/Mremap.lean` carries
the first half, as `iff`s and refutations over `mremap_spec`, and was
written while the tree had no checker to state the second half on.  This
file carries the second half: the same calls, the same effects, the same
fixtures, and the checker's verdict on each, so a checker that accepted
everything, rejected everything or declined everything fails here by name.
The four `_sound_`/`_complete_` lemmas beside the checker say that it and
the spec agree on every input, and would say so as well of a wrong spec
beside a matching wrong checker; only a verdict on a value named from
outside tells the two apart, which is what each pin below is.  The KERNEL
argument for every answer is beside the spec-level pin of the same claim
in that file and in the Rocq example the mapping at the end of this header
names; each docstring here keeps only the reading its own verdict rests on.

HOW THESE ARE STATED.  `check_mremap_row` below is the argument narrowing
of Rocq's `arm_mremap` (`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`)
and of the row for 216 in `Sys/SyscallTable.lean`, spelled once: the first
four registers as they arrive, since every argument of `mremap` is an
`unsigned long` (`SYSCALL_DEFINE5(mremap, …)`, mm/mremap.c:1961-1963,
Linux v6.18.46) and nothing is narrowed.  The direct pins isolate argument handling from table lookup; the
`_over_the_real_table` twins exercise dispatch as well.  The model fixtures are those of `Checks/Cases/Mm/Mremap.lean`
and of `Checks/Cases/Prelude.lean`, imported rather than copied, so the
two files cannot drift apart on an address or a page count; the four
INPUT fixtures Rocq's checker-level statements take (`mremap_at_in`,
`mremap_misaligned_in`, `mremap_orphan_in`, `mremap_placed_in`) have no
spec-level twin — the spec pins are stated over a symbolic input — and are
defined here.  Every equality is closed by `rfl`: `Model` has no
`DecidableEq`, so `decide` is unavailable, and the checker on a closed
input reduces to a constructor by evaluation alone.  Where Rocq writes the
post-state as `with_vmmaps <ledger> <fixture>`, the pins here write the
whole ledger out as `fixture (VmMaps.mkVmMapsFull …)`, the spec-level
file's spelling; where Rocq writes it as `mremap_model_next …` (the three
lazily backed cases) the ledgers are written out too, so the pin says what
the post-state IS rather than which arm the checker took.

WHAT IS NOT HERE.  Almost no pin carries a `probe:` line, although
`testing/syscall-check/tests/mremap_shapes.c` runs several of these shapes
against the kernel and `testing/syscall-check/traces/mremap_shapes/` holds
the runs.  Two things stand in the way.  For a `= CheckReject` pin it is
`tools/check_lean_pin_evidence.py`'s polarity reading, which classes a
statement by `¬`, `≠`, `False` and the word `Unmodeled`: that verdict
reads as positive there, so the `reject --mutate` case that matches it
would be refused as the wrong polarity.  For a `= CheckOk` pin it is the
recorded return, which the reader requires to be the pin's answer: the
kernel answers an unmutated call with an address no fixture here holds,
so only a case whose mutation fixes the return to an errno could back a
pin — and none does yet, because a pin carries exactly one evidence line
and the kernel reading beside each of these is the one the guard retraces
against the source.  Every evidence line below is a kernel reading.  Three
Rocq cases of the file are not this checker's and are not
restated: `mremap_refund_is_regrantable` is a `check_syscall` example on
`mmap` (222), and belongs with that checker's pins;
`mremap_zero_entry_passes_the_source_gate` is a fact about
`mremap_source_b`, twinned at the spec level as
`zero_entry_passes_the_source_gate`; and the `Run.apply_effect` cases and
the ledger lemmas are twinned in `Checks/Cases/Mm/Mremap.lean`.

WHICH ROCQ EXAMPLE EACH THEOREM RESTATES.  This file mirrors no Rocq file,
so it carries no `rocq-cases` register — `tools/check_lean_cases_parity.py`
would refuse one here — and the spec-level twin `Checks/Cases/Mm/Mremap.lean`
carries none either, so Rocq's `Checks/Cases/Mm/Mremap.v` is held by no
register in this tree: its checker `Example`s are compared to nothing
mechanically, and the debt is the spec-level file's to pay, where the
parity guard reads.  The mapping is therefore prose, read by no guard,
kept so a reader can find the Rocq `Example` a verdict pin restates.  Each
line is the Rocq
`Example` followed by the theorem that restates its `check_syscall`
statement; the pins under "The checker's own shape", the `_is_rejected`
and `_is_declined` twins beside the positive pins, the precedence and
boundary pins (`_precedes_`, `_at_task_size_`, `_over_task_size_`), and
everything under the "adversarial round" sections have no Rocq statement
and are this file's own.  It stops being complete the day a theorem
restating a Rocq statement is added without a line.

- `mremap_shrink_enomem_unmodeled`: `mremap_shrink_enomem_unmodeled`
- `mremap_shrink_inplace_unmodeled`: `mremap_shrink_inplace_unmodeled`
- `mremap_grow_beyond_budget_rejected`: `mremap_grow_beyond_budget_rejected`
- `mremap_move_to_occupied_range_rejected`: `mremap_move_to_occupied_range_rejected`
- `mremap_equal_size_inplace_unmodeled`: `mremap_equal_size_inplace_unmodeled`
- `mremap_equal_size_enomem_unmodeled`: `mremap_equal_size_enomem_unmodeled`
- `mremap_inplace_grow_accepts`: `mremap_inplace_grow_accepts` (Rocq's `mremap_one_page_model` is the Prelude's `tight_model`)
- `mremap_inplace_grow_into_neighbour_rejected`: `mremap_inplace_grow_into_neighbour_rejected`
- `mremap_inplace_grow_into_image_rejected`: `mremap_inplace_grow_into_image_rejected`
- `mremap_move_out_of_the_image_accepts`: `mremap_move_out_of_the_image_accepts`
- `mremap_inplace_grow_to_ceiling_accepts`: `mremap_inplace_grow_to_ceiling_accepts` (Rocq writes the source as a literal; here it is `demo_top - 8192`, as the spec-level twin spells it)
- `mremap_inplace_grow_past_ceiling_rejected`: `mremap_inplace_grow_past_ceiling_rejected`
- `mremap_move_down_from_ceiling_accepts`: `mremap_move_down_from_ceiling_accepts`
- `mremap_wrapping_new_size_einval_unmodeled`: `mremap_wrapping_new_size_einval_unmodeled`
- `mremap_wrapping_new_size_success_unmodeled`: `mremap_wrapping_new_size_success_unmodeled`
- `mremap_top_aligned_new_size_enomem_unmodeled`: `mremap_top_aligned_new_size_enomem_is_declined`
- `mremap_top_aligned_new_size_einval_unmodeled`: `mremap_top_aligned_new_size_einval_is_declined`
- `mremap_misaligned_old_size_zero_unmodeled`: `mremap_misaligned_old_size_zero_unmodeled`
- `mremap_old_size_zero_aligned_is_unmodeled`: `mremap_old_size_zero_aligned_is_unmodeled`
- `mremap_old_size_zero_gate_precedes_the_source_gate`: `mremap_old_size_zero_gate_precedes_the_source_gate`
- `mremap_wrapping_old_size_is_unmodeled`: `mremap_wrapping_old_size_is_unmodeled`
- `mremap_move_onto_brk_orphan_page_rejected`: `mremap_move_onto_brk_orphan_page_rejected`
- `mremap_move_above_brk_orphan_accepts`: `mremap_move_above_brk_orphan_accepts`
- `mremap_move_onto_orphan_without_residual_accepts`: `mremap_move_onto_orphan_without_residual_accepts`
- `mremap_lazy_shrink_inplace_unmodeled`: `mremap_lazy_shrink_inplace_unmodeled`
- `mremap_lazy_grow_bypasses_eager_delta`: `mremap_lazy_grow_bypasses_eager_delta`
- `mremap_lazy_move_relocates_materialized_pages`: `mremap_lazy_move_relocates_materialized_pages`
- `mremap_mixed_backing_fails_closed`: `mremap_mixed_backing_fails_closed`
- `mremap_move_low_destination_admitted`: `mremap_move_low_destination_admitted`
- `mremap_move_unaligned_destination_rejected`: `mremap_move_unaligned_destination_rejected`
- `mremap_move_onto_source_rejected`: `mremap_move_onto_source_rejected`
- `mremap_move_just_above_source_accepts`: `mremap_move_just_above_source_accepts`
- `mremap_inplace_grow_past_demo_top_admitted_under_high_sp`: `mremap_inplace_grow_past_demo_top_admitted_under_high_sp`
- `mremap_move_past_demo_top_rejected_under_low_sp`: `mremap_move_past_demo_top_rejected_under_low_sp`
- `mremap_move_past_demo_top_admitted_under_high_sp`: `mremap_move_past_demo_top_admitted_under_high_sp` -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mremap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap (mremap_model_next)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mremap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
  (fixture demo_sp demo_top demo_limit tight_model noaccess_three_pages
   noaccess_image_overlap)
-- Selective, because this file restates the spec-level file's cases under
-- Rocq's `mremap_`-prefixed names with the checker's verdict; a wholesale
-- `open` of both would make any shared name ambiguous for a file that
-- opens the two together.
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mremap
  (mremap_in two_page_model three_page_model roomy_model over_budget_two_pages
   budget_full_model occupied_model crowded_model
   below_image_model grow_to_ceiling_model grow_past_ceiling_model zero_entry_model
   lazy_two_pages lazy_one_page mixed_backing placement_model mremap_src
   mremap_overlapping_dst m_brk_orphan_with_source m_brk_orphan_without_residual hi_sp
   grow_past_top_hi_model move_source_lo_model move_source_hi_model high_source_model
   half_hole_model)

/-! ## Evaluation depth

Every pin below is closed by `rfl`, and the elaborator's definitional
unfolding of the checker on a closed input runs deeper than the default
`maxRecDepth` of 512 allows: the `Int` comparisons on the rounded sizes
(`TASK_SIZE <`, the shrink test, `two_pow_64 ≤`) unfold `Int.decLt`,
`Int.decLe` and `Int.decEq` through `Int.sub`/`Int.add`/`subNatNat`,
whose `Nat` recursion `Meta.whnf` folds only once both operands are raw
literals, so a literal still wrapped in `Nat.succ` or in a `BitVec.toNat`
costs a frame per step.  The unfolding is finite and fast — the whole
file elaborates in seconds — so the depth is raised once, for the file,
where `Checks/Cases/Fs/Namei.lean` raises it per declaration: there a
handful of pins need it, here every pin that gets past the flag gate does
(the ones that stop there close at the default), so a per-declaration
raise would be the same line before nearly every theorem.  The value is
one of the three that file uses (8192, 32768 and 100000, by declaration)
and the smallest of them that closes every pin here — 8192 leaves most of
them at the limit.  The kernel, which
folds literals natively, re-checks every `rfl` at its own depth.  Nothing
about the model is changed by the option: a pin that needed a deeper stack
to evaluate is not a pin that evaluates to anything else. -/
set_option maxRecDepth 32768

/-! ## The dispatcher's application of the checker -/

/-- `check_mremap` as the dispatcher applies it: the first four registers
as they arrive — Rocq's `arm_mremap` and the row for 216 in
`Sys/SyscallTable.lean`.  When the checked-arm table gains the arm, its
`ca_check_arm_mremap` unfolds to this application. -/
def check_mremap_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m

/-! ## Inputs

Rocq's four checker-level input fixtures, under their names.  a3 is
`MREMAP_MAYMOVE`, the one modeled flag word; a4 is nonzero in three of
them, as in Rocq, because Linux reads `new_addr` only under `MREMAP_FIXED`
or `MREMAP_DONTUNMAP` (`vrm_implies_new_addr`, mm/mremap.c:927-930,
Linux v6.18.46), and `mremap_placed_in` zeroes it so the placement cases
show that the model reads it no more than the kernel does. -/

/-- The call on `old_addr`, with the sizes given and a stale a4. -/
def mremap_at_in (old_addr old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [old_addr, old_size, new_size, 1, 0x12345000, 0]
    (fun _ => none) (fun _ => none)

/-- The call on the misaligned address 65537. -/
def mremap_misaligned_in (old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [65537, old_size, new_size, 1, 0x12345000, 0]
    (fun _ => none) (fun _ => none)

/-- The growing call on the one-page mapping at 131072 of the brk-orphan
fixtures. -/
def mremap_orphan_in : SyscallInput :=
  SyscallInput.mkInput 216 [131072, 4096, 8192, 1, 0x12345000, 0]
    (fun _ => none) (fun _ => none)

/-- The call of the placement cases, with a4 zero. -/
def mremap_placed_in (old_addr old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [old_addr, old_size, new_size, 1, 0, 0]
    (fun _ => none) (fun _ => none)

/-! ## The checker's own shape: the gates first, then the effect's ledgers -/

/-- a4 is inert on an accepted grow: Linux reads `new_addr` only under
FIXED or DONTUNMAP, neither present here. Both effects must be accepted,
so an unconditional decline cannot satisfy this pin.
kernel: mm/mremap.c:vrm_implies_new_addr,check_mremap_params@v6.18.46 -/
theorem mremap_a4_is_inert :
    check_mremap_row (mremap_at_in 65536 4096 8192)
      (mkEffect 65536 [] [(69632, 4096)]) tight_model
      = CheckOk (mremap_model_next tight_model 65536 4096 65536 8192) []
    ∧ check_mremap_row (mremap_placed_in 65536 4096 8192)
      (mkEffect 65536 [] [(69632, 4096)]) tight_model
      = CheckOk (mremap_model_next tight_model 65536 4096 65536 8192) [] := by
  exact ⟨rfl, rfl⟩

/-- Honest twin of the ledger and errno lies below, at the same grow state.
kernel: mm/mremap.c:expand_vma,expand_vma_in_place@v6.18.46 -/
theorem mremap_grow_honest_twin_accepts :
    check_mremap_row (mremap_in 4096 8192)
      (mkEffect 65536 [] [(69632, 4096)]) tight_model
    = CheckOk (mremap_model_next tight_model 65536 4096 65536 8192) [] := rfl

/-- A grow does not write a byte ledger; the honest twin above reaches CheckOk.
kernel: mm/mremap.c:expand_vma,do_mremap@v6.18.46 -/
theorem mremap_grow_with_a_write_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [(65536, [0])] [(69632, 4096)] [] [] []) tight_model = CheckReject := rfl

/-- A grow does not copy user bytes into the kernel; the honest twin above reaches CheckOk.
kernel: mm/mremap.c:expand_vma,do_mremap@v6.18.46 -/
theorem mremap_grow_with_a_copyin_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] [(65536, 1)]) tight_model = CheckReject := rfl

/-- The killable lock can return EINTR only for a fatal signal, which prevents
observation of the return (see `mremap_errnos`); the honest twin above reaches CheckOk.
kernel: mm/mremap.c:expand_vma,do_mremap@v6.18.46 -/
theorem mremap_grow_answered_eintr_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (mkEffect (errno_ret EINTR) [] []) tight_model = CheckReject := rfl

/-- A grow has no EINVAL result under the host premises recorded in bugs/qemu-user-mremap-grow-host-page-and-reserved-va.md; the honest twin above reaches CheckOk.
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,expand_vma,do_mremap@v6.18.46 -/
theorem mremap_grow_einval_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (mkEffect (errno_ret EINVAL) [] []) tight_model = CheckReject := rfl

/-- A flag word with a bit outside `MREMAP_MAYMOVE` declines whatever the
effect: `MREMAP_FIXED | MREMAP_MAYMOVE` is a real shape (`check_mremap_params`,
:1758-1760 lets it through) that the model does not cover, so the checker
says so before it reads the effect.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_a_fixed_flag_is_declined :
    check_mremap_row (SyscallInput.mkInput 216 [65536, 8192, 4096, 3, 0, 0]
        (fun _ => none) (fun _ => none))
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- …and so does a bare 0, the shape that forbids a move: the shrink in
place that Linux would still perform (`mremap_at`'s `MREMAP_SHRINK` arm
does not read the flags, :1560-1572) is outside the modeled flag word, and
the model declines rather than guess.
kernel: mm/mremap.c:check_mremap_params,mremap_at@v6.18.46 -/
theorem mremap_flags_zero_is_declined :
    check_mremap_row (SyscallInput.mkInput 216 [65536, 8192, 4096, 0, 0, 0]
        (fun _ => none) (fun _ => none))
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_foreign_flags_misaligned_unmodeled :
    check_mremap_row (SyscallInput.mkInput 216 [65537, 8192, 4096, 8, 0, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_an_effect_with_a_write_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [(65536, [0])] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_an_effect_with_a_copyin_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] [(65536, 1)]) two_page_model
    = CheckUnmodeled := by
  rfl

/-- The declines come before the effect is looked at: the same odd-shaped
effect against a declined call is `CheckUnmodeled`, not `CheckReject`.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_a_declined_call_is_declined_whatever_the_effect_shape :
    check_mremap_row (mremap_in 8192 18446744073709547520)
      (SyscallEffect.mkEffectU 65536 [(65536, [0])] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-! ## The argument gates -/

/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_address_enomem_unmodeled :
    check_mremap_row (mremap_misaligned_in 8192 4096)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_address_success_unmodeled :
    check_mremap_row (mremap_misaligned_in 8192 4096)
      (mkEffect 65537 [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_wrapping_new_size_einval_unmodeled :
    check_mremap_row (mremap_in 8192 18446744073709551615)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_wrapping_new_size_success_unmodeled :
    check_mremap_row (mremap_in 8192 18446744073709551615)
      (mkEffect 65536 [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_zero_new_size_einval_unmodeled :
    check_mremap_row (mremap_in 8192 0)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_zero_new_size_precedes_the_zero_old_size_decline_unmodeled :
    check_mremap_row (mremap_in 0 0)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- A page-aligned new size in the top page of the word rounds to itself,
above `TASK_SIZE`, and the call DECLINES: Rocq's
`mremap_top_aligned_new_size_is_enomem` accepts -ENOMEM here, the answer of
Linux v6.12's `MREMAP_MAYMOVE` grow path, which Linux v6.18.46's
`check_mremap_params` (:1775-1776) never gives; neither is claimed, as the
header says.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_top_aligned_new_size_enomem_is_declined :
    check_mremap_row (mremap_in 8192 18446744073709547520)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- …and -EINVAL, which v6.18.46 does answer, is declined too, where Rocq's
`mremap_top_aligned_new_size_einval_rejected` rejects it: a decline is
neither acceptance nor refusal.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_top_aligned_new_size_einval_is_declined :
    check_mremap_row (mremap_in 8192 18446744073709547520)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_above_task_size_unmodeled :
    check_mremap_row (mremap_misaligned_in 8192 18446744073709547520)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- The decline is STRICT at `TASK_SIZE`, as the kernel's test is: a new
length of exactly `TASK_SIZE` passes `new_len > TASK_SIZE` (:1775-1776)
and is a grow the model admits -ENOMEM for — `may_expand_vm`'s from
`check_prep_vma` (:1742-1743), or the placement search's, since no
destination of that length fits below `alloc_top`.
kernel: mm/mremap.c:check_mremap_params,check_prep_vma@v6.18.46 -/
theorem mremap_new_size_at_task_size_is_not_declined :
    check_mremap_row (mremap_in 8192 (Z_to_bv 64 TASK_SIZE))
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckOk two_page_model [] := by
  rfl

/-- …and one page over it is declined, with the -EINVAL v6.18.46 answers
offered.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_new_size_one_page_over_task_size_is_declined :
    check_mremap_row (mremap_in 8192 (Z_to_bv 64 (TASK_SIZE + 4096)))
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_old_size_zero_unmodeled :
    check_mremap_row (mremap_misaligned_in 0 4096)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- An aligned zero old size declines: the answer of `check_prep_vma`'s
duplicate arm (:1690-1694) turns on `VM_SHARED | VM_MAYSHARE`, which the
ledger does not record (Rocq's `mremap_old_size_zero_aligned_is_unmodeled`).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mremap_old_size_zero_aligned_is_unmodeled :
    check_mremap_row (mremap_in 0 4096)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- …and it declines on a ledger holding a zero-size entry at the address
too, so the decline is the old-size gate's and not the source gate's
(Rocq's `mremap_old_size_zero_gate_precedes_the_source_gate`; the
spec-level `zero_entry_passes_the_source_gate` shows the source gate
would have let that entry through).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mremap_old_size_zero_gate_precedes_the_source_gate :
    check_mremap_row (mremap_in 0 4096)
      (mkEffect (errno_ret ENOMEM) [] []) zero_entry_model
    = CheckUnmodeled := by
  rfl

/-- An old size in the top partial page wraps to 0 under `do_mremap`'s
`PAGE_ALIGN` (:1917) and meets the same duplicate arm: declined (Rocq's
`mremap_wrapping_old_size_is_unmodeled`).
kernel: mm/mremap.c:do_mremap,check_prep_vma@v6.18.46 -/
theorem mremap_wrapping_old_size_is_unmodeled :
    check_mremap_row (mremap_in 18446744073709551615 4096)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- A source whose backing is MIXED — one lazy page under a two-page entry
— declines: which provenance the post-state inherits is not something the
ledger can say (Rocq's `mremap_mixed_backing_fails_closed`).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mremap_mixed_backing_fails_closed :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) mixed_backing
    = CheckUnmodeled := by
  rfl

/-- A source the ledger does not hold declines rather than answer the
-EFAULT `check_prep_vma` gives a failed `vma_lookup` (:1658-1659): the
ledger holds the model's own grants and not every VMA of the process, so
an address it lacks may still be mapped.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mremap_untracked_source_is_declined :
    check_mremap_row (mremap_at_in 131072 8192 4096)
      (mkEffect (errno_ret EFAULT) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- …and so does a strict PREFIX of a tracked entry, offered the move Linux
would perform for it — `check_prep_vma` asks only `old_len ≤ vma->vm_end -
addr` (:1720-1721), and `vrm_can_expand_in_place` (:1436-1437) sends a
prefix to the move path — because `mremap_source_b` demands the exact
entry.  The narrowing is the safe direction; the pin keeps it visible.
kernel: mm/mremap.c:check_prep_vma,vrm_can_expand_in_place@v6.18.46 -/
theorem mremap_prefix_of_a_tracked_entry_is_declined :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-! ## Equal size: `mremap_at`'s `MREMAP_NO_RESIZE` arm -/

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_inplace_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect 65536 [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_enomem_unmodeled :
    check_mremap_row (mremap_in 8192 8192)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_with_a_zero_fill_unmodeled :
    check_mremap_row (mremap_in 8192 8192)
      (mkEffect 65536 [] [(65536, 8192)]) two_page_model
    = CheckUnmodeled := by
  rfl

/-! ## The shrink: `mremap_at`'s `MREMAP_SHRINK` arm -/

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_enomem_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_inplace_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_unmapping_the_wrong_page_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_returning_the_new_end_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 69632 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_that_moves_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 131072 [] [] [(65536, 8192)]
        [MemCopy.mkCopy 65536 131072 8192] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_answered_einval_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_efault_on_a_modeled_source_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (mkEffect (errno_ret EFAULT) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_lazy_shrink_inplace_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) lazy_two_pages
    = CheckUnmodeled := by
  rfl

/-! ## The in-place grow: `expand_vma` when `vrm_can_expand_in_place` holds -/

/-- The in-place grow is admitted: `expand_vma_in_place` extends the VMA
(:1470) and the new page, with no page tables behind it, reads as zeroes
(Rocq's `mremap_inplace_grow_accepts`).
kernel: mm/mremap.c:expand_vma,vrm_can_expand_in_place,expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_accepts :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) tight_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) [] := by
  rfl

/-- …and the same grow WITHOUT the zero-fill is a lie: the grown page is
fresh anonymous memory, and the zeroes ledger has to say so.
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_without_the_zero_fill_is_rejected :
    check_mremap_row (mremap_in 4096 8192) (mkEffect 65536 [] []) tight_model
    = CheckReject := by
  rfl

/-- -ENOMEM beside a zero-fill is rejected: `expand_vma_in_place` refuses
the charge (:1458-1459) before anything is mapped.
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_enomem_with_a_zero_fill_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [(69632, 4096)] [] [] []) tight_model
    = CheckReject := by
  rfl

/-- A grow past the budget is rejected: `may_expand_vm` (mm/mmap.c:1324-1347)
refuses the delta from `check_prep_vma` (:1742-1743) before any arm runs
(Rocq's `mremap_grow_beyond_budget_rejected`).
kernel: mm/mremap.c:check_prep_vma; mm/mmap.c:may_expand_vm@v6.18.46 -/
theorem mremap_grow_beyond_budget_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (mkEffect 65536 [] [(69632, 4096)]) budget_full_model
    = CheckReject := by
  rfl

/-- …and the -ENOMEM that refusal answers is accepted, the state unchanged.
kernel: mm/mremap.c:check_prep_vma; mm/mmap.c:may_expand_vm@v6.18.46 -/
theorem mremap_grow_beyond_budget_enomem_accepts :
    check_mremap_row (mremap_in 4096 8192)
      (mkEffect (errno_ret ENOMEM) [] []) budget_full_model
    = CheckOk budget_full_model [] := by
  rfl

/-- A live neighbour directly above the source refuses the in-place grow:
`vma_expandable`'s `find_vma_intersection` (:1421-1422) sees it, and had
the kernel merged the two into one VMA, `vrm_can_expand_in_place`
(:1436-1437) refuses a source that is not its VMA's tail just the same
(Rocq's `mremap_inplace_grow_into_neighbour_rejected`).
kernel: mm/mremap.c:vma_expandable,vrm_can_expand_in_place@v6.18.46 -/
theorem mremap_inplace_grow_into_neighbour_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) crowded_model
    = CheckReject := by
  rfl

/-- …and so does a LOAD segment there: the image's reservation is a VMA
the same test walks (Rocq's `mremap_inplace_grow_into_image_rejected`).
kernel: mm/mremap.c:vma_expandable@v6.18.46 -/
theorem mremap_inplace_grow_into_image_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) below_image_model
    = CheckReject := by
  rfl

/-- The grant top is INCLUSIVE for the in-place grow: a mapping two pages
below `demo_top` grows to end exactly at it (Rocq's
`mremap_inplace_grow_to_ceiling_accepts`).
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_to_ceiling_accepts :
    check_mremap_row (mremap_at_in (Z_to_bv 64 (demo_top - 8192)) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 8192)) []
        [(Z_to_bv 64 (demo_top - 4096), 4096)] [] [] []) grow_to_ceiling_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 8192), 8192)] []
        0 0 8192 0 demo_sp)) [] := by
  rfl

/-- …and one page higher the grown mapping would cross into the stack band:
rejected.  The refusal is the MODEL's `alloc_top` bound, read from the
ledger's entry `sp`; `vma_expandable` (:1415-1427) tests only overflow,
an intersecting VMA and a `MAP_FIXED` probe, and the argument that a
modeled trace never asks is beside the spec-level
`inplace_grow_past_ceiling_rejected` (Rocq's
`mremap_inplace_grow_past_ceiling_rejected`).
kernel: mm/mremap.c:vma_expandable; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem mremap_inplace_grow_past_ceiling_rejected :
    check_mremap_row (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) []
        [(Z_to_bv 64 demo_top, 4096)] [] [] []) grow_past_ceiling_model
    = CheckReject := by
  rfl

/-- …while the same grow is admitted once the ledger's stack pointer is
`hi_sp`: the bound is the ledger's, not a constant (Rocq's
`mremap_inplace_grow_past_demo_top_admitted_under_high_sp`).
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_past_demo_top_admitted_under_high_sp :
    check_mremap_row (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) []
        [(Z_to_bv 64 demo_top, 4096)] [] [] []) grow_past_top_hi_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] []
        0 0 8192 (Z_to_bv 64 mmap_base_max) hi_sp)) [] := by
  rfl

/-- A lazy grow succeeds at a FULL backed budget: the new page is a
reservation, not an eager charge, as `vrm_calc_charge` charges nothing for
a VMA without `VM_ACCOUNT` (:976-977) (Rocq's
`mremap_lazy_grow_bypasses_eager_delta`, post-state written out).
kernel: mm/mremap.c:vrm_calc_charge,expand_vma_in_place@v6.18.46 -/
theorem mremap_lazy_grow_bypasses_eager_delta :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) lazy_one_page
    = CheckOk (with_vm_backing [(65536, 8192)] [65536]
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 4096 0 demo_sp))) [] := by
  rfl

/-! ## The move: `expand_vma` through `vrm_set_new_addr` and `move_vma` -/

/-- A move onto a range another mapping holds is rejected: the destination
search runs over the live VMAs (`vrm_set_new_addr`, :957-960;
`vm_unmapped_area`, mm/mmap.c:663) and never returns an occupied range
(Rocq's `mremap_move_to_occupied_range_rejected`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mremap_move_to_occupied_range_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) occupied_model
    = CheckReject := by
  rfl

/-- A move past the budget is rejected as the in-place grow is: the gate
is `may_expand_vm` (mm/mmap.c:1324-1347) from `check_prep_vma`
(:1742-1743), which `do_mremap` runs (:1932) before `mremap_at` picks
either path (:1937).
kernel: mm/mremap.c:check_prep_vma,do_mremap; mm/mmap.c:may_expand_vm@v6.18.46 -/
theorem mremap_move_beyond_budget_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) budget_full_model
    = CheckReject := by
  rfl

/-- The move out from under the image is admitted, the reservation
untouched: the source is unmapped (`unmap_source_vma`, :1078), its
contents copied (`copy_vma_and_data`, :1181), and the grown page above
the copy zero-filled (Rocq's `mremap_move_out_of_the_image_accepts`).
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_out_of_the_image_accepts :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) below_image_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [(69632, 4096)] [(131072, 8192)] []
        0 0 8192 0 demo_sp)) [] := by
  rfl

/-- A move that leaves the source mapped is rejected: `move_vma` unmaps
it (`unmap_source_vma` at :1312) unless `MREMAP_DONTUNMAP` asked
otherwise, and that flag is outside the modeled word.  The unmap is best
effort — a failed `do_vmi_munmap` is swallowed (:1075-1076, :1125-1128)
and the source retained — but a retained source reads as zeroes once
`move_page_tables` (:1208) has moved its pages, so this effect, which
copies the source's bytes, is not that outcome either; the outcome itself
is bugs/mremap-maymove-answers-success.md's, outside the model.
kernel: mm/mremap.c:move_vma,unmap_source_vma@v6.18.46 -/
theorem mremap_move_leaving_the_source_mapped_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] []
        [MemCopy.mkCopy 65536 131072 4096] []) below_image_model
    = CheckReject := by
  rfl

/-- …and so is one that names no copy: the destination holds the source's
contents (`copy_vma_and_data`, :1181-1237, through `move_page_tables`),
and a ledger that says otherwise says the old bytes were lost.
kernel: mm/mremap.c:move_vma,copy_vma_and_data,move_page_tables@v6.18.46 -/
theorem mremap_move_without_the_copy_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)] [] [])
      below_image_model
    = CheckReject := by
  rfl

/-- …and so is one whose grown page is not zero-filled: neither `copy_vma`
(mm/vma.c:1853, from `copy_vma_and_data` at :1193) nor `move_page_tables`
(:1208) installs a page table for the delta, so the page beyond the copy
reads as fresh zeroes, and a ledger without them says it held something.
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_move_without_the_zero_fill_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) below_image_model
    = CheckReject := by
  rfl

/-- The move DOWN from the ceiling, to 65536, is admitted (Rocq's
`mremap_move_down_from_ceiling_accepts`).
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_down_from_ceiling_accepts :
    check_mremap_row (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(Z_to_bv 64 (demo_top - 4096), 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 (demo_top - 4096)) 65536 4096] []) grow_past_ceiling_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) [] := by
  rfl

/-- A lazy move relocates the touched page with the mapping: its charge
moves to 131072 and the reservation follows (Rocq's
`mremap_lazy_move_relocates_materialized_pages`, post-state written out).
kernel: mm/mremap.c:move_vma,copy_vma_and_data,move_page_tables@v6.18.46 -/
theorem mremap_lazy_move_relocates_materialized_pages :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) lazy_one_page
    = CheckOk (with_vm_backing [(131072, 8192)] [131072]
        (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192)] [] 0 0 4096 0 demo_sp))) [] := by
  rfl

/-- A move onto the brk orphan's page is rejected: the destination
`[65536, 73728)` crosses the residual brk entry, which the search over the
live VMAs (`vrm_set_new_addr`, :957-960; `vm_unmapped_area`, mm/mmap.c:663)
never returns (Rocq's `mremap_move_onto_brk_orphan_page_rejected`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mremap_move_onto_brk_orphan_page_rejected :
    check_mremap_row mremap_orphan_in
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
        [MemCopy.mkCopy 131072 65536 4096] []) m_brk_orphan_with_source
    = CheckReject := by
  rfl

/-- …and one page higher, clear of the residual, the move is admitted with
the protected range carried over verbatim (Rocq's
`mremap_move_above_brk_orphan_accepts`).
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_above_brk_orphan_accepts :
    check_mremap_row mremap_orphan_in
      (SyscallEffect.mkEffectU 69632 [] [(73728, 4096)] [(131072, 4096)]
        [MemCopy.mkCopy 131072 69632 4096] []) m_brk_orphan_with_source
    = CheckOk (fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(69632, 8192), (65536, 4084)]
        [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)) [] := by
  rfl

/-- With the residual entry taken out of the same state the move onto the
orphan page is ACCEPTED: the guard reads the live entries and nothing
else, as the kernel's search does (`vrm_set_new_addr`, :957-960;
`vm_unmapped_area`, mm/mmap.c:663).  The state is unreachable; the case
is kept so the load-bearing property is visible (Rocq's
`mremap_move_onto_orphan_without_residual_accepts`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mremap_move_onto_orphan_without_residual_accepts :
    check_mremap_row mremap_orphan_in
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
        [MemCopy.mkCopy 131072 65536 4096] []) m_brk_orphan_without_residual
    = CheckOk (fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(65536, 8192)] [(65536, 4096)]
        65536 69620 demo_limit 0 demo_sp)) [] := by
  rfl

/-! ## Placement: the destination is any free, aligned range under the top -/

/-- A growing move to a low destination is admitted: 0x80000000 is
page-aligned, positive, below the ceiling and free, which is everything
the model asks of a preference-free placement, and `__get_unmapped_area`
(mm/mmap.c:811-864) is free to answer it (Rocq's
`mremap_move_low_destination_admitted`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mremap_move_low_destination_admitted :
    check_mremap_row (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 0x80000000) []
        [(Z_to_bv 64 0x80001000, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000000) 4096] [])
      placement_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 8192)] [] 0 0 8192
        (Z_to_bv 64 mmap_base_max) demo_sp)) [] := by
  rfl

/-- An unaligned destination is rejected: `__get_unmapped_area` answers
-EINVAL to one (mm/mmap.c:859-860), so the search never returns it
(Rocq's `mremap_move_unaligned_destination_rejected`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mremap_move_unaligned_destination_rejected :
    check_mremap_row (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 0x80000001) []
        [(Z_to_bv 64 0x80001001, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000001) 4096] [])
      placement_model
    = CheckReject := by
  rfl

/-- A destination of 0 is rejected: the search's floor is a page —
`generic_get_unmapped_area_topdown` sets `low_limit` to `PAGE_SIZE`
(mm/mmap.c:765) and its bottom-up fallback to `TASK_UNMAPPED_BASE`
(mm/mmap.c:781) — so `vrm_set_new_addr` (:957-960) never receives it.  At
0 the positivity conjunct is what refuses: the address is aligned, the two
pages under the source are free, and the zero ledger is the tail's.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem mremap_move_to_address_zero_is_rejected :
    check_mremap_row (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
      (SyscallEffect.mkEffectU 0 [] [(4096, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) 0 4096] []) placement_model
    = CheckReject := by
  rfl

/-- A destination that OVERLAPS the source is rejected: Linux runs the
search while the source VMA is still live (`vrm_set_new_addr` from
`expand_vma` at :1539, the source unmapped only by `move_vma` at :1312),
so the destination cannot be a range the source still holds (Rocq's
`mremap_move_onto_source_rejected`).
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_onto_source_rejected :
    check_mremap_row (mremap_placed_in mremap_src 4096 8192)
      (SyscallEffect.mkEffectU mremap_overlapping_dst [] [(mremap_src, 4096)] [(mremap_src, 4096)]
        [MemCopy.mkCopy mremap_src mremap_overlapping_dst 4096] []) placement_model
    = CheckReject := by
  rfl

/-- …and the ordinary move, one page above the source, is admitted (Rocq's
`mremap_move_just_above_source_accepts`).
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_just_above_source_accepts :
    check_mremap_row (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 0x2aaaaac000) []
        [(Z_to_bv 64 0x2aaaaad000, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x2aaaaac000) 4096] [])
      placement_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x2aaaaac000, 8192)] [] 0 0 8192
        (Z_to_bv 64 mmap_base_max) demo_sp)) [] := by
  rfl

/-- A move whose destination ends one page past `demo_top` is rejected
under the low stack pointer — the model's bound, read from the ledger's
entry `sp`; the kernel's own top-down search stops at the mm's
`mmap_base` on its first attempt (`generic_get_unmapped_area_topdown`,
mm/mmap.c:765-766), but its bottom-up fallback (:781-782) and the legacy
layout (:713-714) run to `mmap_end`, which riscv's `arch_get_mmap_end`
sets at `TASK_SIZE_64` (arch/riscv/include/asm/processor.h:20-23, :32),
so the band above `mmap_base` is not the kernel's bound; the argument for
the model's is beside
the spec-level `move_past_demo_top_rejected_under_low_sp` (Rocq's
`mremap_move_past_demo_top_rejected_under_low_sp`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem mremap_move_past_demo_top_rejected_under_low_sp :
    check_mremap_row (mremap_at_in 65536 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
        [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
      move_source_lo_model
    = CheckReject := by
  rfl

/-- …and admitted under the high one (Rocq's
`mremap_move_past_demo_top_admitted_under_high_sp`).
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_past_demo_top_admitted_under_high_sp :
    check_mremap_row (mremap_at_in 65536 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
        [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
      move_source_hi_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 8192
        (Z_to_bv 64 mmap_base_max) hi_sp)) [] := by
  rfl

/-! ## The adversarial round

CLAUDE.md asks that a syscall checker be met with adversarial cases — the
lies Linux could never tell (where qemu-user tells one, the docstring
says so), in the shapes the conformance harness's
mutation operators (`testing/syscall-check/main.ml`) produce — and that
every discussion get a test on both sides.  The sections below are that
round for `check_mremap`: each triple was first evaluated against Linux
v6.18.46 by reading `mm/mremap.c`, then against the checker, and the two
never disagreed on a modeled shape; what the round found was DECISIONS
WITHOUT A PIN, which these are.  They are grouped as the round was — gate
order, refused argument shapes, rounding below page granularity, then one
group per arm — and each states the checker's answer to one input the
sections above do not reach: a second errno the arm must refuse, a ledger
that is right in one field and wrong in another, a boundary value the
kernel rounds or wraps, a fixture with room the earlier ones lack.

Three things the round settled without a pin are pinned in the deep
review's round at the end of this file.  A destination of 4096 is admitted
(`mremap_move_to_page_one_is_admitted`; `mremap_move_low_destination_admitted`
above places at 0x80000000, not at the floor) because `mmap_min_addr` is a
sysctl whose default is a configuration choice, not a kernel constant.  Shrinking calls, including candidates splitting the unmap into two entries,
now decline (`mremap_shrink_unmap_split_in_two_unmodeled`).
`do_mremap` spells -EINTR (mm/mremap.c:1924-1925, Linux v6.18.46): the
answer of a task killed while it waits for the mmap lock, which returns to
nobody. The shrink pin now declines the whole shape
(`mremap_shrink_answered_eintr_unmodeled`). -/

/-- Two live rw pages at 65536 under a four-page budget: room for a one-page
grow, in place or moved, of a TWO-page source, so a destination can meet the
source's tail without the budget refusing first. -/
def two_page_roomy_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 16384 0 demo_sp)

/-! ## The adversarial round: gate order -/
/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_top_aligned_enomem_unmodeled :
    check_mremap_row (mremap_misaligned_in 8192 18446744073709547520)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_flags_zero_misaligned_unmodeled :
    check_mremap_row (SyscallInput.mkInput 216 [65537, 8192, 4096, 0, 0, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- `MREMAP_DONTUNMAP` alone declines: Linux answers it -EINVAL for want of
`MREMAP_MAYMOVE` (:1791-1792), and the model does not cover the flag.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_dontunmap_is_declined :
    check_mremap_row (SyscallInput.mkInput 216 [65536, 8192, 4096, 4, 0x12345000, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- …and with `MREMAP_MAYMOVE` beside it too: a resizing `DONTUNMAP` call is
-EINVAL (:1795-1796), an equal-size one is served by `mremap_to`, and
neither is claimed.
kernel: mm/mremap.c:check_mremap_params,mremap_to@v6.18.46 -/
theorem mremap_dontunmap_maymove_is_declined :
    check_mremap_row (SyscallInput.mkInput 216 [65536, 8192, 4096, 5, 0x12345000, 0]
        (fun _ => none) (fun _ => none))
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_both_sizes_zero_enomem_unmodeled :
    check_mremap_row (mremap_in 0 0) (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-! ## The adversarial round: the argument gates, refused shapes -/
/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_efault_unmodeled :
    check_mremap_row (mremap_misaligned_in 8192 4096) (mkEffect (errno_ret EFAULT) [] [])
      two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_einval_with_a_ledger_unmodeled :
    check_mremap_row (mremap_misaligned_in 8192 4096)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_new_size_zero_success_unmodeled :
    check_mremap_row (mremap_in 8192 0) (mkEffect 65536 [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_new_size_zero_enomem_unmodeled :
    check_mremap_row (mremap_in 8192 0) (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_lowest_wrapping_new_size_einval_unmodeled :
    check_mremap_row (mremap_in 8192 18446744073709547521)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- …and -EINVAL, the answer one page higher, is rejected at exactly
`TASK_SIZE`: the comparison is strict.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_exactly_task_size_einval_is_rejected :
    check_mremap_row (mremap_in 4096 (Z_to_bv 64 TASK_SIZE))
      (mkEffect (errno_ret EINVAL) [] []) tight_model
    = CheckReject := by
  rfl
/-- `TASK_SIZE - 1` rounds up to `TASK_SIZE` (`do_mremap`, :1918) and is the
same unsatisfiable grow.
kernel: mm/mremap.c:do_mremap,check_mremap_params,vrm_set_new_addr; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mremap_task_size_minus_one_rounds_to_task_size :
    check_mremap_row (mremap_in 4096 (Z_to_bv 64 (TASK_SIZE - 1)))
      (mkEffect (errno_ret ENOMEM) [] []) tight_model
    = CheckOk tight_model [] := by
  rfl
/-- One byte above `TASK_SIZE` rounds a page above it and declines, on the
-EINVAL v6.18.46 answers (:1775-1776) and on the -ENOMEM v6.12's grow path
answered (today `check_prep_vma`'s `may_expand_vm`, :1742-1743, or the
placement search) alike — both conjuncts, so neither errno is one the
checker accepts.
kernel: mm/mremap.c:do_mremap,check_mremap_params,check_prep_vma@v6.18.46 -/
theorem mremap_one_past_task_size_is_declined :
    check_mremap_row (mremap_in 4096 (Z_to_bv 64 (TASK_SIZE + 1)))
      (mkEffect (errno_ret EINVAL) [] []) tight_model
    = CheckUnmodeled
    ∧ check_mremap_row (mremap_in 4096 (Z_to_bv 64 (TASK_SIZE + 1)))
      (mkEffect (errno_ret ENOMEM) [] []) tight_model
    = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> rfl
/-! ## The adversarial round: rounding below page granularity -/
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_new_size_4097_is_equal_size_unmodeled :
    check_mremap_row (mremap_in 8192 4097) (mkEffect 65536 [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_new_size_4097_shrink_shaped_unmodeled :
    check_mremap_row (mremap_in 8192 4097)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_new_size_4097_enomem_unmodeled :
    check_mremap_row (mremap_in 8192 4097) (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_new_size_4095_is_a_one_page_shrink_unmodeled :
    check_mremap_row (mremap_in 8192 4095)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- A 4095-byte OLD size rounds to the one-page entry (`do_mremap`, :1917)
and the in-place grow is admitted as for 4096.
kernel: mm/mremap.c:do_mremap,expand_vma_in_place@v6.18.46 -/
theorem mremap_old_size_4095_rounds_to_the_entry :
    check_mremap_row (mremap_in 4095 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) tight_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) [] := by
  rfl
/-! ## The adversarial round: the shrink -/
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_unmapping_too_much_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 8192)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_with_a_zero_fill_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [(65536, 4096)] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_with_a_copy_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [MemCopy.mkCopy 65536 65536 4096] [])
      two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_without_the_unmap_unmodeled :
    check_mremap_row (mremap_in 8192 4096) (mkEffect 65536 [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_enomem_with_the_unmap_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_answered_eperm_unmodeled :
    check_mremap_row (mremap_in 8192 4096) (mkEffect (errno_ret EPERM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_answered_eagain_unmodeled :
    check_mremap_row (mremap_in 8192 4096) (mkEffect (errno_ret EAGAIN) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_by_two_refunds_two_pages_unmodeled :
    check_mremap_row (mremap_in 12288 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 8192)] [] []) three_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_by_two_short_tail_unmodeled :
    check_mremap_row (mremap_in 12288 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) three_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_by_two_wrong_base_unmodeled :
    check_mremap_row (mremap_in 12288 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(73728, 4096)] [] []) three_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_on_an_over_budget_ledger_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) over_budget_two_pages
    = CheckUnmodeled := by
  rfl
/-! ## The adversarial round: the in-place grow -/
/-- An in-place grow that zero-fills the SOURCE page instead of the grown
one is rejected: `vma_merge_extend` (from :1470) installs no page tables for
the existing pages, and their contents survive.
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_rezeroing_the_source_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(65536, 4096)] [] [] []) tight_model
    = CheckReject := by
  rfl
/-- …and one that zero-fills MORE than the delta is rejected.
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_zero_filling_too_much_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 8192)] [] [] []) tight_model
    = CheckReject := by
  rfl
/-- A MOVED return beside in-place zeroes is rejected: a return other than
`addr` is `move_vma`'s `new_addr` (:1316), whose ledger unmaps and copies
the source.
kernel: mm/mremap.c:expand_vma,move_vma@v6.18.46 -/
theorem mremap_moved_return_with_in_place_zeroes_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(69632, 4096)] [] [] []) tight_model
    = CheckReject := by
  rfl
/-- An in-place grow that also unmaps the source is rejected: `expand_vma`
returns `addr` at :1526 without reaching `move_vma`.
kernel: mm/mremap.c:expand_vma,expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_with_an_unmap_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(65536, 4096)] [] []) tight_model
    = CheckReject := by
  rfl
/-- …and so is one carrying a copy.
kernel: mm/mremap.c:expand_vma,expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_with_a_copy_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [MemCopy.mkCopy 65536 69632 4096] [])
      tight_model
    = CheckReject := by
  rfl
/-- -ENOMEM that also unmapped the source is rejected: under `MREMAP_MAYMOVE`
a failed `move_vma` unmaps the DESTINATION (`copy_vma_and_data` re-points
the request at it, :1218-1228) and returns the errno (:1316), so the source
stays as it was.
kernel: mm/mremap.c:move_vma,copy_vma_and_data,unmap_source_vma@v6.18.46 -/
theorem mremap_grow_enomem_with_an_unmap_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) tight_model
    = CheckReject := by
  rfl
/-- -EAGAIN on a grow is rejected: `mlock_future_ok` (mm/mmap.c:228, from
:1739-1740) refuses only a `VM_LOCKED` VMA, which nothing on the modeled
surface makes.
kernel: mm/mremap.c:check_prep_vma; mm/mmap.c:mlock_future_ok@v6.18.46 -/
theorem mremap_grow_answered_eagain_is_rejected :
    check_mremap_row (mremap_in 4096 8192) (mkEffect (errno_ret EAGAIN) [] []) tight_model
    = CheckReject := by
  rfl
/-- -EINVAL on a grow whose arguments passed every gate is rejected: the
remaining -EINVAL of `check_prep_vma` (:1731-1734) needs `pgoff + new_len
>> 12` to wrap, which a source under `alloc_top` cannot.
kernel: mm/mremap.c:check_mremap_params,check_prep_vma@v6.18.46 -/
theorem mremap_grow_answered_einval_is_rejected :
    check_mremap_row (mremap_in 4096 8192) (mkEffect (errno_ret EINVAL) [] []) tight_model
    = CheckReject := by
  rfl
/-- -EFAULT on a grow of a modeled source is rejected: `old_len > vm_end -
addr` (:1720-1721) is excluded by the exact entry, and `VM_DONTEXPAND |
VM_PFNMAP` (:1736-1737) is never set on an anonymous grant.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mremap_grow_answered_efault_is_rejected :
    check_mremap_row (mremap_in 4096 8192) (mkEffect (errno_ret EFAULT) [] []) tight_model
    = CheckReject := by
  rfl
/-- -EPERM on a grow is rejected: `check_prep_vma`'s sealed test
(:1662-1663) as on the shrink, and the move path's security hook —
`mm_get_unmapped_area_vmflags`'s call at mm/mmap.c:862-863, into
`cap_mmap_addr` (security/commoncap.c:1459-1471) — cannot fire on a
NULL-hint search, whose floor is clamped to `mmap_min_addr`
(mm/vma.c:2898-2899, :2955-2956), itself at least `dac_mmap_min_addr`
(security/min_addr.c:17-24).
kernel: mm/mremap.c:check_prep_vma; mm/mmap.c:mm_get_unmapped_area_vmflags; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mremap_grow_answered_eperm_is_rejected :
    check_mremap_row (mremap_in 4096 8192) (mkEffect (errno_ret EPERM) [] []) tight_model
    = CheckReject := by
  rfl
/-- -ENOMEM on a grow the ledger has room for is accepted with the state
unchanged: `may_expand_vm` (:1742-1743), the commit charge
(`expand_vma_in_place`, :1458-1459; `move_vma`, :1281-1282) and a failed
`copy_vma` (`copy_vma_and_data`, :1193-1198) can each refuse, none having
changed a mapping.
kernel: mm/mremap.c:check_prep_vma,expand_vma_in_place,move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_grow_enomem_preserves_state :
    check_mremap_row (mremap_in 4096 8192) (mkEffect (errno_ret ENOMEM) [] []) tight_model
    = CheckOk tight_model [] := by
  rfl
/-- An in-place grow by TWO pages zero-fills a two-page tail
(`vma_merge_extend` from :1470 extends by `vrm->delta`).
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_by_two_accepts :
    check_mremap_row (mremap_in 4096 12288)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 8192)] [] [] []) roomy_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 16384 0 demo_sp)) [] := by
  rfl
/-- …and zero-filling only the OLD length's worth of it is rejected: the
delta is `new_len - old_len`, not `old_len`.
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_by_two_short_tail_is_rejected :
    check_mremap_row (mremap_in 4096 12288)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) roomy_model
    = CheckReject := by
  rfl
/-- With a live neighbour above the source the grow still has two admitted
answers beside the rejected in-place one: -ENOMEM…
kernel: mm/mremap.c:vma_expandable,expand_vma,move_vma@v6.18.46 -/
theorem mremap_crowded_grow_enomem_accepts :
    check_mremap_row (mremap_in 4096 8192) (mkEffect (errno_ret ENOMEM) [] []) crowded_model
    = CheckOk crowded_model [] := by
  rfl
/-- …and the move, the neighbour carried over untouched: `vma_expandable`
(:1421-1422) sends `expand_vma` to `vrm_set_new_addr` and `move_vma`
(:1539-1543).
kernel: mm/mremap.c:vma_expandable,expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_crowded_grow_moves :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) crowded_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192), (69632, 4096)] [] 0 0 16384 0 demo_sp))
        [] := by
  rfl
/-! ## The adversarial round: the move -/
/-- The growing move of a one-page source to 131072, on the ledger the lies
below vary: the source unmapped, its one page copied, the grown page
zero-filled.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_grow_fresh_move_accepts :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) tight_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192)] [] 0 0 8192 0 demo_sp)) [] := by
  rfl
/-- A copy the length of the NEW size is rejected: `copy_vma_and_data`
moves `vrm->old_len` bytes of page tables (:1191, :1208), and the delta has
none to move.
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_move_copying_too_much_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 8192] []) tight_model
    = CheckReject := by
  rfl
/-- A copy from the page ABOVE the source is rejected: the copy runs from
`vrm->addr` (:1191).
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_move_copying_from_the_wrong_source_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 69632 131072 4096] []) tight_model
    = CheckReject := by
  rfl
/-- …and a copy landing a page into the destination is rejected: the copy
runs to `vrm->new_addr` (:1191), which is what is returned (:1316).
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_move_copying_to_the_wrong_destination_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 135168 4096] []) tight_model
    = CheckReject := by
  rfl
/-- An unmap LONGER than the source is rejected: `unmap_source_vma` hands
`do_vmi_munmap` exactly `vrm->old_len` (:1082, :1122).
kernel: mm/mremap.c:move_vma,unmap_source_vma@v6.18.46 -/
theorem mremap_move_unmapping_too_much_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 8192)]
        [MemCopy.mkCopy 65536 131072 4096] []) tight_model
    = CheckReject := by
  rfl
/-- Zero-filling the WHOLE destination is rejected: its first page holds the
moved page tables (`move_page_tables` from :1208), and only the delta is
fresh.
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_move_zero_filling_the_whole_destination_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(131072, 8192)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) tight_model
    = CheckReject := by
  rfl
/-- …and so is a zero-fill of the destination's HEAD alone.
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_move_zero_filling_the_head_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(131072, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) tight_model
    = CheckReject := by
  rfl
/-- A destination whose HEAD lands on the source's tail is rejected: the
search runs while the source is live (`vrm_set_new_addr` at :1539, the
source unmapped at :1312), so `[69632, 81920)` cannot be returned against
the source `[65536, 73728)`.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_onto_the_source_tail_is_rejected :
    check_mremap_row (mremap_in 8192 12288)
      (SyscallEffect.mkEffectU 69632 [] [(77824, 4096)] [(65536, 8192)]
        [MemCopy.mkCopy 65536 69632 8192] []) two_page_roomy_model
    = CheckReject := by
  rfl
/-- …a destination whose TAIL lands on the source's head likewise…
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_under_the_source_head_is_rejected :
    check_mremap_row (mremap_in 8192 12288)
      (SyscallEffect.mkEffectU 57344 [] [(65536, 4096)] [(65536, 8192)]
        [MemCopy.mkCopy 65536 57344 8192] []) two_page_roomy_model
    = CheckReject := by
  rfl
/-- …while the destination directly ABOVE the source, touching it and
overlapping nothing, is admitted.
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_adjacent_above_a_two_page_source_accepts :
    check_mremap_row (mremap_in 8192 12288)
      (SyscallEffect.mkEffectU 73728 [] [(81920, 4096)] [(65536, 8192)]
        [MemCopy.mkCopy 65536 73728 8192] []) two_page_roomy_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(73728, 12288)] [] 0 0 16384 0 demo_sp)) [] := by
  rfl
/-- A move-shaped ledger returning the SOURCE address is rejected: `old` is
the in-place return, whose ledger has no unmap and no copy.  The checker
reads the return against `old` before it tests a move, so the move test
never sees this address; had it, `mremap_fresh_b` refuses a destination
equal to the source (`mremap_fresh_neq_old`), so the verdict does not
depend on the order — the order pinned is the spec's.
kernel: mm/mremap.c:expand_vma,expand_vma_in_place,move_vma@v6.18.46 -/
theorem mremap_move_to_the_source_itself_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 65536 4096] []) tight_model
    = CheckReject := by
  rfl
/-- -ENOMEM beside a complete move ledger is rejected: an admitted failure
cannot keep the move it performed (`move_vma` returns the errno at :1316
having unmapped the destination, not the source).
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_enomem_with_move_ledgers_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) tight_model
    = CheckReject := by
  rfl
/-- A move growing by TWO pages zero-fills a two-page tail above the one
copied page.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_by_two_accepts :
    check_mremap_row (mremap_in 4096 12288)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 8192)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) roomy_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(131072, 12288)] [] 0 0 16384 0 demo_sp)) [] := by
  rfl
/-- …and a one-page tail there is rejected.
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_move_by_two_short_tail_is_rejected :
    check_mremap_row (mremap_in 4096 12288)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) roomy_model
    = CheckReject := by
  rfl
/-- The ceiling is INCLUSIVE for the move too: a destination ending exactly
at `demo_top` is admitted under the low stack pointer (the pinned rejection
is one page higher).
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_ending_exactly_at_the_ceiling_accepts :
    check_mremap_row (mremap_at_in 65536 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 8192)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)]
        [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 8192)) 4096] [])
      move_source_lo_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 8192), 8192)] [] 0 0 8192
        (Z_to_bv 64 mmap_base_max) demo_sp)) [] := by
  rfl
/-! ## The adversarial round: equal size -/
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_efault_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect (errno_ret EFAULT) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_einval_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_eperm_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect (errno_ret EPERM) [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_returning_a4_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect 0x12345000 [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_relocated_unmodeled :
    check_mremap_row (mremap_in 8192 8192)
      (SyscallEffect.mkEffectU 0x12345000 [] [] [(65536, 8192)]
        [MemCopy.mkCopy 65536 0x12345000 8192] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_over_budget_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect 65536 [] []) over_budget_two_pages
    = CheckUnmodeled := by
  rfl
/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_lazy_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect 65536 [] []) lazy_two_pages
    = CheckUnmodeled := by
  rfl
/-- A SUBRANGE of a live entry declines even at equal size, where Linux
answers `addr` (`vma_lookup`, :1931, needs only a VMA at `addr`): the source
gate demands the exact entry.
kernel: mm/mremap.c:do_mremap,check_prep_vma@v6.18.46 -/
theorem mremap_equal_size_subrange_is_unmodeled :
    check_mremap_row (mremap_in 4096 4096) (mkEffect 65536 [] []) two_page_model
    = CheckUnmodeled := by
  rfl
/-- …and so does a range running PAST the entry's end, where Linux also
answers `addr` (:1676-1677 returns before the :1720-1721 length test).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mremap_equal_size_overlong_is_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect 65536 [] []) tight_model
    = CheckUnmodeled := by
  rfl

/-! ## The deep review's round

The deep review of this file read the checker against Rocq and Linux and
found no verdict to move; what it found was, again, decisions without a
pin — the witness's, the source gate's conjuncts taken one at a time, the
`vm_reserved` half of the move's free-range test, a copy beside an errno,
and three things the adversarial round had settled in prose.  This section
is that round's tests.  Where the adversarial round's prose asserted that
NO implementation produces a shape, the docstrings now say whose answer
each rejection is: the checker follows `mremap_spec`, and where the spec
declines Linux/qemu-user disagreements, these pins require CheckUnmodeled
for the former Linux-only answers (see `mremap_spec`, #1426). -/

/-- The witness declines exactly where the checker does: a flag word other
than `MREMAP_MAYMOVE`, a zero rounded old size, a new size rounding past
`TASK_SIZE`, and a source the ledger does not track as one mapping.
The kernel readings are the checker pins `mremap_flags_zero_is_declined`,
`mremap_old_size_zero_aligned_is_unmodeled`, `mremap_one_past_task_size_is_declined`
and `mremap_untracked_source_is_declined`.
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,do_mremap@v6.18.46 -/
theorem mremap_witness_declines_where_the_checker_declines :
    mremap_witness 65536 4096 8192 0 tight_model = Unmodeled
      ∧ mremap_witness 65536 0 8192 1 tight_model = Unmodeled
      ∧ mremap_witness 65536 4096 (Z_to_bv 64 (TASK_SIZE + 4096)) 1 tight_model = Unmodeled
      ∧ mremap_witness 131072 4096 8192 1 tight_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- This shape declines because supported implementations disagree;
see the source argument at `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_witness_misaligned_address_unmodeled :
    mremap_witness 65537 4096 8192 1 tight_model
      = Unmodeled := by
  rfl

/-- …and on a zero or wrapping new size: `PAGE_ALIGN` in `do_mremap`
(:1917-1918) leaves both at zero, which `check_mremap_params` refuses
(:1771-1772).
kernel: mm/mremap.c:do_mremap,check_mremap_params@v6.18.46 -/
theorem mremap_witness_zero_or_wrapping_new_size_unmodeled :
    mremap_witness 65536 4096 0 1 tight_model
      = Unmodeled
    ∧ mremap_witness 65536 4096 18446744073709551615 1 tight_model
      = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- This shape declines because supported implementations disagree;
see the source argument at `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_witness_equal_size_unmodeled :
    mremap_witness 65536 8192 8192 1 two_page_model
      = Unmodeled
    ∧ mremap_witness 65536 4097 8192 1 two_page_model
      = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- The witness and checker follow the spec's decline boundary (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_witness_shrink_declines_grow_is_enomem :
    mremap_witness 65536 8192 4096 1 two_page_model = Unmodeled
    ∧ mremap_witness 65536 4096 8192 1 tight_model
      = Ok (mkEffect (errno_ret ENOMEM) [] []) tight_model []
    ∧ mremap_witness 65536 4096 (Z_to_bv 64 TASK_SIZE) 1 tight_model
      = Ok (mkEffect (errno_ret ENOMEM) [] []) tight_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The witness and checker follow the spec's decline boundary (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_checker_matches_the_witness :
    check_mremap_row (mremap_in 8192 4096) (mkEffect (errno_ret ENOMEM) [] []) two_page_model
      = CheckUnmodeled
    ∧ check_mremap_row (mremap_in 4096 8192) (mkEffect (errno_ret ENOMEM) [] []) tight_model
      = CheckOk tight_model []
    ∧ check_mremap_row (mremap_in 8192 8192) (mkEffect 65536 [] []) two_page_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The source gate's `alloc_top` conjunct alone declines: a two-page
source whose end is one page above the run's grant top, at equal size,
where Linux would answer the address — `vma_lookup` (`do_mremap`, :1931)
finds the VMA wherever it is and `mremap_at` returns `addr` (:1557-1559).
The bound is the model's, kept so that a modeled source's address is never
an encoded errno (`mremap_source_ret_not_errno`); the other four conjuncts
hold on this fixture.
kernel: mm/mremap.c:do_mremap,mremap_at@v6.18.46 -/
theorem mremap_source_over_alloc_top_is_declined :
    check_mremap_row (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 8192 8192)
      (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] []) high_source_model
    = CheckUnmodeled := by
  rfl

/-- The `vm_reserved` conjunct alone declines: the image's page at 4096,
both reserved and tracked live, at equal size — Linux serves it
(`check_prep_vma` returns at :1676-1677 for a call that neither expands
nor moves, and `mremap_at` returns `addr`, :1557-1559); the model declines
because the image's bytes are not this ledger's to remap.
kernel: mm/mremap.c:check_prep_vma,mremap_at@v6.18.46 -/
theorem mremap_source_on_the_image_is_declined :
    check_mremap_row (mremap_at_in 4096 4096 4096) (mkEffect 4096 [] []) noaccess_image_overlap
    = CheckUnmodeled := by
  rfl

/-- The `vm_noaccess` conjunct alone declines: three pages tracked live and
wholly inaccessible, at equal size — no test in `check_prep_vma` reads the
protection, so Linux answers the address (:1676-1677, then `mremap_at`
:1557-1559); the model has no ledger shape for remapping a protected
range.
kernel: mm/mremap.c:check_prep_vma,mremap_at@v6.18.46 -/
theorem mremap_noaccess_source_is_declined :
    check_mremap_row (mremap_in 12288 12288) (mkEffect 65536 [] []) noaccess_three_pages
    = CheckUnmodeled := by
  rfl

/-- A move onto the image's LOAD reservation is rejected on the
`vm_reserved` half of the free-range test alone — the destination is clear
of every live mapping and the budget is met.  The segment is a live
file-backed VMA in the kernel's tree, and `vm_unmapped_area`
(mm/mmap.c:663) never returns an occupied range to `vrm_set_new_addr`
(:957).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mremap_move_onto_the_image_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 69632 [] [(73728, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 69632 4096] []) below_image_model
    = CheckReject := by
  rfl

/-- A copy beside -ENOMEM, with no zero-fill and no unmap, is rejected: a
failed `move_page_tables` is reverted (`copy_vma_and_data`, :1215-1224)
and the new VMA is what `unmap_source_vma` then removes (:1226-1228), so
no copy survives an errno return.
kernel: mm/mremap.c:move_vma,copy_vma_and_data@v6.18.46 -/
theorem mremap_enomem_with_a_copy_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [MemCopy.mkCopy 65536 131072 4096] [])
      tight_model
    = CheckReject := by
  rfl

/-- A growing move to the first page is admitted: 4096 is the floor of the
kernel's own top-down search (`generic_get_unmapped_area_topdown`,
mm/mmap.c:765, `info.low_limit = PAGE_SIZE`), and `cap_mmap_addr`
(security/commoncap.c:1459-1471) refuses only an address below
`dac_mmap_min_addr`, whose default `CONFIG_DEFAULT_MMAP_MIN_ADDR` is 4096
(mm/Kconfig:726-729) — a sysctl, not a kernel constant — so some
supported configuration hands this address back.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown; security/commoncap.c:cap_mmap_addr@v6.18.46 -/
theorem mremap_move_to_page_one_is_admitted :
    check_mremap_row (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
      (SyscallEffect.mkEffectU 4096 [] [(8192, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) 4096 4096] []) placement_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(4096, 8192)] [] 0 0 8192
        (Z_to_bv 64 mmap_base_max) demo_sp)) [] := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_answered_eintr_unmodeled :
    check_mremap_row (mremap_in 8192 4096) (mkEffect (errno_ret EINTR) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_unmap_split_in_two_unmodeled :
    check_mremap_row (mremap_in 12288 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096), (73728, 4096)] [] []) three_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_answered_eagain_unmodeled :
    check_mremap_row (mremap_in 8192 8192) (mkEffect (errno_ret EAGAIN) [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_equal_size_with_a_lone_unmap_unmodeled :
    check_mremap_row (mremap_in 8192 8192)
      (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- A move onto a gap that fits only the OLD length is rejected:
`vrm_set_new_addr` asks the search for `vrm->new_len` (:957), so the
destination must be free for both pages, and 135168 is live.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mremap_move_onto_a_half_hole_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) half_hole_model
    = CheckReject := by
  rfl

/-- Declined across the Linux/qemu-user disagreement; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_misaligned_grow_einval_unmodeled :
    check_mremap_row (mremap_misaligned_in 4096 8192) (mkEffect (errno_ret EINVAL) [] []) tight_model
    = CheckUnmodeled := by
  rfl

/-- The Prelude's `demo_top` at the two literals Rocq's
`Checks/Cases/Mm/Mremap.v` spells — the source of its
`mremap_inplace_grow_to_ceiling_accepts` (140735332474880) and of its
`mremap_inplace_grow_past_ceiling_rejected` (140735332478976) — so the
`demo_top - 8192` and `demo_top - 4096` sources above restate those cases
and not others.
model: `demo_top` against Rocq's literals, decided once. -/
theorem mremap_demo_top_offsets_are_rocqs_literals :
    demo_top - 8192 = 140735332474880 ∧ demo_top - 4096 = 140735332478976 := by
  decide

/-! The mutation sweep the review ran (159 mutants of the checker and the
witness, judged with the four twin theorems and `mremap_witness_ok`
deleted so that only the pins could refute them) left two checker mutants
alive that were not equivalent: the shrink arm accepting a zero-fill of the
tail it unmaps, and the in-place grow arm accepting an unmap of the tail it
zero-fills.  Each is one extra ledger term beside a correct one, which no
pin above offers; these two do. -/

/-- Declined because Linux and qemu-user disagree on this shape; the
old candidate answer is not accepted (see `mremap_spec`, #1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_zero_filling_the_tail_unmodeled :
    check_mremap_row (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := by
  rfl

/-- An in-place grow that also unmaps its new tail is rejected:
`expand_vma` in place (`expand_vma_in_place`, through `vma_merge_extend`
from :1470) extends the VMA by `vrm->delta` and unmaps nothing, so the
tail's zero-fill beside an unmap of the same range is not the spec's grow
term.
kernel: mm/mremap.c:expand_vma,expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_unmapping_the_tail_is_rejected :
    check_mremap_row (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(69632, 4096)] [] []) tight_model
    = CheckReject := by
  rfl

/-! Rerun over the pins above, the same sweep left four witness mutants
alive that were not equivalent, each a gate the witness could lose or
reorder while every witness pin above still held: the flag gate behind the
alignment gate, the source gate behind the equal-size return, the
backing-uniform conjunct dropped, and the old-size gate dropped — the last
distinguishable only on a ledger holding a zero-size entry at the address,
which is why `zero_entry_model` is the fixture.  A fifth, the `TASK_SIZE`
gate's left operand shifted by one, is equivalent: `page_round_up_Z` yields
multiples of `page_size` and `TASK_SIZE` is one, so the shifted comparison
agrees with the original on every input. -/

/-- The witness's gates fire in the checker's order, and each pulls its own
weight: a flag word other than `MREMAP_MAYMOVE` declines before the address
is inspected, as `check_mremap_params` tests the flag word (:1759-1760)
before `offset_in_page(addr)` (:1763-1764); and a zero rounded old size
declines on a ledger holding a zero-size entry at the address, which the
source gate would have let through (the checker's
`mremap_old_size_zero_gate_precedes_the_source_gate`).
kernel: mm/mremap.c:check_mremap_params,do_mremap@v6.18.46 -/
theorem mremap_witness_gates_fire_in_the_checkers_order :
    mremap_witness 65537 4096 8192 0 tight_model = Unmodeled
      ∧ mremap_witness 65536 0 8192 1 zero_entry_model = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- A grow needs a tracked source with uniform backing: `check_prep_vma`
validates the source before `mremap_at` expands or moves it. The tracked,
eager control differs from the mixed source only in its backing ledger.
kernel: mm/mremap.c:check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_witness_grow_needs_a_uniform_tracked_source :
    mremap_witness 131072 4096 8192 1 tight_model = Unmodeled
      ∧ mremap_witness 65536 8192 12288 1 mixed_backing = Unmodeled
      ∧ mremap_witness 65536 12288 16384 1 noaccess_three_pages = Unmodeled
      ∧ mremap_witness 4096 4096 8192 1 noaccess_image_overlap = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Tracked eager sources let the witness choose the charge refusal Linux
can return before expanding or moving in `check_prep_vma`.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mremap_witness_clean_source_grows_are_modeled :
    mremap_witness 131072 4096 8192 1
        (fixture (VmMaps.mkVmMapsFull [] [(131072, 4096)] [] 0 0 8192 0 demo_sp)) ≠ Unmodeled
      ∧ mremap_witness 65536 8192 12288 1 two_page_model ≠ Unmodeled
      ∧ mremap_witness 65536 12288 16384 1
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 16384 0 demo_sp)) ≠ Unmodeled
      ∧ mremap_witness 4096 4096 8192 1
        (fixture (VmMaps.mkVmMapsFull [] [(4096, 4096)] [] 0 0 16384 0 demo_sp)) ≠ Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> cases h

-- lean-port sentinel: ticket V-Mm-Mremap appends below this line

section V_Mm_Mremap

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## V-Mm-Mremap — `mremap` over the real table

The direct checker pins isolate its argument and effect handling. These
pins also exercise lookup at 216. A declined shape alone cannot distinguish
that lookup from a missing arm, and a refusal can survive a register swap.
The accepted in-place grow and move down from the ceiling supply that
missing distinction: transposing the sizes declines the grow, and the
ceiling move names a source other than the default 65536. The retained
shrink pins now assert decline. `arm_mremap_is_the_row` separately ties
the registered arm's acceptor to `check_mremap_row`.

POLARITY is the sections' above: every pin about the kernel's answer
carries a `kernel:` line, `CheckOk`, `CheckReject` and `CheckUnmodeled`
alike, and a pin about the table's own contents carries `model:`. -/

/-- The lookup the dispatcher performs at 216: `checked_table` finds
`arm_mremap` there.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_mremap : lookup_ca checked_table 216 = some arm_mremap :=
  lookup_ca_checked_table_mremap

/-- The arm's acceptor is `check_mremap_row` on every input, effect and
model, so each checker-level pin above is a verdict of `check_syscall` at
216 as well: the arm reads `a0`-`a3` in order, as `check_mremap_row` does.
model: `arm_mremap`'s `ca_check` against this file's application of the
checker; the arm's own contents, not a kernel claim. -/
theorem arm_mremap_is_the_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_mremap.ca_check i eff m = check_mremap_row i eff m := rfl

/-! ### The twelve Rocq `= CheckReject` examples, through `check_syscall` -/

/-- `mremap_grow_beyond_budget_rejected` over the real table: a grow past
the budget is refused by `may_expand_vm` (mm/mmap.c:1324-1347) from
`check_prep_vma` (mm/mremap.c:1742-1743, Linux v6.18.46).
kernel: mm/mremap.c:check_prep_vma; mm/mmap.c:may_expand_vm@v6.18.46 -/
theorem mremap_grow_beyond_budget_rejected_over_the_real_table :
    check_syscall (mremap_in 4096 8192)
      (mkEffect 65536 [] [(69632, 4096)]) budget_full_model
    = CheckReject := rfl

/-- `mremap_move_to_occupied_range_rejected` over the real table: the
destination search runs over the live VMAs (`vrm_set_new_addr`,
mm/mremap.c:957-960; `vm_unmapped_area`, mm/mmap.c:663, Linux v6.18.46)
and never returns an occupied range.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mremap_move_to_occupied_range_rejected_over_the_real_table :
    check_syscall (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
        [MemCopy.mkCopy 65536 131072 4096] []) occupied_model
    = CheckReject := rfl

/-- Equal sizes decline across implementations: Linux keeps the mapping
in place (`mremap_at`, mm/mremap.c, v6.18.46), while QEMU 11.1.1
linux-user/mmap.c `target_mremap`:1194-1209 may relocate or fail ENOMEM.
kernel: mm/mremap.c:mremap_at,check_prep_vma@v6.18.46 -/
theorem mremap_equal_size_enomem_unmodeled_over_the_real_table :
    check_syscall (mremap_in 8192 8192)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := rfl

/-- `mremap_inplace_grow_into_neighbour_rejected` over the real table: a
live neighbour directly above the source is seen by `vma_expandable`
(mm/mremap.c:1421-1422, Linux v6.18.46).
kernel: mm/mremap.c:vma_expandable,vrm_can_expand_in_place@v6.18.46 -/
theorem mremap_inplace_grow_into_neighbour_rejected_over_the_real_table :
    check_syscall (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) crowded_model
    = CheckReject := rfl

/-- `mremap_inplace_grow_into_image_rejected` over the real table: the
image's reservation is a VMA the same test walks (`vma_expandable`,
mm/mremap.c, Linux v6.18.46).
kernel: mm/mremap.c:vma_expandable@v6.18.46 -/
theorem mremap_inplace_grow_into_image_rejected_over_the_real_table :
    check_syscall (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) below_image_model
    = CheckReject := rfl

/-- `mremap_inplace_grow_past_ceiling_rejected` over the real table: the
refusal is the model's `alloc_top` bound, read from the ledger's entry
`sp`; the argument that a modeled trace never asks is beside the
spec-level `inplace_grow_past_ceiling_rejected`.
kernel: mm/mremap.c:vma_expandable; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem mremap_inplace_grow_past_ceiling_rejected_over_the_real_table :
    check_syscall (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) []
        [(Z_to_bv 64 demo_top, 4096)] [] [] []) grow_past_ceiling_model
    = CheckReject := rfl

/-- `mremap_wrapping_new_size_success_unmodeled` over the real table: a
new size in the top partial page of the word page-aligns to 0
(`do_mremap`, mm/mremap.c:1918, Linux v6.18.46) and `!new_len`
(:1771-1772) answers -EINVAL; QEMU 11.1.1 linux-user/mmap.c
`target_mremap`:1194-1209 can fail allocation first. The model declines
the input before inspecting this candidate success.
kernel: mm/mremap.c:do_mremap,check_mremap_params@v6.18.46 -/
theorem mremap_wrapping_new_size_success_unmodeled_over_the_real_table :
    check_syscall (mremap_in 8192 18446744073709551615)
      (mkEffect 65536 [] []) two_page_model
    = CheckUnmodeled := rfl

/-- Rocq's `mremap_top_aligned_new_size_einval_rejected`, whose verdict is
not kept: a page-aligned new size in the top page of the word is above
`TASK_SIZE`, and the arm DECLINES the -EINVAL that Linux v6.18.46's
`check_mremap_params` (mm/mremap.c:1775-1776) answers, because Linux
v6.12's `MREMAP_MAYMOVE` grow path answered -ENOMEM and the spec twin
admits neither; the argument is the spec twin's header.  These two are
the verdicts `testing/syscall-check/tests/mremap_shapes.c`'s two
`wrapnew` CASE lines meet, which the replay reads as fail-closed.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_top_aligned_new_size_einval_is_declined_over_the_real_table :
    check_syscall (mremap_in 8192 18446744073709547520)
      (mkEffect (errno_ret EINVAL) [] []) two_page_model
    = CheckUnmodeled := rfl

/-- …and Rocq's `mremap_top_aligned_new_size_is_enomem`, the -ENOMEM
beside it, declined on the same argument.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem mremap_top_aligned_new_size_enomem_is_declined_over_the_real_table :
    check_syscall (mremap_in 8192 18446744073709547520)
      (mkEffect (errno_ret ENOMEM) [] []) two_page_model
    = CheckUnmodeled := rfl

/-- `mremap_move_onto_brk_orphan_page_rejected` over the real table: the
destination `[65536, 73728)` crosses the residual brk entry, which the
search over the live VMAs (`vrm_set_new_addr`, mm/mremap.c:957-960;
`vm_unmapped_area`, mm/mmap.c:663, Linux v6.18.46) never returns.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem mremap_move_onto_brk_orphan_page_rejected_over_the_real_table :
    check_syscall mremap_orphan_in
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
        [MemCopy.mkCopy 131072 65536 4096] []) m_brk_orphan_with_source
    = CheckReject := rfl

/-- `mremap_move_unaligned_destination_rejected` over the real table:
`__get_unmapped_area` answers -EINVAL to an unaligned address
(mm/mmap.c:859-860, Linux v6.18.46), so the search never returns one.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem mremap_move_unaligned_destination_rejected_over_the_real_table :
    check_syscall (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 0x80000001) []
        [(Z_to_bv 64 0x80001001, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000001) 4096] [])
      placement_model
    = CheckReject := rfl

/-- `mremap_move_onto_source_rejected` over the real table: Linux runs the
search while the source VMA is still live (`vrm_set_new_addr` from
`expand_vma`, mm/mremap.c:1539, the source unmapped only by `move_vma` at
:1312, Linux v6.18.46), so the destination cannot overlap it.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_onto_source_rejected_over_the_real_table :
    check_syscall (mremap_placed_in mremap_src 4096 8192)
      (SyscallEffect.mkEffectU mremap_overlapping_dst [] [(mremap_src, 4096)] [(mremap_src, 4096)]
        [MemCopy.mkCopy mremap_src mremap_overlapping_dst 4096] []) placement_model
    = CheckReject := rfl

/-- `mremap_move_past_demo_top_rejected_under_low_sp` over the real table:
the model's bound, read from the ledger's entry `sp`; the argument that
it is the model's and not the kernel's is beside the checker-level twin
and the spec-level `move_past_demo_top_rejected_under_low_sp`.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem mremap_move_past_demo_top_rejected_under_low_sp_over_the_real_table :
    check_syscall (mremap_at_in 65536 4096 8192)
      (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
        [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
      move_source_lo_model
    = CheckReject := rfl

/-! ### Dispatcher pins that name the registers -/

/-- The witness and checker follow the spec's decline boundary (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem mremap_shrink_inplace_unmodeled_over_the_real_table :
    check_syscall (mremap_in 8192 4096)
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := rfl

/-- `mremap_inplace_grow_accepts` over the real table: `expand_vma_in_place`
extends the VMA (mm/mremap.c:1470, Linux v6.18.46) and the new page reads
as zeroes.
kernel: mm/mremap.c:expand_vma,vrm_can_expand_in_place,expand_vma_in_place@v6.18.46 -/
theorem mremap_inplace_grow_accepts_over_the_real_table :
    check_syscall (mremap_in 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) tight_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) [] := rfl

/-- `mremap_move_down_from_ceiling_accepts` over the real table: the
source is `demo_top - 4096`, not `mremap_in`'s 65536.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem mremap_move_down_from_ceiling_accepts_over_the_real_table :
    check_syscall (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 4096 8192)
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(Z_to_bv 64 (demo_top - 4096), 4096)]
        [MemCopy.mkCopy (Z_to_bv 64 (demo_top - 4096)) 65536 4096] []) grow_past_ceiling_model
    = CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) [] := rfl

/-- The shrink above with its two sizes transposed, which is what an arm
reading the old size from `a2` and the new one from `a1` would hand the
checker: it declines, since the source gate asks the ledger for a
one-page mapping at 65536 and the one there is two pages.
model: `check_mremap`'s source gate on a closed model; the checker's own
answer to a call no arm makes, not a kernel claim. -/
theorem mremap_shrink_transposed_is_declined :
    Checks.Sys.Mm.Mremap.check_mremap 65536 4096 8192 1
      (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model
    = CheckUnmodeled := rfl

/-- The grow in place above with its two sizes transposed: the checker
declines, since the source gate asks the ledger for a two-page mapping at
65536 and the one there is one page.
model: `check_mremap`'s source gate on a closed model; the checker's own
answer to a call no arm makes, not a kernel claim. -/
theorem mremap_inplace_grow_transposed_is_declined :
    Checks.Sys.Mm.Mremap.check_mremap 65536 8192 4096 1
      (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) tight_model
    = CheckUnmodeled := rfl

end V_Mm_Mremap

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mremap
