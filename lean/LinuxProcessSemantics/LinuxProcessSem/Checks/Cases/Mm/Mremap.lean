import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Mm.Mremap — what `mremap` admits, read off against Linux

Worked examples over `Sys.Mm.Mremap.mremap_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Mm/Mremap.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f)
throughout, in `mm/mremap.c` unless another file is named.

HOW THESE ARE STATED.  Where a grow may MOVE the admitted set is infinite, and the `iff` keeps the
spec's own placement guard, `mremap_fresh_b`, as the condition on the
destination; `fresh_b_conjuncts` pins what that guard is, and the concrete
admissions and refusals decide it at one destination each.  Each decision
gets its `iff`, closed by `sys_norm`, and a refutation of the answer a
lying kernel would give, closed by `sys_refute`.  The argument gates hold
for EVERY model, so their pins quantify over `m` rather than name a
fixture.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree.

ROCQ COVERAGE.  Every Rocq example and lemma of that file has a same-named
twin here, or one under a name whose docstring says which Rocq case it is;
most drop the `mremap_` prefix the Rocq names carry, since the namespace
says it.  The eight cases about `Run.apply_effect` — `mremap_copy_reads_pre_effect_snapshot`,
the four `apply_effect_*` orderings and the three `mremap_snapshot_*`
fixtures they read — are twinned in the last section against the Lean
`Run.apply_effect` (`Run.lean`), which Rocq's `Checks/Cases/Mm/Mremap.v`
imports through `Run` and this file reaches through the Prelude.
`mremap_move_dst_eq_old_is_refused_before_region_free` is documentary in
Rocq (a `reflexivity` on a ground term, kept for what it explains); its twin
is `dst_eq_old_refused_before_region_free`.  Three Rocq INPUT fixtures have
no twin: `mremap_at_in`, `mremap_placed_in` and `mremap_orphan_in` build the
`SyscallInput` that Rocq's checker-level statements take, while the pins
here are stated on `mremap_spec` over a symbolic input `i`.  `mremap_in`
stays because the dispatcher pins use its grow shape: an accepted grow
can distinguish routing to mremap from a missing arm's decline. The
misaligned fixture is no longer needed by those dispatcher pins.
Nothing reads this paragraph mechanically yet; the Cases coverage ledger
(ticket T9) will. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mremap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register

What `Checks/Cases/Tactic.lean` says a spec owes the `sys_simp` set: its
unfolding, its errno list's, and its post-state and effect builders', at
low priority.  The `*_b` gates are decided, never unfolded, so they are
not registered.  `Sys/Mm/Mremap.v` is the only Rocq spec that builds a
`MemCopy`, so the copy record's injectivity is registered here, at the
default priority the constructor injectivities in `Tactic.lean`'s pass list
have; when a second copy-bearing spec is ported, the line moves into that
list (a `lean: base:` change) and this one goes.  The lines live here
rather than in that register on purpose: a port PR creates its own files
and edits no shared one (docs/merge-commutativity.md). -/

attribute [sys_simp low]
  mremap_spec.eq_1 mremap_errnos.eq_1 mremap_model_next.eq_1 mremap_maps_next.eq_1
  mremap_inplace_effect.eq_1 mremap_move_effect.eq_1 mremap_tail.eq_1
attribute [sys_simp] MemCopy.mkCopy.injEq

/-! ## The flags and errnos these checks spell out -/

/-- The one modeled flags word.
kernel: include/uapi/linux/mman.h:MREMAP_MAYMOVE@v6.18.46 -/
example : MREMAP_MAYMOVE = 1 := by decide
/-- The one injectable errno.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM@v6.18.46 -/
example : mremap_errnos = [ENOMEM] := by decide
/-- The page-table depth the tree pins is Sv48, whose `TASK_SIZE` is `2^47`
(`TASK_SIZE_64 = PGDIR_SIZE * PTRS_PER_PGD / 2`,
arch/riscv/include/asm/pgtable.h:1081, Linux v6.18.46, taken by `TASK_SIZE`
at :1088);
the spec's declared decline compares against it.
model: the model's own constant at a numeral; the kernel reading is in the prose above and on `State.TASK_SIZE`. -/
example : TASK_SIZE = 140737488355328 := by decide

/-! ## Inputs and fixtures

Rocq builds each model as `with_vmmaps <ledger> (init_model … demo_sp …)`;
here they are `fixture` of a literal ledger, the Prelude's normal form, and
the lazily backed ones are `with_vm_backing` over such a fixture.  Names
keep Rocq's, without the `mremap_` prefix where the namespace already says
it. -/

/-- The mremap input for `old_size` and `new_size` at 65536 with
`MREMAP_MAYMOVE`.  a4 is deliberately nonzero: Linux reads `new_addr` only
under `MREMAP_FIXED`/`MREMAP_DONTUNMAP` — `check_mremap_params` returns
before its `new_addr` tests (:1779-1780) and `check_prep_vma` overwrites
the field with `addr` when no new address is implied (:1672-1673). -/
def mremap_in (old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [65536, old_size, new_size, 1, 0x12345000, 0] (fun _ => none) (fun _ => none)

/-- Two live rw pages at 65536 under a two-page budget.  Given one page back
it is the Prelude's `tight_model`, which the shrink pins name for the
post-state and the one-page pins for the source (Rocq's `mremap_shrunk_model`
and `mremap_one_page_model` are that one ledger under two names). -/
def two_page_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)

/-- Three live rw pages at 65536 under a three-page budget: a shrink to one
page drops a TWO-page tail, whose length is not the new length. -/
def three_page_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 12288 0 demo_sp)

/-- One live page at 65536 under a four-page budget: room to grow by two
pages, in place or moved, so the delta is not the old length either. -/
def roomy_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 16384 0 demo_sp)

/-- Two live pages at 65536 under a ONE-page budget: a ledger already over
its limit, on which nothing but a grow may be a budget refusal. -/
def over_budget_two_pages : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 4096 0 demo_sp)

/-- One live page under a budget of exactly that page. -/
def budget_full_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 4096 0 demo_sp)

/-- One live page at 65536 and two at 131072, under a four-page budget. -/
def occupied_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (131072, 8192)] [] 0 0 16384 0 demo_sp)

/-- Two adjacent live pages: an in-place grow of the first runs into the
second. -/
def crowded_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 0 0 16384 0 demo_sp)

/-- One live page immediately below a LOAD reservation. -/
def below_image_model : Model :=
  fixture (VmMaps.mkVmMapsFull [(69632, 4096)] [(65536, 4096)] [] 0 0 8192 0 demo_sp)

/-- One live page two pages below the run's grant top: growing it by a
page ends exactly AT the top. -/
def grow_to_ceiling_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 8192), 4096)] [] 0 0 8192 0 demo_sp)

/-- One live page one page below the top: growing it by a page crosses it. -/
def grow_past_ceiling_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] [] 0 0 8192 0 demo_sp)

/-- A ledger entry of size ZERO at 65536: nothing a run can produce, since
`VmMaps` carries no well-formedness predicate it is writable by hand, and
it is what the clone gate's position is pinned against. -/
def zero_entry_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 0)] [] 0 0 8192 0 demo_sp)

/-- Two lazily reserved pages, both touched, under a two-page budget. -/
def lazy_two_pages : Model :=
  with_vm_backing [(65536, 8192)] [65536, 69632]
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp))

/-- One lazily reserved page, touched, under a one-page budget. -/
def lazy_one_page : Model :=
  with_vm_backing [(65536, 4096)] [65536]
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 4096 0 demo_sp))

/-- A two-page mapping of which only the first page is lazy: a MAP_FIXED
inside it split the provenance without splitting `vm_maps`. -/
def mixed_backing : Model :=
  with_vm_backing [(65536, 4096)] []
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp))

/-! ## The placement guard's two unsatisfiable readings

Two `iff` pins below say a grow is forced to -ENOMEM because no destination
satisfies `mremap_fresh_b`.  These are the halves that argument rests on,
each read off the guard's conjuncts: the ceiling conjunct with a request
the width of the address space, and the budget conjunct with a budget the
source has spent. -/

/-- No destination fits a `TASK_SIZE` request below the grant top: the
ceiling conjunct needs `dst + 2^47 ≤ demo_top`, and `demo_top` is below
`2^47`.
The kernel fact it rests on: the search bounds a destination by `TASK_SIZE` (`__get_unmapped_area`, mm/mmap.c:857-858) and the run's grant top sits below it, so no destination of that width exists.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem no_room_for_task_size_move (dst : word) :
    mremap_fresh_b one_map_model 4096 140737488355328 65536 4096 dst
      (Z_to_bv 64 140737488355328) ≠ true := by
  intro h
  have hd : 0 ≤ bv_unsigned dst := Int.natCast_nonneg _
  have htop : alloc_top (m_vmmaps one_map_model) = demo_top := by decide
  simp only [mremap_fresh_b, Bool.and_eq_true, decide_eq_true_eq, htop] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hle⟩, -⟩, -⟩ := h
  simp only [demo_top, sp_window_lo, stack_max_size] at hle
  omega

/-- No destination fits a two-page mapping under a one-page budget: the
budget conjunct charges the re-created mapping whole, at any destination.
The kernel fact it rests on: the move's commit charge is the delta (`vrm_calc_charge`, :986, refused at `move_vma` :1281-1282), which a spent budget cannot take at any destination.
kernel: mm/mremap.c:vrm_calc_charge,move_vma@v6.18.46 -/
theorem no_room_over_budget (dst : word) :
    mremap_fresh_b budget_full_model 4096 8192 65536 4096 dst 8192 ≠ true := by
  intro h
  simp only [mremap_fresh_b, Bool.and_eq_true] at h
  obtain ⟨-, hb⟩ := h
  revert hb
  simp only [mremap_final_budget_b, mremap_model_next, mremap_source_lazy_b, mremap_maps_next,
    vm_resize_backing, vm_backing_within_limit, vm_backing_used, vm_backed_maps, budget_full_model]
  sys_simp_pass +ground +decide
  -- the ground pass leaves the empty-list cuts and filter, which carry
  -- the free destination in their bounds; the nil equations remove them
  simp only [maps_subtract, maps_subtract_all, List.filter_nil, live_bytes, List.length_nil]
  decide

/-! ## The argument gates, for every model

`do_mremap` rounds both lengths (:1917-1918) and runs `check_mremap_params`
(:1752-1820) before it takes the lock (:1924) or looks up a VMA (:1931),
so what these gates answer is independent of the address space, and the
pins say so by quantifying over `m`. -/

/-- `flags = 0` declines: Linux serves it on the MAYMOVE path up to the
move — no test before `expand_vma`'s `MREMAP_MAYMOVE` read at :1535-1536
distinguishes 0 from MAYMOVE (the earlier reads of `vrm->flags`, at :1759,
:1779, :1672-1676, :1696, :1928 and :1937, test only the mask, FIXED and
DONTUNMAP) — so the answer is real, and declining it is the narrowing the
spec announces, not a claim that Linux fails.
kernel: mm/mremap.c:check_mremap_params,expand_vma@v6.18.46 -/
theorem flags_zero_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …so the success Linux really answers a `flags = 0` shrink with is not
claimed either: nothing is, on that call.
kernel: mm/mremap.c:mremap_at@v6.18.46 -/
theorem flags_zero_shrink_success_not_claimed (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 4096 0 i m
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) m' evs) := by
  sys_refute

/-- `MREMAP_FIXED` (2) declines, with or without MAYMOVE.  Linux answers
-EINVAL to FIXED without MAYMOVE (`check_mremap_params`, :1791-1792) and
serves FIXED|MAYMOVE through `mremap_to` (:1363-1413), which destroys the
destination before the move; the model has no shape for either.
kernel: include/uapi/linux/mman.h:MREMAP_FIXED; mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem fixed_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 2 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …and FIXED with MAYMOVE beside it, the shape `mremap_to` serves
(:1363-1413), declines the same way.
kernel: mm/mremap.c:do_mremap,mremap_to@v6.18.46 -/
theorem fixed_maymove_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 3 i m o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem dontunmap_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 4 i m o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem dontunmap_maymove_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 5 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A flag bit outside the three declines too.  Linux answers a
deterministic -EINVAL (`check_mremap_params`, :1759-1760), and the decline
is the narrowing the spec announces; the -EINVAL is not claimed.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem unknown_flag_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 8 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The -EINVAL Linux answers the unknown bit with is not claimed: nothing
is, on that call.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem unknown_flag_einval_not_claimed (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 8 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The one read
that precedes both, `untagged_addr(addr)` in the syscall body (:1980), can
change no answer (the `mremap_spec` docstring).
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem flags_precede_alignment (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65537 4096 8192 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …and the alignment -EINVAL is not claimed under `flags = 0` either.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem flags_precede_alignment_einval_not_claimed (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ mremap_spec 65537 4096 8192 0 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem unaligned_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65537 4096 8192 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A success at a misaligned address is rejected: `check_mremap_params`
refuses the address (:1763-1764) before any VMA is read.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem unaligned_success_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65537 4096 8192 1 i m (Ok (mkEffect 65537 [] [(69633, 4096)]) m' evs) := by
  sys_refute

/-- …and so is -EFAULT there: the VMA lookup that could answer it
(`do_mremap`, :1931) sits behind the alignment test.
kernel: mm/mremap.c:check_mremap_params,do_mremap@v6.18.46 -/
theorem unaligned_efault_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65537 4096 8192 1 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem misaligned_old_size_zero_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65537 0 4096 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem old_size_zero_misaligned_is_unmodeled (i : SyscallInput) (m : Model) :
    mremap_spec 65537 0 4096 1 i m Unmodeled := by
  sys_norm

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem new_size_zero_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 0 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A success for a zero new length is rejected (:1771-1772).
no-row: this pin fixes address 65536, and no supported implementation answers a zero new length with success.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem new_size_zero_success_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 0 1 i m (Ok (mkEffect 65536 [] []) m' evs) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem wrapping_new_size_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 (Z_to_bv 64 (two_pow_64 - 1)) 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- A success on the wrapped length is rejected: the rounded length is zero
(:1918) and refused (:1771-1772).
kernel: mm/mremap.c:do_mremap,check_mremap_params@v6.18.46 -/
theorem wrapping_new_size_success_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 (Z_to_bv 64 (two_pow_64 - 1)) 1 i m
        (Ok (mkEffect 65536 [] []) m' evs) := by
  sys_refute

/-- kernel: mm/mremap.c:do_mremap,check_mremap_params@v6.18.46 -/
theorem wrapping_new_size_enomem_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 (Z_to_bv 64 (two_pow_64 - 1)) 1 i m
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem both_sizes_zero_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 0 0 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- This shape declines because supported implementations disagree;
see the source argument at `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem both_sizes_zero_declines (i : SyscallInput) (m : Model) :
    mremap_spec 65536 0 0 1 i m Unmodeled := by
  sys_norm

/-! ### The declared decline: a new length above `TASK_SIZE`

`check_mremap_params` answers -EINVAL to a rounded `new_len` above
`TASK_SIZE` on every path (:1775-1776, Linux v6.18.46), before the lock.
At Linux v6.12 the test sat inside `mremap_to`, which only the FIXED and
DONTUNMAP shapes reached, and a MAYMOVE grow of that size was answered
-ENOMEM — by the RLIMIT_AS test of `may_expand_vm` (mm/mmap.c, Linux v6.12),
run first from the v6.12 `vma_to_resize`, or, past it, by the syscall body's
placement search (mm/mremap.c:1170, Linux v6.12), whose `__get_unmapped_area`
(mm/mmap.c, Linux v6.12) refuses a length above TASK_SIZE.
Two supported kernels disagree, so the intersection is empty and the spec
declines: neither answer is claimed. -/

/-- A page-aligned new size in the top page of the word is above
`TASK_SIZE`: declined.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem top_aligned_new_size_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 (Z_to_bv 64 (two_pow_64 - 4096)) 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- Neither kernel's answer is claimed: not the -ENOMEM of Linux v6.12…
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem top_aligned_new_size_enomem_not_claimed (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 (Z_to_bv 64 (two_pow_64 - 4096)) 1 i m
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- …nor the -EINVAL of v6.18.46 (:1775-1776), which v6.12 never answers.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem top_aligned_new_size_einval_not_claimed (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 (Z_to_bv 64 (two_pow_64 - 4096)) 1 i m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- One page above `TASK_SIZE` is declined for every model: the test is
decided before the address space is read.
kernel: mm/mremap.c:check_mremap_params@v6.18.46 -/
theorem above_task_size_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 (Z_to_bv 64 (140737488355328 + 4096)) 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- This request leaves the modeled surface; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem unaligned_above_task_size_unmodeled_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65537 4096 (Z_to_bv 64 (140737488355328 + 4096)) 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- This request leaves the modeled surface; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem unaligned_above_task_size_declines (i : SyscallInput) (m : Model) :
    mremap_spec 65537 4096 (Z_to_bv 64 (140737488355328 + 4096)) 1 i m Unmodeled := by
  sys_norm

/-- THE BOUNDARY IS STRICT: `new_len > TASK_SIZE`, so a new length of
exactly `TASK_SIZE` passes the gate (:1775-1776) and goes on to the
address space, where both kernels answer -ENOMEM — the grow cannot be
placed anywhere: not in place, because the 2^47 bytes above the source
meet a VMA (the stack, the vDSO) in any real process (`vma_expandable`'s
`find_vma_intersection`, :1421-1422), and not moved, because the search
`vrm_set_new_addr` asks (:957-960) refuses a length the width of the
address space at once (`len > mmap_end - mmap_min_addr`,
`generic_get_unmapped_area_topdown`, mm/mmap.c:747-748).  Here only the
environment's -ENOMEM is admitted: no destination satisfies the placement
guard, which `no_room_for_task_size_move` pins.
no-row: `one_map_model` fixes address 65536 while recorded rows use runtime addresses, and no probe asks for a new length of exactly TASK_SIZE.
kernel: mm/mremap.c:check_mremap_params,expand_vma,vma_expandable,vrm_set_new_addr; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem exactly_task_size_is_enomem (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 (Z_to_bv 64 140737488355328) 1 i one_map_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_map_model [] := by
  sys_norm
  constructor
  · rintro (h | ⟨dst, -, hg⟩)
    · exact h
    · exact absurd hg (no_room_for_task_size_move dst)
  · exact Or.inl

/-! ### The clone shape and the wrapping old size

A rounded old length of zero is Linux's "duplicate a mapping" request,
refused with -EINVAL for a private mapping in `check_prep_vma`
(:1690-1694) — after the VMA lookup (:1931), the seal check (:1662-1663)
and only when the call would map something new (:1676-1677).  -/

/-- A zero old size declines, for every model.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem old_size_zero_aligned_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 0 4096 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The -EINVAL Linux answers a private duplicate with (:1690-1694) is not
claimed: whether a VMA sits at the address is not something the ledger can
settle short of an exact entry.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem old_size_zero_einval_not_claimed (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 0 4096 1 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A ledger entry of size ZERO passes the source gate at a zero old
length: with the clone gate deleted, control would reach `mremap_source_b`
and ACCEPT a hand-built zero-size entry.
The gate stands for `vma_lookup` (`do_mremap`, :1931) and `check_prep_vma`'s refusals; the counterfactual measures the clone gate's position against it.
kernel: mm/mremap.c:do_mremap,check_prep_vma@v6.18.46 -/
theorem zero_entry_passes_the_source_gate :
    mremap_source_b (m_vmmaps zero_entry_model) 65536 0 0 = true := by decide

/-- …and the answer is still a decline on that ledger, so the flip is
attributable to the clone gate alone (Rocq's
`mremap_old_size_zero_gate_precedes_the_source_gate`).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem old_size_zero_gate_precedes_the_source_gate (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 0 4096 1 i zero_entry_model o ↔ o = Unmodeled := by
  sys_norm

/-- An old size in the top partial page rounds past the word.
model: page rounding at the all-ones length, decided once; the kernel claim is `wrapping_old_size_is_unmodeled`. -/
theorem wrapping_old_size_rounds_past_the_word :
    two_pow_64 ≤ page_round_up_Z (bv_unsigned (Z_to_bv 64 (two_pow_64 - 1))) := by decide

/-- A wrapping old size cannot pass the source gate whatever the ledger:
its `alloc_top` conjunct needs `old + old_nZ ≤ alloc_top`, and `alloc_top`
is below `2^64`.  So the wrap half of the clone gate is redundant, and
this is its honest pin (the Rocq lemma of the same name).
rocq-twin: mremap_wrapping_old_size_cannot_pass_the_source_gate -/
theorem wrapping_old_size_cannot_pass_the_source_gate (h : VmMaps) (old old_n : word)
    (old_nZ : Int) (hwrap : two_pow_64 ≤ old_nZ) :
    mremap_source_b h old old_n old_nZ = false := by
  have htop := alloc_top_lt h
  have hold : 0 ≤ bv_unsigned old := Int.natCast_nonneg _
  have hno : ¬ (bv_unsigned old + old_nZ ≤ alloc_top h) := by omega
  simp only [mremap_source_b, decide_eq_false hno, Bool.false_and]

/-- …and the call declines (Rocq's `mremap_wrapping_old_size_is_unmodeled`).
kernel: mm/mremap.c:do_mremap,check_prep_vma@v6.18.46 -/
theorem wrapping_old_size_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    mremap_spec 65536 (Z_to_bv 64 (two_pow_64 - 1)) 4096 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-! ## Sources the ledger cannot answer for

`vma_lookup` (:1931) needs only a VMA at `addr`; the model needs an EXACT
tracked entry, clear of the image and of every protected range
(`mremap_source_b`) with uniform backing (`mremap_backing_uniform_b`).
Each shortfall declines, the safe direction. -/

/-- kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem subrange_source_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 4096 1 i two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- The `addr` Linux really answers there is not claimed: nothing is, on
that call.
kernel: mm/mremap.c:mremap_at@v6.18.46 -/
theorem subrange_source_success_not_claimed (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 4096 1 i two_page_model (Ok (mkEffect 65536 [] []) m' evs) := by
  sys_refute

/-- kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem overlong_source_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 12288 12288 1 i two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- The -EFAULT a grow past the VMA's end gets (:1720-1721) is not claimed
either.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem overlong_source_grow_efault_not_claimed (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 12288 16384 1 i two_page_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and the grow declines outright — no -ENOMEM and no move is admitted on
a source the ledger cannot vouch for, so the source gate is read on the
grow path exactly as on the others.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem overlong_source_grow_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 12288 16384 1 i two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- No mapping at the address declines rather than answer the -EFAULT of
`check_prep_vma` (:1658-1659): the ledger is not a complete picture of the
address space (the stack has no entry), so that errno would be a guess.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem unmapped_source_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 131072 4096 4096 1 i two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- The -EFAULT (:1658-1659) is not claimed: the ledger's hole may be the
kernel's stack.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem unmapped_source_efault_not_claimed (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 131072 4096 4096 1 i two_page_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A PROT_NONE source declines: Linux moves and resizes a protected
mapping like any other (no test in `check_prep_vma` reads the
protection), but the model has no ledger shape for remapping a protected
range.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem noaccess_source_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 12288 16384 1 i noaccess_three_pages o ↔ o = Unmodeled := by
  sys_norm

/-- The image's pages decline even on a ledger that also lists them live —
the `vm_reserved` conjunct — since the image bytes are not this ledger's.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem image_source_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 4096 4096 8192 1 i noaccess_image_overlap o ↔ o = Unmodeled := by
  sys_norm

/-- A tracked entry that runs past the grant top: no run produces one, since
every grant is placed below `alloc_top`, but the ledger admits the literal. -/
def high_source_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 16384 0 demo_sp)

/-- Such a source declines even at equal size — the `alloc_top` conjunct of
`mremap_source_b`, which Linux has no counterpart for (`vma_lookup` finds
the VMA wherever it is) and which the Rocq `mremap_source_ret_not_errno`
needs so that a successful in-place return is never an encoded errno.
kernel: mm/mremap.c:do_mremap,check_prep_vma,mremap_at@v6.18.46 -/
theorem source_over_alloc_top_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec (Z_to_bv 64 (demo_top - 4096)) 8192 8192 1 i high_source_model o ↔ o = Unmodeled := by
  sys_norm

/-- A source whose backing is MIXED — one lazy page under a two-page
entry — declines: which provenance a grown tail inherits is not something
the ledger can say (Rocq's `mremap_mixed_backing_fails_closed`).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mixed_backing_fails_closed (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 12288 1 i mixed_backing o ↔ o = Unmodeled := by
  sys_norm

/-- Mixed provenance cannot determine which backing a grown tail inherits.
no-row: `mixed_backing` fixes address 65536; recorded grows use runtime addresses.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem mixed_backing_grow_not_claimed (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 12288 1 i mixed_backing
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- Removing only the protected-source ledger entry permits a grow; Linux's
`check_prep_vma` can refuse it through `may_expand_vm` (:1742-1743) before
expanding or moving.
no-row: the fixture fixes address 65536; recorded grows use runtime addresses.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem noaccess_source_clean_grow_is_modeled (i : SyscallInput) :
    mremap_spec 65536 12288 16384 1 i
      (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 16384 0 demo_sp))
      (Ok (mkEffect (errno_ret ENOMEM) [] [])
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- Removing only the image reservation permits the same grow; `may_expand_vm`
(:1742-1743) can refuse it before either placement path is taken.
no-row: the fixture fixes source address 4096; recorded grows remap runtime-placed mappings, never that address.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem image_source_clean_grow_is_modeled (i : SyscallInput) :
    mremap_spec 4096 4096 8192 1 i
      (fixture (VmMaps.mkVmMapsFull [] [(4096, 4096)] [] 0 0 16384 0 demo_sp))
      (Ok (mkEffect (errno_ret ENOMEM) [] [])
        (fixture (VmMaps.mkVmMapsFull [] [(4096, 4096)] [] 0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- Uniform eager backing makes the two-page source's grow answerable;
the spec does not decline it.
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem uniform_backing_grow_is_modeled (i : SyscallInput) :
    ¬ mremap_spec 65536 8192 12288 1 i two_page_model Unmodeled := by
  sys_refute

/-! ## Equal size: declined across the implementation disagreement

The source argument is on `mremap_spec` (#1426). -/

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem equal_size_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 8192 1 i two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- no-row: `two_page_model` fixes address 65536; corpus equal-size rows use runtime addresses and every equal-size call now declines (#1426).
kernel: mm/mremap.c:mremap_at@v6.18.46 -/
theorem equal_size_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 8192 1 i two_page_model
        (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem equal_size_is_unmodeled (i : SyscallInput) :
    mremap_spec 65536 8192 8192 1 i two_page_model Unmodeled := by
  sys_norm

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem new_size_4095_is_equal_size (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 4095 1 i tight_model o ↔ o = Unmodeled := by
  sys_norm

/-- A shrink-shaped answer to the 4095-byte request is rejected: the rounded
lengths are equal (:1917-1918).
no-row: `tight_model` fixes address 65536; corpus rows use runtime addresses and the rounded-equal call now declines (#1426).
kernel: mm/mremap.c:do_mremap,mremap_at@v6.18.46 -/
theorem new_size_4095_shrink_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 4095 1 i tight_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(69631, 1)] [] []) m' evs) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem old_size_4097_is_equal_size (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 4097 8192 1 i two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem lazy_equal_size_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 8192 1 i lazy_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem equal_size_over_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 8192 1 i over_budget_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-! ## Shrink: declined across the implementation disagreement

The old in-place effect remains a negative candidate below. -/

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem shrink_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 4096 1 i two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
no-row: `two_page_model` fixes address 65536; corpus shrink rows use runtime addresses and every shrink now declines (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem shrink_enomem_not_claimed (i : SyscallInput) :
    ¬ mremap_spec 65536 8192 4096 1 i two_page_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) two_page_model []) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
no-row: `two_page_model` and `tight_model` fix address 65536; corpus shrink rows use runtime addresses and every shrink now declines (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem shrink_inplace_not_claimed (i : SyscallInput) :
    ¬ mremap_spec 65536 8192 4096 1 i two_page_model
      (Ok (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) tight_model []) := by
  sys_refute

/-- A shrink that unmaps the WRONG page, keeps the tail in the ledger,
zero-fills, or returns the new end instead of `addr`, is a lie.
kernel: mm/mremap.c:mremap_at,shrink_vma@v6.18.46 -/
theorem shrink_wrong_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 4096 1 i two_page_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- A shrink whose ledger still holds the tail is rejected: `do_vmi_munmap`
removed it (`shrink_vma`, :1337-1338).  Hypothesis form, as the forged
post-state differs from the admitted one with `evs` symbolic.
kernel: mm/mremap.c:shrink_vma; mm/vma.c:do_vmi_munmap@v6.18.46 -/
theorem shrink_unshrunk_ledger_rejected (i : SyscallInput) (evs : List event) :
    ¬ mremap_spec 65536 8192 4096 1 i two_page_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) two_page_model evs) := by
  intro h
  sys_refute at h

/-- A shrink that zero-fills the kept page is rejected: `shrink_vma` touches
only the tail (:1330).
kernel: mm/mremap.c:shrink_vma@v6.18.46 -/
theorem shrink_with_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 4096 1 i two_page_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [(65536, 4096)] [(69632, 4096)] [] []) m' evs) := by
  sys_refute

/-- A shrink returning the new end is rejected: `mremap_at` returns `addr`
(:1572).
no-row: `two_page_model` fixes address 65536; corpus shrink rows use runtime addresses and every shrink now declines (#1426).
kernel: mm/mremap.c:mremap_at@v6.18.46 -/
theorem shrink_returning_new_end_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 4096 1 i two_page_model
        (Ok (SyscallEffect.mkEffectU 69632 [] [] [(69632, 4096)] [] []) m' evs) := by
  sys_refute

/-- no-row: `two_page_model` fixes address 65536; corpus shrink rows use runtime addresses and every shrink now declines (#1426).
kernel: mm/mremap.c:check_prep_vma,shrink_vma@v6.18.46 -/
theorem shrink_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 8192 4096 1 i two_page_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem shrink_by_two_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 12288 4096 1 i three_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- A shrink by two that drops only ONE page — a tail the length of the new
size — is a lie: `vrm->delta` is `old_len - new_len` (`shrink_vma`, :1331).
kernel: mm/mremap.c:shrink_vma@v6.18.46 -/
theorem shrink_by_two_short_tail_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 12288 4096 1 i three_page_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) m' evs) := by
  sys_refute

/-- …and so is a tail based at `old + (old_n - new_n)`, which keeps the
middle page and drops the last: `unmap_start` is `addr + new_len` (:1330).
kernel: mm/mremap.c:shrink_vma@v6.18.46 -/
theorem shrink_by_two_wrong_base_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 12288 4096 1 i three_page_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(73728, 4096)] [] []) m' evs) := by
  sys_refute

/-- The refunded page is grantable again: an ordinary rw `mmap` after the
shrink may be placed at 131072 with the budget the tail gave back.
kernel: mm/vma.c:do_vmi_munmap; mm/mmap.c:do_mmap@v6.18.46 -/
theorem refund_is_regrantable (i : SyscallInput) :
    mmap_spec 0 4096 3 34 mmap_fd_none 0 i tight_model
      (Ok (mkEffect 131072 [] [(131072, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(131072, 4096), (65536, 4096)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-! ## Grow: in place, or moved

`expand_vma` (:1512-1544) grows in place when `vrm_can_expand_in_place`
holds (:1520-1526) and otherwise moves under MAYMOVE (:1535-1543).  The
in-place test reads the next VMA and the `MAP_FIXED` search
(`vma_expandable`, :1415-1427), which the ledger does not carry, so the
model admits both resolutions wherever its own coarser test allows the
in-place one. -/

/-- Three resolutions on a one-page mapping with a free page above it:
-ENOMEM with nothing changed; the in-place grow with exactly the new page
zero-filled; or a move to a fresh destination `dst` — the whole source
copied, the tail page above it zero-filled, the source unmapped.
kernel: mm/mremap.c:expand_vma,expand_vma_in_place,move_vma,copy_vma_and_data@v6.18.46 -/
theorem inplace_grow_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 1 i tight_model o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) tight_model []
       ∨ o = Ok (mkEffect 65536 [] [(69632, 4096)])
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) []
       ∨ ∃ dst : word,
           o = Ok (SyscallEffect.mkEffectU dst [] [(dst + 4096, 4096)] [(65536, 4096)]
                    [MemCopy.mkCopy 65536 dst 4096] [])
                  (mremap_model_next tight_model 65536 4096 dst 8192) []
           ∧ mremap_fresh_b tight_model 4096 8192 65536 4096 dst 8192 = true) := by
  sys_norm

/-- The in-place grow is admitted (Rocq's `mremap_inplace_grow_accepts`):
`expand_vma_in_place` extends the VMA (`vma_merge_extend`, :1470) and the
new page has no page tables, so it reads as zeroes.
kernel: mm/mremap.c:expand_vma_in_place; mm/vma.c:vma_merge_extend@v6.18.46 -/
theorem inplace_grow_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i tight_model
      (Ok (mkEffect 65536 [] [(69632, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-- …and so is a move to 131072, copying the source and zero-filling the
grown page above it (`move_vma`, :1266-1317).
kernel: mm/mremap.c:move_vma,copy_vma_and_data,unmap_source_vma@v6.18.46 -/
theorem move_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i tight_model
      (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
            [MemCopy.mkCopy 65536 131072 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-- …and the environment's -ENOMEM, with nothing changed: every failure
of the move rolls back (`copy_vma_and_data`, :1208-1228) and the in-place
charge is refused before anything moved (`expand_vma_in_place`, :1458-1459).
kernel: mm/mremap.c:expand_vma_in_place,copy_vma_and_data@v6.18.46 -/
theorem grow_enomem_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i tight_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) tight_model []) := by
  sys_norm

/-- An -ENOMEM that also unmapped the source is a lie: under MAYMOVE the
failed move unmaps the NEW area, not the source (:1224-1228 re-point the
request before `unmap_source_vma`, :1312).
kernel: mm/mremap.c:copy_vma_and_data,move_vma@v6.18.46 -/
theorem grow_enomem_with_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- An errno outside `mremap_errnos` on a grow is refused: -EINVAL,
-EFAULT and -EAGAIN are gates this shape has passed (the `mremap_errnos`
docstring walks `check_prep_vma`, :1690-1743).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem grow_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- -EAGAIN needs a locked VMA (`mlock_future_ok`, mm/mmap.c:233-234),
which no modeled mapping is.
kernel: mm/mremap.c:check_prep_vma; mm/mmap.c:mlock_future_ok@v6.18.46 -/
theorem grow_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- The grow never declines on a tracked source.
kernel: mm/mremap.c:expand_vma@v6.18.46 -/
theorem grow_never_unmodeled (i : SyscallInput) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model Unmodeled := by
  sys_refute

/-- The in-place grow must zero-fill exactly the delta: a success that
zero-fills nothing, or the whole grown mapping, is refused — the delta has
no page tables (`vma_merge_extend` installs none) and the old page keeps
its bytes.
kernel: mm/mremap.c:expand_vma_in_place; mm/vma.c:vma_merge_extend@v6.18.46 -/
theorem inplace_grow_without_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model (Ok (mkEffect 65536 [] []) m' evs) := by
  sys_refute

/-- …and one that zero-fills the old page too is rejected: the kept page
keeps its bytes, `vma_merge_extend` extends and zaps nothing.
kernel: mm/mremap.c:expand_vma_in_place; mm/vma.c:vma_merge_extend@v6.18.46 -/
theorem inplace_grow_rezeroing_source_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (mkEffect 65536 [] [(65536, 8192)]) m' evs) := by
  sys_refute

/-- …and a success that grew the ledger by two pages for a one-page delta
is refused.
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem inplace_grow_wrong_ledger_rejected (i : SyscallInput) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (mkEffect 65536 [] [(69632, 4096)])
            (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 8192 0 demo_sp)) evs) := by
  intro h
  sys_refute at h

/-! ### A grow by two pages

Every other grow in this file is 4096 → 8192, where the delta equals the
old length, so `mremap_tail`'s length `new_nZ - old_nZ` and the copy length
`old_n` are not told apart from their wrong spellings.  A grow by two pages
does. -/

/-- In place, the two new pages read as zeroes: `vma_merge_extend` extends
the VMA by `vrm->delta` (`expand_vma_in_place`, :1470) and installs no page
table for it.
kernel: mm/mremap.c:expand_vma_in_place; mm/vma.c:vma_merge_extend@v6.18.46 -/
theorem inplace_grow_by_two_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 12288 1 i roomy_model
      (Ok (mkEffect 65536 [] [(69632, 8192)])
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- Zero-filling only the OLD length's worth of the delta is refused: the
whole delta is new.
kernel: mm/mremap.c:expand_vma_in_place; mm/vma.c:vma_merge_extend@v6.18.46 -/
theorem inplace_grow_by_two_short_tail_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 12288 1 i roomy_model
        (Ok (mkEffect 65536 [] [(69632, 4096)]) m' evs) := by
  sys_refute

/-- Moved, the ONE source page is copied and the TWO pages above it at the
destination read as zeroes: `move_page_tables` walks `vrm->old_len`
(`PAGETABLE_MOVE`, :1191; :1208) and `copy_vma` installs nothing for the
rest of `vrm->new_len` (:1193).
kernel: mm/mremap.c:move_vma,copy_vma_and_data,move_ptes@v6.18.46 -/
theorem move_grow_by_two_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 12288 1 i roomy_model
      (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 8192)] [(65536, 4096)]
            [MemCopy.mkCopy 65536 131072 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(131072, 12288)] [] 0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- A copy the length of the DELTA — two pages from a one-page source,
reading past the VMA — is refused: `move_ptes` moves `old_len` bytes of
page-table entries and nothing beyond the source (:1191, :1208).
kernel: mm/mremap.c:copy_vma_and_data,move_ptes@v6.18.46 -/
theorem move_copy_of_the_delta_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 12288 1 i roomy_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 8192)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 8192] []) m' evs) := by
  sys_refute

/-- …and a moved tail the length of the OLD size, one page of a two-page
delta, is refused too.
kernel: mm/mremap.c:copy_vma_and_data,move_ptes@v6.18.46 -/
theorem move_grow_by_two_short_tail_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 12288 1 i roomy_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] []) m' evs) := by
  sys_refute

/-! ### What a move must look like

`move_ptes` moves every present PTE of the WHOLE source (:268-269 skip
only the empty ones, :287 clears, :300 installs), the grown tail has no
page tables, and `unmap_source_vma` (:1122) drops the source. -/

/-- A move that copies only part of the source is refused.
kernel: mm/mremap.c:move_ptes,copy_vma_and_data@v6.18.46 -/
theorem move_short_copy_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 2048] []) m' evs) := by
  sys_refute

/-- …and so is one with no copy at all, or one that leaves the source
mapped, or one that zero-fills the whole destination.
kernel: mm/mremap.c:move_ptes,unmap_source_vma@v6.18.46 -/
theorem move_without_copy_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)] [] []) m' evs) := by
  sys_refute

/-- A move that leaves the source mapped is rejected: `unmap_source_vma`
drops it (:1122).
kernel: mm/mremap.c:unmap_source_vma@v6.18.46 -/
theorem move_without_unmap_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] []
              [MemCopy.mkCopy 65536 131072 4096] []) m' evs) := by
  sys_refute

/-- A move that zero-fills the copied page is rejected: the moved PTEs
carry the bytes (`move_ptes`, :287, :300).
kernel: mm/mremap.c:move_ptes@v6.18.46 -/
theorem move_rezeroing_destination_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(131072, 8192)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] []) m' evs) := by
  sys_refute

/-- A move-shaped answer AT the source address is refused — by the
`dst ≠ old` conjunct of `mremap_fresh_b` and, independently, by its
`region_free` conjunct, since the source is still in `vm_maps`; so this pin
does not isolate `dst ≠ old`, and `dst_eq_old_refused_before_region_free`
records which of the two answers first.  In Linux the destination search
runs while the source is live (`vrm_set_new_addr` at :1539,
`unmap_source_vma` at :1312), so it can never land on the source.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem move_onto_itself_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 65536 4096] []) m' evs) := by
  sys_refute

/-- A move whose ledger still lists the source is refused.
kernel: mm/mremap.c:unmap_source_vma@v6.18.46 -/
theorem move_keeping_source_in_ledger_rejected (i : SyscallInput) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i tight_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] [])
            (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192), (65536, 4096)] [] 0 0 8192 0 demo_sp)) evs) := by
  intro h
  sys_refute at h

/-! ### Where the in-place grow is unavailable

The model's in-place test is `mremap_inplace_grow_b`: the grown range
clear of the image and of every other live mapping, ending at or below
`alloc_top`, and within budget.  Each conjunct is pinned by a state that
flips it and nothing else. -/

/-- A live neighbour directly above the source: the in-place grow is
refused, and the move is what remains (Rocq's
`mremap_inplace_grow_into_neighbour_rejected`).  Linux's
`find_vma_intersection` (:1421-1422) refuses the expansion for the same
neighbour.
kernel: mm/mremap.c:vma_expandable@v6.18.46 -/
theorem inplace_grow_into_neighbour_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i crowded_model
        (Ok (mkEffect 65536 [] [(69632, 4096)]) m' evs) := by
  sys_refute

/-- …and the move remains admitted on the crowded ledger.
kernel: mm/mremap.c:expand_vma,move_vma@v6.18.46 -/
theorem crowded_move_still_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i crowded_model
      (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
            [MemCopy.mkCopy 65536 131072 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192), (69632, 4096)] [] 0 0 16384 0 demo_sp)) []) := by
  sys_norm

/-- The image directly above the source: the in-place grow is refused —
the `vm_reserved` half of the guard, which no trace can reach (a tracked
mapping never sits below a LOAD segment) and only this ledger can flip.
kernel: mm/mremap.c:vma_expandable@v6.18.46 -/
theorem inplace_grow_into_image_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i below_image_model
        (Ok (mkEffect 65536 [] [(69632, 4096)]) m' evs) := by
  sys_refute

/-- …and the move out from under it is admitted, the reservation untouched.
kernel: mm/mremap.c:expand_vma,move_vma@v6.18.46 -/
theorem move_out_of_the_image_accepts (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i below_image_model
      (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
            [MemCopy.mkCopy 65536 131072 4096] [])
          (fixture (VmMaps.mkVmMapsFull [(69632, 4096)] [(131072, 8192)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-- …but a move ONTO the image is refused: the LOAD segments are VMAs the
destination search walks (`vm_unmapped_area`, mm/mmap.c:663), so it never
returns a range they hold.  This is the `vm_reserved` half of the guard's
`region_free`; every other move in this file with a reservation places its
destination clear of it (probe `movetext`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem move_onto_image_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i below_image_model
        (Ok (SyscallEffect.mkEffectU 69632 [] [(73728, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 69632 4096] []) m' evs) := by
  sys_refute

/-- …and at that destination only the reserved half refuses: the live half
of `region_free` and every other conjunct of `mremap_fresh_b` hold.
The kernel claim is `move_onto_image_rejected`'s: the search walks the live VMAs and the image's own mappings and never returns a range they hold.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem image_destination_fails_only_reserved :
    region_free (m_vmmaps below_image_model).vm_reserved 69632 8192 = false
    ∧ region_free (m_vmmaps below_image_model).vm_maps 69632 8192 = true
    ∧ (!(bv_eqb (69632 : word) 65536)) = true
    ∧ (bv_unsigned (69632 : word) % page_size == 0) = true
    ∧ (0 < bv_unsigned (69632 : word)) = true
    ∧ (bv_unsigned (69632 : word) + 8192 ≤ alloc_top (m_vmmaps below_image_model)) = true
    ∧ mremap_final_budget_b below_image_model 65536 4096 69632 8192 = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The grant top is INCLUSIVE for the in-place grow: a mapping two pages
below `demo_top` grows to end exactly at it (Rocq's
`mremap_inplace_grow_to_ceiling_accepts`).
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem inplace_grow_to_ceiling_accepts (i : SyscallInput) :
    mremap_spec (Z_to_bv 64 (demo_top - 8192)) 4096 8192 1 i grow_to_ceiling_model
      (Ok (mkEffect (Z_to_bv 64 (demo_top - 8192)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 8192), 8192)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-- …and one page higher the grown mapping would cross into the stack
band, which is in neither ledger and only the `alloc_top` conjunct sees:
refused (Rocq's `mremap_inplace_grow_past_ceiling_rejected`; the pair
differs only in the source's base address).  The refusal is the MODEL's:
`vma_expandable` (:1415-1427) tests only overflow, an intersecting VMA and
a `MAP_FIXED` probe bounded by `TASK_SIZE`, so Linux itself would grow in
place here if nothing were mapped above.  What keeps a modeled trace from
asking is that the kernel's top-down search places below `mmap_base`
(mm/util.c:434, at least 128 MiB under the stack top;
`generic_get_unmapped_area_topdown` takes it as its high limit,
mm/mmap.c:766, Linux v6.18.46), while the band above `alloc_top` is the
stack's (`State.alloc_top`).  The search's bottom-up fallback (mm/mmap.c:778-784)
runs only once the space under `mmap_base` is exhausted, and a placement
into the band that Linux would honour is the residual
`bugs/grants-into-the-stack-band.md` records.
kernel: mm/mremap.c:vma_expandable; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem inplace_grow_past_ceiling_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 8192 1 i grow_past_ceiling_model
        (Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]) m' evs) := by
  sys_refute

/-- …while the move DOWN from there, to 65536, is admitted.
kernel: mm/mremap.c:expand_vma,move_vma@v6.18.46 -/
theorem move_down_from_ceiling_accepts (i : SyscallInput) :
    mremap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 8192 1 i grow_past_ceiling_model
      (Ok (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(Z_to_bv 64 (demo_top - 4096), 4096)]
            [MemCopy.mkCopy (Z_to_bv 64 (demo_top - 4096)) 65536 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 8192 0 demo_sp)) []) := by
  sys_norm

/-! ## The backing budget

Linux charges the NET DELTA of a grow (`may_expand_vm`, mm/mmap.c:1324-1345,
Linux v6.18.46, from `check_prep_vma` at :1742-1743; `vrm_calc_charge`,
:986) on both the
in-place and the move path; the model charges the complete post-state,
the same delta for eager mappings. -/

/-- Under a budget already spent by the source, a grow is forced to
-ENOMEM: the in-place gate refuses, and no destination satisfies the
placement guard — which `no_room_over_budget` pins — so only the errno
arm remains (Rocq's `mremap_grow_beyond_budget_rejected`).
kernel: mm/mremap.c:check_prep_vma,vrm_calc_charge,expand_vma_in_place,move_vma; mm/mmap.c:may_expand_vm@v6.18.46 -/
theorem grow_over_budget_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 4096 8192 1 i budget_full_model o ↔
      o = Ok (mkEffect (errno_ret ENOMEM) [] []) budget_full_model [] := by
  sys_norm
  constructor
  · rintro (h | ⟨dst, -, hg⟩)
    · exact h
    · exact absurd hg (no_room_over_budget dst)
  · exact Or.inl

/-- The in-place success is refused over budget: the commit charge
(`vrm_calc_charge`, :990-991) fails first.
kernel: mm/mremap.c:expand_vma_in_place,vrm_calc_charge@v6.18.46 -/
theorem grow_over_budget_inplace_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i budget_full_model
        (Ok (mkEffect 65536 [] [(69632, 4096)]) m' evs) := by
  sys_refute

/-- …and so is the move: its charge (`move_vma`, :1281-1282) is the same
delta.
kernel: mm/mremap.c:move_vma,vrm_calc_charge@v6.18.46 -/
theorem grow_over_budget_move_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i budget_full_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] []) m' evs) := by
  sys_refute

/-- A move onto a range another mapping holds is refused: the destination
search runs over the live VMAs (`vrm_set_new_addr`, :957-960;
`vm_unmapped_area`, mm/mmap.c:663) and never returns an occupied range
(Rocq's `mremap_move_to_occupied_range_rejected`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem move_to_occupied_range_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i occupied_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] []) m' evs) := by
  sys_refute

/-! ## MAP_NORESERVE provenance across a resize

`State.vm_resize_backing` keeps the lazy provenance and the touched pages
with their source-relative offsets: a shrink releases the pages beyond the
new end, a grow extends the reservation without charging its tail, and a
move carries the touched pages over (the page tables move with
`move_page_tables`, :1208).  What the kernel charges is the VMA's commit
(`vrm_calc_charge`, :976-977 skips a VMA without `VM_ACCOUNT`, which a
`MAP_NORESERVE` mapping lacks outside strict overcommit). -/

/-- The old Linux-only answer is no longer certain across supported
implementations; see the decline argument in `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem lazy_shrink_unmodeled_iff (i : SyscallInput) (o : outcome SyscallEffect) :
    mremap_spec 65536 8192 4096 1 i lazy_two_pages o ↔ o = Unmodeled := by
  sys_norm

/-- …read off the post-state function: one page reserved, one page
charged (Rocq's `mremap_lazy_shrink_ledgers_are_exact`).
model: algebra of the resize helper only; this does not assert a modeled shrink. -/
theorem lazy_shrink_ledgers_are_exact :
    m_vm_lazy (mremap_model_next lazy_two_pages 65536 8192 65536 4096) = [(65536, 4096)]
    ∧ m_vm_materialized (mremap_model_next lazy_two_pages 65536 8192 65536 4096) = [65536]
    ∧ vm_backing_used (mremap_model_next lazy_two_pages 65536 8192 65536 4096) = 4096 := by
  refine ⟨by decide, by decide, by decide⟩

/-- A shrink that KEPT the second page's charge is refused.
kernel: mm/mremap.c:shrink_vma@v6.18.46 -/
theorem lazy_shrink_keeping_charge_rejected (i : SyscallInput) (evs : List event) :
    ¬ mremap_spec 65536 8192 4096 1 i lazy_two_pages
        (Ok (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] [])
            (with_vm_backing [(65536, 4096)] [65536, 69632]
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 0 demo_sp))) evs) := by
  intro h
  sys_refute at h

/-- A lazy grow succeeds at a FULL backed budget: the new page is a
reservation, not an eager charge (Rocq's
`mremap_lazy_grow_bypasses_eager_delta`).  Linux charges nothing for it
either: `vrm_calc_charge` returns at once without `VM_ACCOUNT` (:976-977).
kernel: mm/mremap.c:vrm_calc_charge,expand_vma_in_place@v6.18.46 -/
theorem lazy_grow_bypasses_eager_delta (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i lazy_one_page
      (Ok (mkEffect 65536 [] [(69632, 4096)])
          (with_vm_backing [(65536, 8192)] [65536]
            (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 4096 0 demo_sp))) []) := by
  sys_norm

/-- …and the post-state keeps only the old charge (Rocq's
`mremap_lazy_grow_preserves_only_old_charge`).
model: the ledgers of the lazy grow's post-state, decided once; the kernel claim is the pin above. -/
theorem lazy_grow_preserves_only_old_charge :
    m_vm_lazy (mremap_model_next lazy_one_page 65536 4096 65536 8192) = [(65536, 8192)]
    ∧ m_vm_materialized (mremap_model_next lazy_one_page 65536 4096 65536 8192) = [65536]
    ∧ vm_backing_used (mremap_model_next lazy_one_page 65536 4096 65536 8192) = 4096 := by
  refine ⟨by decide, by decide, by decide⟩

/-- An in-place lazy grow that charged the new page eagerly — the
post-state a kernel that dropped the provenance would report — is refused;
the forgery differs from the admitted post-state in the lazy ledger alone.
kernel: mm/mremap.c:vrm_calc_charge@v6.18.46 -/
theorem lazy_grow_eager_charge_rejected (i : SyscallInput) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i lazy_one_page
        (Ok (mkEffect 65536 [] [(69632, 4096)])
            (with_vm_backing [(65536, 4096)] [65536]
              (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 4096 0 demo_sp))) evs) := by
  intro h
  sys_refute at h

/-- A lazy move relocates the touched page with the mapping: the page's
charge moves to 131072 and the reservation follows (Rocq's
`mremap_lazy_move_relocates_materialized_pages`).
kernel: mm/mremap.c:move_vma,copy_vma_and_data,move_page_tables@v6.18.46 -/
theorem lazy_move_relocates_materialized_pages (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i lazy_one_page
      (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
            [MemCopy.mkCopy 65536 131072 4096] [])
          (with_vm_backing [(131072, 8192)] [131072]
            (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192)] [] 0 0 4096 0 demo_sp))) []) := by
  sys_norm

/-- …and its ledgers follow the contents (Rocq's
`mremap_lazy_move_ledgers_follow_contents`).
model: the ledgers of the lazy move's post-state, decided once; the kernel claim is the pin above. -/
theorem lazy_move_ledgers_follow_contents :
    m_vm_lazy (mremap_model_next lazy_one_page 65536 4096 131072 8192) = [(131072, 8192)]
    ∧ m_vm_materialized (mremap_model_next lazy_one_page 65536 4096 131072 8192) = [131072]
    ∧ vm_backing_used (mremap_model_next lazy_one_page 65536 4096 131072 8192) = 4096 := by
  refine ⟨by decide, by decide, by decide⟩

/-- A lazy move that left the touched page's charge at the OLD address is
refused: `move_page_tables` (:1208) moves the page, so its charge is at
the destination.
kernel: mm/mremap.c:copy_vma_and_data,move_page_tables@v6.18.46 -/
theorem lazy_move_leaving_page_behind_rejected (i : SyscallInput) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i lazy_one_page
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] [])
            (with_vm_backing [(131072, 8192)] [65536]
              (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192)] [] 0 0 4096 0 demo_sp))) evs) := by
  intro h
  sys_refute at h

/-! ## Moved destinations are preference-free placements

Linux picks a MAYMOVE destination with `get_unmapped_area` at `new_addr = 0`
and no `MAP_FIXED` (`vrm_set_new_addr`, :949, :952-953, :957-960), so
whatever the spec may say about a preference-free `mmap` placement it may
say here, and no more: page-aligned, positive, ending at or below the
run's grant top, disjoint from every recorded mapping, within budget.  The
kernel's allocator descends from an `mmap_base` just under the stack
(`mmap_base`, mm/util.c:434, Linux v6.18.46) and never produces a destination as low as
0x80000000, so only these cases can say what the spec does with one. -/

/-- One live page at 0x2aaaaab000 under a two-page budget, with the
top-down `mmap_base` recorded. -/
def placement_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x2aaaaab000, 4096)] [] 0 0 8192
    (Z_to_bv 64 mmap_base_max) demo_sp)

/-- A growing move to a low destination is admitted: 0x80000000 is
page-aligned, positive, below the ceiling and free, which is everything
the spec asks of a preference-free placement (Rocq's
`mremap_move_low_destination_admitted`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem move_low_destination_admitted (i : SyscallInput) :
    mremap_spec (Z_to_bv 64 0x2aaaaab000) 4096 8192 1 i placement_model
      (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 0x80000000) []
            [(Z_to_bv 64 0x80001000, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
            [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000000) 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 8192)] [] 0 0 8192
            (Z_to_bv 64 mmap_base_max) demo_sp)) []) := by
  sys_norm

/-- An unaligned destination is refused: `__get_unmapped_area` answers
-EINVAL to one (mm/mmap.c:859-860), so the search never returns it.
kernel: mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem move_unaligned_destination_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec (Z_to_bv 64 0x2aaaaab000) 4096 8192 1 i placement_model
        (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 0x80000001) []
              [(Z_to_bv 64 0x80001001, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
              [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000001) 4096] []) m' evs) := by
  sys_refute

/-- Destination 0 is refused: the search's floor is `PAGE_SIZE`
(`generic_get_unmapped_area_topdown` sets `info.low_limit`, mm/mmap.c:765)
and `__get_unmapped_area` ends in `security_mmap_addr` (:862), -EPERM below
`mmap_min_addr` for an unprivileged task — so Linux never returns 0 (probe
`movegrow`'s "dst nonzero").  The `0 < dst` conjunct of `mremap_fresh_b`.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,__get_unmapped_area@v6.18.46 -/
theorem move_to_zero_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec (Z_to_bv 64 0x2aaaaab000) 4096 8192 1 i placement_model
        (Ok (SyscallEffect.mkEffectU 0 [] [(4096, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
              [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) 0 4096] []) m' evs) := by
  sys_refute

/-- …and at destination 0 every OTHER conjunct of the guard holds, so the
refusal above is that conjunct's alone.
The kernel claim is `move_to_zero_rejected`'s: the search's low limit is a page and address 0 is refused below `mmap_min_addr`.
kernel: mm/mmap.c:generic_get_unmapped_area_topdown,__get_unmapped_area@v6.18.46 -/
theorem zero_destination_fails_only_positivity :
    (0 < bv_unsigned (0 : word)) = false
    ∧ (!(bv_eqb (0 : word) (Z_to_bv 64 0x2aaaaab000))) = true
    ∧ (bv_unsigned (0 : word) % page_size == 0) = true
    ∧ (bv_unsigned (0 : word) + 8192 ≤ alloc_top (m_vmmaps placement_model)) = true
    ∧ region_free ((m_vmmaps placement_model).vm_reserved ++ (m_vmmaps placement_model).vm_maps) 0 8192 = true
    ∧ mremap_final_budget_b placement_model (Z_to_bv 64 0x2aaaaab000) 4096 0 8192 = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The source and the overlapping destination are NAMED, and the case
below and its witness both use the names, so the witness cannot drift off
the case it is evidence for. -/
def mremap_src : word := Z_to_bv 64 0x2aaaaab000
def mremap_src_n : word := Z_to_bv 64 4096
def mremap_overlapping_dst : word := Z_to_bv 64 0x2aaaaaa000
def mremap_overlapping_dst_n : word := Z_to_bv 64 8192

/-- A destination that OVERLAPS the source is refused — the disjointness
condition doing the work a move most needs it for.  Linux runs the search
while the source VMA is still live (`vrm_set_new_addr` at :1539, the source
unmapped only by `unmap_source_vma` at :1312), so the destination cannot
be a range the source still holds; the model gets the exclusion from `old`
still being in `vm_maps` when `region_free` runs.  The address is chosen
so that ONLY `region_free` refuses it: it starts one page BELOW the source
and is two pages long, so `dst ≠ old` holds and the alignment, positivity,
ceiling and budget conjuncts hold too — the next pin checks that.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem move_onto_source_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec mremap_src 4096 8192 1 i placement_model
        (Ok (SyscallEffect.mkEffectU mremap_overlapping_dst [] [(mremap_src, 4096)] [(mremap_src, 4096)]
              [MemCopy.mkCopy mremap_src mremap_overlapping_dst 4096] []) m' evs) := by
  sys_refute

/-- …and the uniqueness is CHECKED rather than asserted: at that
destination every other conjunct of `mremap_fresh_b` holds and only
`region_free` fails.  Each conjunct is the guard's, at the arguments the
case above passes; that the six are ALL of them is `fresh_b_conjuncts`.
The kernel claim is `move_onto_source_rejected`'s: the search runs while the source VMA is live, so it never returns a range the source holds.
kernel: mm/mremap.c:expand_vma,vrm_set_new_addr,move_vma@v6.18.46 -/
theorem move_onto_source_only_region_free_fails :
    region_free ((m_vmmaps placement_model).vm_reserved ++ (m_vmmaps placement_model).vm_maps)
      mremap_overlapping_dst mremap_overlapping_dst_n = false
    ∧ !(bv_eqb mremap_overlapping_dst mremap_src) = true
    ∧ (bv_unsigned mremap_overlapping_dst % page_size == 0) = true
    ∧ (0 < bv_unsigned mremap_overlapping_dst) = true
    ∧ (bv_unsigned mremap_overlapping_dst + bv_unsigned mremap_overlapping_dst_n
         ≤ alloc_top (m_vmmaps placement_model)) = true
    ∧ mremap_final_budget_b placement_model mremap_src mremap_src_n
        mremap_overlapping_dst mremap_overlapping_dst_n = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The spelling that would NOT have bitten: at `dst = old` the guard's
first conjunct is already false, so `region_free` is never consulted and
such a case would pin nothing about it.
model: the guard's first conjunct at the source, decided once; documentary, with `move_onto_source_rejected` as the pin. -/
theorem dst_eq_old_refused_before_region_free :
    (!(bv_eqb mremap_src mremap_src)) = false := by decide

/-- THE ENUMERATION IS PINNED BY THE BUILD: the guard is exactly these six
conjuncts, at abstract arguments, so a seventh conjunct breaks this
statement instead of quietly voiding the witness above (the Rocq lemma of
the same name).
rocq-twin: mremap_fresh_b_conjuncts -/
theorem fresh_b_conjuncts (m : Model) (old_nZ new_nZ : Int) (old old_n dst new_n : word) :
    mremap_fresh_b m old_nZ new_nZ old old_n dst new_n
      = (!(bv_eqb dst old)
         && (bv_unsigned dst % page_size == 0)
         && (0 < bv_unsigned dst)
         && (bv_unsigned dst + new_nZ ≤ alloc_top (m_vmmaps m))
         && region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) dst new_n
         && mremap_final_budget_b m old old_n dst new_n) := rfl

/-- …and the ordinary move, one page above the source, is admitted.
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem move_just_above_source_accepts (i : SyscallInput) :
    mremap_spec (Z_to_bv 64 0x2aaaaab000) 4096 8192 1 i placement_model
      (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 0x2aaaaac000) []
            [(Z_to_bv 64 0x2aaaaad000, 4096)] [(Z_to_bv 64 0x2aaaaab000, 4096)]
            [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x2aaaaac000) 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x2aaaaac000, 8192)] [] 0 0 8192
            (Z_to_bv 64 mmap_base_max) demo_sp)) []) := by
  sys_norm

/-- A hole of ONE page at 131072, a live page right above it: free for the
old length, not for the new one. -/
def half_hole_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (135168, 4096)] [] 0 0 16384 0 demo_sp)

/-- The destination must be free for the NEW length: `vrm_set_new_addr`
asks the search for `vrm->new_len` (:957), so a gap that fits only the
source is never returned (probe `movehalf`).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem move_onto_half_hole_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i half_hole_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] []) m' evs) := by
  sys_refute

/-- …and the hole really is free for the old length alone.
model: `region_free` at the half hole for both lengths, decided once; the kernel claim is `move_onto_half_hole_rejected`. -/
theorem half_hole_is_free_for_the_old_length_only :
    region_free ((m_vmmaps half_hole_model).vm_reserved ++ (m_vmmaps half_hole_model).vm_maps) 131072 4096 = true
    ∧ region_free ((m_vmmaps half_hole_model).vm_reserved ++ (m_vmmaps half_hole_model).vm_maps) 131072 8192 = false := by
  refine ⟨by decide, by decide⟩

/-! ## The brk-shrink orphan: what keeps a move off protected memory

`mremap_fresh_b` never consults `vm_noaccess`.  On the one reachable state
where a protected range is owned by no `vm_maps` entry — a brk shrink
inside its final page leaves `[69620, 69632)` protected while the brk
entry is TRUNCATED to `(65536, 4084)` — what keeps a page-aligned
destination off the orphan is that residual entry: a destination low
enough to touch the orphan must cross it first.  The pair below differs
only in the destination, one page apart across the orphan's end; the
source at 131072 is an unrelated clean mapping to move. -/

/-- The brk-shrunk ledger with the image reserved, the truncated brk entry,
the orphaned protected page and a clean source at 131072 (Rocq's
`m_brk_orphan_with_source`). -/
def m_brk_orphan_with_source : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(65536, 4084), (131072, 4096)] [(65536, 4096)]
    65536 69620 demo_limit 0 demo_sp)

/-- The counterfactual, UNREACHABLE state: the residual entry taken away. -/
def m_brk_orphan_without_residual : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(131072, 4096)] [(65536, 4096)]
    65536 69620 demo_limit 0 demo_sp)

/-- A move onto the orphan's page is refused: the destination `[65536,
73728)` crosses the residual brk entry, and `region_free` refuses it.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem move_onto_brk_orphan_page_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 131072 4096 8192 1 i m_brk_orphan_with_source
        (Ok (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
              [MemCopy.mkCopy 131072 65536 4096] []) m' evs) := by
  sys_refute

/-- …and one page higher, clear of the residual, the move is admitted with
the protected range carried over verbatim.
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem move_above_brk_orphan_accepts (i : SyscallInput) :
    mremap_spec 131072 4096 8192 1 i m_brk_orphan_with_source
      (Ok (SyscallEffect.mkEffectU 69632 [] [(73728, 4096)] [(131072, 4096)]
            [MemCopy.mkCopy 131072 69632 4096] [])
          (fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(69632, 8192), (65536, 4084)] [(65536, 4096)]
            65536 69620 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-- WHICH half does the work: with the residual entry taken out of the same
state the move onto the orphan page is ACCEPTED, so the property the guard
leans on is "the shrink TRUNCATES the owning entry rather than removing
it", not the orphan's presence in `vm_noaccess`, which the guard never
reads.  The state is unreachable; the case is kept so the load-bearing
property is visible rather than inferred.  The kernel claim is the one the
guard makes: the destination search reads the live VMAs and nothing else
(`vrm_set_new_addr`, :957-960; `vm_unmapped_area`, mm/mmap.c:663).
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:vm_unmapped_area@v6.18.46 -/
theorem move_onto_orphan_without_residual_accepts (i : SyscallInput) :
    mremap_spec 131072 4096 8192 1 i m_brk_orphan_without_residual
      (Ok (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
            [MemCopy.mkCopy 131072 65536 4096] [])
          (fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(65536, 8192)] [(65536, 4096)]
            65536 69620 demo_limit 0 demo_sp)) []) := by
  sys_norm

/-! ## The bound is read from the ledger

The same two effects `inplace_grow_past_ceiling_rejected` and the moved
destination case refuse under `demo_sp` are admitted once the ledger's
stack pointer is `hi_sp`, 256 MiB higher: the grant top is `alloc_top` of
the ledger the run started with, not a constant (the argument is on
`State.alloc_top` and in the twin block of `Cases/Mm/Mmap.v`). -/

/-- An entry stack pointer 256 MiB above the window's bottom. -/
def hi_sp : word := Z_to_bv 64 (sp_window_lo + 0x10000000)

/-- One page just below `demo_top`, on a ledger started at `hi_sp`. -/
def grow_past_top_hi_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] [] 0 0 8192
    (Z_to_bv 64 mmap_base_max) hi_sp)

/-- The in-place grow past `demo_top` is admitted under the high stack
pointer.
kernel: mm/mremap.c:expand_vma_in_place@v6.18.46 -/
theorem inplace_grow_past_demo_top_admitted_under_high_sp (i : SyscallInput) :
    mremap_spec (Z_to_bv 64 (demo_top - 4096)) 4096 8192 1 i grow_past_top_hi_model
      (Ok (mkEffect (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 8192
            (Z_to_bv 64 mmap_base_max) hi_sp)) []) := by
  sys_norm

/-- One page at 65536 on a ledger started at `demo_sp`… -/
def move_source_lo_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 (Z_to_bv 64 mmap_base_max) demo_sp)

/-- …and the same page on a ledger started at `hi_sp`. -/
def move_source_hi_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 (Z_to_bv 64 mmap_base_max) hi_sp)

/-- A move whose destination ends one page past `demo_top` is refused
under the low stack pointer… — the model's bound, read from the ledger's
entry `sp`; the kernel's own top-down search stops lower still, at the
mm's `mmap_base`, which `generic_get_unmapped_area_topdown` takes as its
high limit (mm/mmap.c:766, Linux v6.18.46); its bottom-up fallback
(mm/mmap.c:778-784) runs only once the space under `mmap_base` is
exhausted, and a placement into the band that Linux would honour is the
residual `bugs/grants-into-the-stack-band.md` records.
kernel: mm/mremap.c:vrm_set_new_addr; mm/mmap.c:generic_get_unmapped_area_topdown@v6.18.46 -/
theorem move_past_demo_top_rejected_under_low_sp (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i move_source_lo_model
        (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
              [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] []) m' evs) := by
  sys_refute

/-- …and admitted under the high one.
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem move_past_demo_top_admitted_under_high_sp (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i move_source_hi_model
      (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
            [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 8192
            (Z_to_bv 64 mmap_base_max) hi_sp)) []) := by
  sys_norm

/-- The grant top is INCLUSIVE for the move too: under the low stack pointer
a destination ending exactly at `demo_top` is admitted, the twin of
`inplace_grow_to_ceiling_accepts` (probe `movegrow`'s "exactly at top").
kernel: mm/mremap.c:vrm_set_new_addr,move_vma@v6.18.46 -/
theorem move_to_ceiling_accepts (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i move_source_lo_model
      (Ok (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 8192)) [] [(Z_to_bv 64 (demo_top - 4096), 4096)]
            [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 8192)) 4096] [])
          (fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 8192), 8192)] [] 0 0 8192
            (Z_to_bv 64 mmap_base_max) demo_sp)) []) := by
  sys_norm

/-! ## The bounded approximation, measured

A successful Linux move can leave the source still mapped when the
best-effort unmap of `unmap_source_vma` fails (:1124-1128, "OOM: unable to
split vma, just get accounts right"), while the model always drops `old`.
The cost is bounded: what the ledger calls free after a move differs from
what is really free only over the retained source, so no real placement is
ever refused for it (the Rocq lemma of the same name;
`bugs/mremap-maymove-answers-success.md`). -/

/-- After a move the source entry is gone from the ledger, and a range is
free of the ledger-with-the-source-retained exactly when it is disjoint
from the source and free of the ledger.
rocq-twin: mremap_move_gap_is_the_retained_source -/
theorem move_gap_is_the_retained_source (h : VmMaps) (old dst old_n new_n : word)
    (hdst : bv_eqb dst old = false) :
    map_has (mremap_maps_next h old dst new_n).vm_maps old old_n = false
    ∧ ∀ r n,
        region_free ((old, old_n) :: h.vm_reserved ++ (mremap_maps_next h old dst new_n).vm_maps) r n
          = true
        ↔ iv_overlap r n old old_n = false
          ∧ region_free (h.vm_reserved ++ (mremap_maps_next h old dst new_n).vm_maps) r n = true := by
  refine ⟨?_, fun r n => ?_⟩
  · simp only [mremap_maps_next, map_has, map_remove, List.any_cons, hdst, Bool.false_and,
      Bool.false_or]
    rw [List.any_eq_false]
    intro p hp
    rw [List.mem_filter] at hp
    obtain ⟨-, hq⟩ := hp
    simp only [Bool.not_eq_true'] at hq
    show ¬ (bv_eqb p.1 old && bv_eqb p.2 old_n) = true
    rw [hq, Bool.false_and]
    exact Bool.false_ne_true
  · simp only [List.cons_append, region_free, Bool.and_eq_true, Bool.not_eq_true']

/-! ## The budget mark

`mremap_budget_refused_b` says, from the request and the pre-state alone,
whether a grow's charge is refused: it fires when EITHER the in-place
post-state's gate or the move's gate refuses, and is silent on every
shape the arm declines or answers without charging. -/

/-- The mark fires where the grow's `iff` above lost every charging
resolution.
kernel: mm/mremap.c:check_prep_vma,vrm_calc_charge; mm/mmap.c:may_expand_vm@v6.18.46 -/
theorem budget_mark_fires_over_budget :
    mremap_budget_refused_b 65536 4096 8192 1 budget_full_model = true := by decide

/-- A lazy source and a lazy neighbour, both touched, under a two-page
budget: the two touched pages fill it, and a grow of the source moves or
extends exactly one of them. -/
def lazy_touched_neighbour_model : Model :=
  with_vm_backing [(65536, 4096), (69632, 4096)] [65536, 69632]
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 0 0 8192 0 demo_sp))

/-- Within budget it is silent: on the eager grow, on the lazy grow, and
on the lazy grow beside a touched lazy neighbour, where only the pages
INSIDE the source move with it (`move_page_tables`, :1208, walks the
source range and nothing else) and the neighbour's page keeps its own
charge.
kernel: mm/mremap.c:vrm_calc_charge,copy_vma_and_data@v6.18.46 -/
theorem budget_mark_silent_within_budget :
    mremap_budget_refused_b 65536 4096 8192 1 tight_model = false
    ∧ mremap_budget_refused_b 65536 4096 8192 1 lazy_one_page = false
    ∧ mremap_budget_refused_b 65536 4096 8192 1 lazy_touched_neighbour_model = false := by
  refine ⟨by decide, by decide, by decide⟩

/-- Two of the mark's gates are shadowed on every reachable ledger — the
source gate refuses an unaligned or an empty entry before the budget is
read — so a ledger that CARRIES such an entry is what makes each gate's
own answer visible.  `VmMaps` carries no well-formedness predicate, so
both are writable by hand: an entry based at 65537 under a one-page
budget, and the zero-size entry of `zero_entry_model` under a one-page
budget.  The mark answers `false` for both because the gate fires, where a
mark reading the ledger first would fire on the refused grow.
The gates mirror the kernel's: the alignment -EINVAL of `check_mremap_params` (:1763-1764) and the clone -EINVAL of `check_prep_vma` (:1690-1694), each answered before any charge is read.
kernel: mm/mremap.c:check_mremap_params,check_prep_vma@v6.18.46 -/
theorem budget_mark_gates_are_not_shadowed :
    mremap_budget_refused_b 65537 4096 8192 1
        (fixture (VmMaps.mkVmMapsFull [] [(65537, 4096)] [] 0 0 4096 0 demo_sp)) = false
    ∧ mremap_budget_refused_b 65536 0 8192 1
        (fixture (VmMaps.mkVmMapsFull [] [(65536, 0)] [] 0 0 4096 0 demo_sp)) = false := by
  refine ⟨by decide, by decide⟩

/-- The move's charge counts a source's touched pages only for a LAZY
source, as `State.vm_resize_backing` moves them only then: on a hand-built
ledger with a page under an EAGER source (no reachable ledger has one, a
page is materialized only by the first touch of a lazy one) both drop the
page, and the mark stays silent at a budget the moved page would exceed.
The kernel charges the move its delta (`vrm_calc_charge`, :986) and moves the source's page tables (`copy_vma_and_data`, :1208); a page the ledger does not attribute to a lazy source is not a page the move carries.
kernel: mm/mremap.c:vrm_calc_charge,copy_vma_and_data@v6.18.46 -/
theorem budget_mark_eager_source_moves_no_page :
    mremap_budget_refused_b 65536 4096 8192 1
        (with_vm_backing [] [65536]
          (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 0 demo_sp))) = false := by
  decide

/-- The move's charge, read directly: a lazy source with both pages touched
is charged its two moved pages and nothing for the re-created reservation
(`lazy_two_pages`, grown to three pages); an eager source is charged the
re-created mapping whole (`tight_model`, grown to two).  These are the
two numbers `State.vm_backing_used` reads off the move's post-state at a
fresh destination (the Rocq lemma `mremap_move_charge_at_fresh`).
model: `mremap_move_charge` at a lazy and at an eager source, decided once; ledger arithmetic, not a kernel claim. -/
theorem move_charge_counts_the_moved_pages :
    mremap_move_charge lazy_two_pages 65536 8192 12288 = 8192
    ∧ mremap_move_charge tight_model 65536 4096 8192 = 8192 := by
  refine ⟨by decide, by decide⟩

/-! ### Neither charge bounds the other

The mark tests BOTH gates because neither post-state is charged at least
as much as the other on every state (the `mremap_budget_refused_b`
docstring).  Rocq's `Checks/BudgetPremise.v` carries the two witnesses,
`un_mark_fires_on_the_move_refusal` and `ov_mark_fires_while_a_move_fits`;
they are restated here on two smaller ledgers of the same shape (a one-page
neighbour in place of Rocq's two-page one), because a mark read from one
gate alone passes every other pin in this section. -/

/-- A PROT_NONE mapping directly above the source, under a budget of
exactly the source: the in-place post-state is charged nothing for its
tail — the charge is of the backed view, which subtracts `vm_noaccess` —
while a move re-creates the whole mapping at a fresh destination and is
charged every byte of it. -/
def noaccess_neighbour_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [(69632, 4096)] 0 0 4096 0 demo_sp)

/-- On that ledger the in-place gate fits and the move's gate refuses.
The two gates are the in-place charge (`expand_vma_in_place`, :1458-1459) and the move's (`move_vma`, :1281-1282), both `vrm_calc_charge`'s delta (:986).
kernel: mm/mremap.c:vrm_calc_charge,expand_vma_in_place,move_vma@v6.18.46 -/
theorem move_refusal_is_the_move_charge :
    mremap_final_budget_b noaccess_neighbour_model 65536 4096 65536 8192 = true
    ∧ mremap_move_budget_b noaccess_neighbour_model 65536 4096 8192 = false := by
  refine ⟨by decide, by decide⟩

/-- …so the mark fires there through the move's gate alone: the in-place
resolution is unavailable (the tail meets a live mapping), the move is the
only non-errno resolution, and it is budget-refused.
The Rocq witness is `un_mark_fires_on_the_move_refusal`; the kernel gate it stands for is the move's commit charge (`move_vma`, :1281-1282).
kernel: mm/mremap.c:vrm_calc_charge,move_vma@v6.18.46 -/
theorem budget_mark_fires_on_the_move_refusal :
    mremap_budget_refused_b 65536 4096 8192 1 noaccess_neighbour_model = true := by decide

/-- On the same ledger the spec admits the environment's -ENOMEM…
kernel: mm/mremap.c:move_vma,vrm_calc_charge@v6.18.46 -/
theorem noaccess_neighbour_enomem_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i noaccess_neighbour_model
      (Ok (mkEffect (errno_ret ENOMEM) [] []) noaccess_neighbour_model []) := by
  sys_norm

/-- …refuses the in-place grow, whose tail meets the neighbour
(`find_vma_intersection`, :1421-1422)…
kernel: mm/mremap.c:vma_expandable@v6.18.46 -/
theorem noaccess_neighbour_inplace_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i noaccess_neighbour_model
        (Ok (mkEffect 65536 [] [(69632, 4096)]) m' evs) := by
  sys_refute

/-- …and refuses the move, whose charge (`move_vma`, :1281-1282) the
budget cannot take.
kernel: mm/mremap.c:move_vma,vrm_calc_charge@v6.18.46 -/
theorem noaccess_neighbour_move_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ mremap_spec 65536 4096 8192 1 i noaccess_neighbour_model
        (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
              [MemCopy.mkCopy 65536 131072 4096] []) m' evs) := by
  sys_refute

/-- A LAZY mapping directly above the source, under a two-page budget: the
in-place post-state clears the neighbour's reservation under the grown
tail and charges the tail eagerly, while a move leaves the neighbour
alone. -/
def lazy_neighbour_model : Model :=
  with_vm_backing [(69632, 4096)] []
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 0 0 8192 0 demo_sp))

/-- On that ledger the in-place gate refuses and the move's gate fits.
The two gates are the in-place charge (`expand_vma_in_place`, :1458-1459) and the move's (`move_vma`, :1281-1282), both `vrm_calc_charge`'s delta (:986).
kernel: mm/mremap.c:vrm_calc_charge,expand_vma_in_place,move_vma@v6.18.46 -/
theorem move_fits_beside_lazy_neighbour :
    mremap_final_budget_b lazy_neighbour_model 65536 4096 65536 8192 = false
    ∧ mremap_move_budget_b lazy_neighbour_model 65536 4096 8192 = true := by
  refine ⟨by decide, by decide⟩

/-- …so the mark fires although a move fits: the over-approximation, on a
reachable state, and the safe direction for a premise.
The Rocq witness is `ov_mark_fires_while_a_move_fits`; the kernel gate it stands for is the in-place commit charge (`expand_vma_in_place`, :1458-1459).
kernel: mm/mremap.c:vrm_calc_charge,expand_vma_in_place@v6.18.46 -/
theorem budget_mark_fires_while_a_move_fits :
    mremap_budget_refused_b 65536 4096 8192 1 lazy_neighbour_model = true := by decide

/-- …and the spec admits that move, the neighbour's reservation untouched:
Linux charges the move the delta of the source alone (`vrm_calc_charge`,
:986), never the neighbour.
no-row: `lazy_neighbour_model` fixes address 65536 beside a lazy neighbour; recorded moves use runtime addresses.
kernel: mm/mremap.c:move_vma,vrm_calc_charge@v6.18.46 -/
theorem lazy_neighbour_move_admitted (i : SyscallInput) :
    mremap_spec 65536 4096 8192 1 i lazy_neighbour_model
      (Ok (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
            [MemCopy.mkCopy 65536 131072 4096] [])
          (with_vm_backing [(69632, 4096)] []
            (fixture (VmMaps.mkVmMapsFull [] [(131072, 8192), (69632, 4096)] [] 0 0 8192 0 demo_sp))) []) := by
  sys_norm

/-- The shapes ahead of the charge never fire it, even on a spent budget:
a shrink, an equal-size call, every argument gate, the declared
`TASK_SIZE` decline, and a source the ledger cannot answer for.
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at@v6.18.46 -/
theorem budget_mark_silent_on_gates :
    mremap_budget_refused_b 65536 4096 4096 1 budget_full_model = false
    ∧ mremap_budget_refused_b 65536 4096 8192 0 budget_full_model = false
    ∧ mremap_budget_refused_b 65537 4096 8192 1 budget_full_model = false
    ∧ mremap_budget_refused_b 65536 4096 0 1 budget_full_model = false
    ∧ mremap_budget_refused_b 65536 4096 (Z_to_bv 64 (two_pow_64 - 4096)) 1 budget_full_model = false
    ∧ mremap_budget_refused_b 65536 0 8192 1 budget_full_model = false
    ∧ mremap_budget_refused_b 131072 4096 8192 1 budget_full_model = false
    ∧ mremap_budget_refused_b 65536 8192 4096 1 (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [] 0 0 0 0 demo_sp)) = false := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The `new_nZ ≤ old_nZ` boundary of the mark is EXACT: an equal-size call
is no budget refusal even on a ledger already over its limit, where a mark
that tested `<` would send it to the charge; Linux meters no call that maps
nothing new (`check_prep_vma` returns at :1676-1677, before `may_expand_vm`,
:1742-1743), and `equal_size_over_budget_iff` pins the decline.
kernel: mm/mremap.c:check_prep_vma,mremap_at@v6.18.46 -/
theorem budget_mark_silent_on_equal_size_over_budget :
    mremap_budget_refused_b 65536 8192 8192 1 over_budget_two_pages = false := by decide

/-- A source of MIXED backing is declined by the arm, so it is no budget
refusal either, whatever the charge of its grow would be: the mark reads
the uniformity gate as the spec does (`mixed_backing_fails_closed`).
kernel: mm/mremap.c:check_prep_vma@v6.18.46 -/
theorem budget_mark_silent_on_mixed_backing :
    mremap_budget_refused_b 65536 8192 12288 1 mixed_backing = false := by decide

/-- The mark's `TASK_SIZE` boundary is strict like the spec's: at a new
length of exactly `TASK_SIZE` the grow is answered (only -ENOMEM,
`exactly_task_size_is_enomem`) and its 2^47-byte charge is refused by both
gates, so the mark FIRES there; a mark that declined at `≤` would be silent
on the one grow the spec forces to -ENOMEM.
kernel: mm/mremap.c:check_mremap_params,check_prep_vma; mm/mmap.c:may_expand_vm@v6.18.46 -/
theorem budget_mark_fires_at_exactly_task_size :
    mremap_budget_refused_b 65536 4096 (Z_to_bv 64 140737488355328) 1 one_map_model = true := by decide

/-- The PROT_NONE-neighbour ledger under a two-page budget: the move's
charge of the re-created mapping, 8192, now fits, so the mark is silent —
which is what pins that the move's charge is of the BACKED view (the
`vm_noaccess` cut in `mremap_move_charge`): charged of `vm_maps` instead it
would be 12288 and the mark would fire. -/
def noaccess_neighbour_roomy : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [(69632, 4096)] 0 0 8192 0 demo_sp)

/-- …silent, as `vrm_calc_charge` charges the delta of the accounted
mapping (:986) and a PROT_NONE neighbour's bytes are never part of it.
kernel: mm/mremap.c:vrm_calc_charge,move_vma@v6.18.46 -/
theorem budget_mark_silent_beside_noaccess_neighbour_within_budget :
    mremap_budget_refused_b 65536 4096 8192 1 noaccess_neighbour_roomy = false := by decide

/-- `mremap_tail` is the tail of a GROW and nothing else: empty on a shrink
shape and at equal sizes, one entry of the delta's length on a grow.  The
spec reaches it only under growth, so no `mremap_spec` pin can tell a guard
that is always true from this one; the helper's own contract is pinned
here instead.
model: `mremap_tail` at a shrink, an equal and a grow shape, decided once; the kernel claim is `inplace_grow_admitted`. -/
theorem tail_is_the_tail_of_a_grow :
    mremap_tail 65536 4096 8192 4096 = []
    ∧ mremap_tail 65536 4096 4096 4096 = []
    ∧ mremap_tail 65536 4096 4096 8192 = [(69632, 4096)] := by
  refine ⟨by decide, by decide, by decide⟩

/-- The moved-pages filter of `mremap_move_charge` keeps a source page only
while its offset is STRICTLY below the new length: read at a shrink shape
(which the mark never passes, so no mark pin can see the filter) the
two-page lazy source keeps one page's charge, not two.
model: `mremap_move_charge` at a shrink shape, decided once; the kernel claim is `lazy_move_relocates_materialized_pages`. -/
theorem move_charge_offset_filter_is_strict :
    mremap_move_charge lazy_two_pages 65536 8192 4096 = 4096 := by decide

/-! ## The dispatcher -/

/-- A successful grow through 216 distinguishes routing from a missing arm.
kernel: mm/mremap.c:expand_vma,expand_vma_in_place@v6.18.46 -/
theorem sysno_216_is_mremap :
    syscall_spec (mremap_in 4096 8192) tight_model
      (Ok (mkEffect 65536 [] [(69632, 4096)])
        (mremap_model_next tight_model 65536 4096 65536 8192) []) := by
  sys_norm

/-- Without FIXED or DONTUNMAP, a4 is ignored even on a successful grow.
no-row: `tight_model` fixes address 65536 with a4 = 0xdeadbeef; recorded grows use runtime addresses and none passes that a4 value.
kernel: mm/mremap.c:vrm_implies_new_addr,expand_vma@v6.18.46 -/
theorem new_address_ignored_without_fixed :
    syscall_spec (SyscallInput.mkInput 216 [65536, 4096, 8192, 1, 0xdeadbeef, 0]
      (fun _ => none) (fun _ => none)) tight_model
      (Ok (mkEffect 65536 [] [(69632, 4096)])
        (mremap_model_next tight_model 65536 4096 65536 8192) []) := by
  sys_norm

/-- Swapping a1 and a2 must change the verdict: the grow is admitted,
whereas the swapped call declines (its two-page source is not tracked).
kernel: mm/mremap.c:do_mremap,check_prep_vma,expand_vma@v6.18.46 -/
theorem dispatcher_reads_old_then_new_length (o : outcome SyscallEffect) :
    syscall_spec (mremap_in 4096 8192) tight_model
      (Ok (mkEffect 65536 [] [(69632, 4096)])
        (mremap_model_next tight_model 65536 4096 65536 8192) [])
    ∧ (syscall_spec (mremap_in 8192 4096) tight_model o ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- This request leaves the modeled surface; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem equal_size_dispatch_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (mremap_in 8192 8192) two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-- This request leaves the modeled surface; see `mremap_spec` (#1426).
kernel: mm/mremap.c:check_mremap_params,check_prep_vma,mremap_at,do_mremap@v6.18.46 -/
theorem dispatcher_shrink_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (mremap_in 8192 4096) two_page_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## The machine-side application of a move's effect

Rocq's five `Run.apply_effect` cases, on the Lean `Run.apply_effect`
(`Run.lean`): the parts of an effect are applied unmaps, then zeros, then
copies, then writes, and a copy reads the PRE-EFFECT snapshot of memory —
the order `move_vma` has, page tables moved by `copy_vma_and_data` (:1208)
before `unmap_source_vma` drops the source (:1312), which is why
`mremap_move_effect` may list the copy's source inside `eff_unmaps`. -/

open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.Run

/-- Three bytes of memory: two in the source page at 65536, one far away. -/
def mremap_snapshot_mem (a : word) : Option byte :=
  if bv_eqb a 65536 then some 90
  else if bv_eqb a 65537 then some 165
  else if bv_eqb a 196608 then some 51
  else none

/-- A machine state holding exactly that memory. -/
def mremap_snapshot_ms : machine_state :=
  { ms_regs := bvmap_empty, ms_fregs := bvmap_empty, ms_pc_val := 0,
    ms_svc_pending := none, ms_resv := none, ms_fcsr := 0,
    ms_mem := mremap_snapshot_mem, ms_rom := fun _ => none }

/-- The move of the one page at 65536 to 131072, grown by a page. -/
def mremap_snapshot_effect : SyscallEffect :=
  SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
    [MemCopy.mkCopy 65536 131072 4096] []

/-- Applied to that state, the move copies the source's bytes to the
destination before the source is unmapped, zero-fills the grown page and
leaves unrelated memory alone — the kernel's order: `move_page_tables`
carries the PTEs (:1208) and only then `unmap_source_vma` runs (:1312).
kernel: mm/mremap.c:move_vma,copy_vma_and_data,unmap_source_vma@v6.18.46 -/
theorem copy_reads_pre_effect_snapshot :
    (apply_effect mremap_snapshot_ms mremap_snapshot_effect).ms_mem 131072 = some 90
    ∧ (apply_effect mremap_snapshot_ms mremap_snapshot_effect).ms_mem 131073 = some 165
    ∧ (apply_effect mremap_snapshot_ms mremap_snapshot_effect).ms_mem 65536 = none
    ∧ (apply_effect mremap_snapshot_ms mremap_snapshot_effect).ms_mem 135168 = some 0
    ∧ (apply_effect mremap_snapshot_ms mremap_snapshot_effect).ms_mem 196608 = some 51 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Zeros run after unmaps: a range both unmapped and zeroed reads as zero.
model: the order of `Run.apply_effect`'s parts, decided once; the kernel claim is `copy_reads_pre_effect_snapshot`. -/
theorem apply_effect_zeros_run_after_unmaps :
    (apply_effect mremap_snapshot_ms
      (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [] [])).ms_mem 65536 = some 0 := by
  decide

/-- Copies run after zeros: a destination both zeroed and copied into holds
the copied byte.
model: the order of `Run.apply_effect`'s parts, decided once; the kernel claim is `copy_reads_pre_effect_snapshot`. -/
theorem apply_effect_copies_run_after_zeros :
    (apply_effect mremap_snapshot_ms
      (SyscallEffect.mkEffectU 0 [] [(131072, 4096)] [] [MemCopy.mkCopy 65536 131072 4096] [])).ms_mem 131072
      = some 90 := by
  decide

/-- Writes run after copies: a byte both copied and written holds the
written value.
model: the order of `Run.apply_effect`'s parts, decided once; the kernel claim is `copy_reads_pre_effect_snapshot`. -/
theorem apply_effect_writes_run_after_copies :
    (apply_effect mremap_snapshot_ms
      (SyscallEffect.mkEffectU 0 [(131072, [7])] [] [] [MemCopy.mkCopy 65536 131072 4096] [])).ms_mem 131072
      = some 7 := by
  decide

/-- A copy's SOURCE survives being unmapped and zeroed in the same effect:
the copy reads the snapshot, so the destination gets the source's byte and
the source range reads as zero afterwards.
model: the order of `Run.apply_effect`'s parts, decided once; the kernel claim is `copy_reads_pre_effect_snapshot`. -/
theorem apply_effect_copy_source_survives_unmap_and_zero :
    (apply_effect mremap_snapshot_ms
      (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [MemCopy.mkCopy 65536 131072 4096] [])).ms_mem 131072
      = some 90
    ∧ (apply_effect mremap_snapshot_ms
      (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [MemCopy.mkCopy 65536 131072 4096] [])).ms_mem 65536
      = some 0 := by
  refine ⟨by decide, by decide⟩

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mremap
