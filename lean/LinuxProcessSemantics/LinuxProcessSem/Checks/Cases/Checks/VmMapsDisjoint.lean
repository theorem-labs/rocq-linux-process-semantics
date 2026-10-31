import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mmap

/-! # Checks.Cases.Checks.VmMapsDisjoint — the ledger invariant, exercised (ticket K4)

Pins over `Checks.VmMapsDisjoint` and its part `Checks.VmMapsDisjoint.Arms`,
the twin of `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`.  The Rocq
tree has no check file for it — its own examples sit in the file, and their
twins sit in the Lean twin — so this file mirrors nothing: these are the
Lean tree's tests for what the twin ports, in the place every pin in this
tree lives so that `tools/check_lean_pins.py` and
`tools/check_lean_pin_evidence.py` read them.  Not part of the trusted
specification.

WHAT IS UNDER TEST is a claim about the model, not about a syscall: that
no PAGE-ALIGNED byte of `vm_maps` has two owners in any reachable state,
while an arbitrary byte may.  The kernel fact behind the "may" is on the
twin's header — `SYSCALL_DEFINE1(brk)` (mm/mmap.c:153-158, Linux v6.18.46,
commit 1f99e9ab748f) moves the break within a page with no address-space
test — and every pin here is a closed computation over the model's own
ledgers, so each carries a `model:` line and no kernel citation: inventing
one would be the fault the evidence tool exists to refuse.

Each decision the twin ports gets a positive and a negative pin: the
half-open ownership test, the owner count, the invariant and its
companion (each conjunct refuted on its own), the distinct-byte measure,
base uniqueness at an aligned base (and the statement the alignment
hypothesis refuses), the witness ledgers' fields, the start state, the
frame machinery arm by arm — every `vm_step` shape on one fixture, and
`vm_done` on the hypothesis it exists for and on one it does not fit, with
the default rule's message pinned — `arm_preserves_vm`, the lookup in the
form `Checks/VmMapsDisjoint/Arms.lean` states the dispatcher-level fact, and the alternation
itself: run over a two-arm fixture table, then over the same table with
one arm left uncovered so that the fallback's message is pinned rather
than described, and anchored to `checked_table` by name. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.VmMapsDisjoint

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch

section Ownership

/-! ## `owns_b` and `owners`: who owns a byte

The interval is half-open, as every range in the ledger is: the base is
owned, the byte at base plus size is not.  The counts are read off the
overlap ledger PART 1 reaches, `[(67536, 100), (65536, 4096)]`. -/

/-- The base byte is owned.
model: `owns_b` on a closed pair and address -/
theorem owns_b_admits_the_base : owns_b (65536, 4096) 65536 = true := by decide

/-- …and so is the last byte of the range.
model: `owns_b` on a closed pair and address -/
theorem owns_b_admits_the_last_byte : owns_b (65536, 4096) 69631 = true := by decide

/-- The byte AT base plus size is not: the interval is half-open, which is
what lets two adjacent entries own disjoint sets.
model: `owns_b` on a closed pair and address -/
theorem owns_b_refuses_the_end : owns_b (65536, 4096) 69632 = false := by decide

/-- Nor is the byte below the base.
model: `owns_b` on a closed pair and address -/
theorem owns_b_refuses_below_the_base : owns_b (65536, 4096) 65535 = false := by decide

/-- The brk grant's first byte, inside the step-5 mapping, has TWO owners
in the overlap ledger: this is the byte-level overlap PART 1 reaches.
model: `owners` over `wit_overlap`'s ledger -/
theorem overlap_byte_has_two_owners : owners (m_vmmaps wit_overlap).vm_maps 67536 = 2 := by
  decide

/-- The page-aligned byte 65536 has one owner in the same ledger.
model: `owners` over `wit_overlap`'s ledger -/
theorem aligned_byte_has_one_owner : owners (m_vmmaps wit_overlap).vm_maps 65536 = 1 := by
  decide

/-- The page-aligned byte 69632, the end of the step-5 mapping, has none.
model: `owners` over `wit_overlap`'s ledger -/
theorem end_byte_has_no_owner : owners (m_vmmaps wit_overlap).vm_maps 69632 = 0 := by decide

end Ownership

section Invariant

/-! ## `page_owner_unique`, `sizes_nonzero`, `maps_wf`, `vm_wf`

The invariant is stated over every `Int`, so it is not decided: the
positive pins are proofs on the two ledgers PART 1 reaches, the refutations
are ledgers a page-aligned base is doubled in. -/

/-- The overlap ledger IS page-owner-unique: its doubly owned bytes,
`[67536, 67636)`, contain no multiple of 4096.  This is the whole point of
PART 2 — the byte-level overlap is real and the page-level invariant
survives it.
model: `page_owner_unique` on `wit_overlap`'s ledger -/
theorem overlap_ledger_is_page_owner_unique :
    page_owner_unique (m_vmmaps wit_overlap).vm_maps := by
  intro p hp
  have e1 : bv_unsigned (67536 : word) = 67536 := by decide
  have e2 : bv_unsigned (100 : word) = 100 := by decide
  have e3 : bv_unsigned (65536 : word) = 65536 := by decide
  have e4 : bv_unsigned (4096 : word) = 4096 := by decide
  simp only [page_size] at hp
  show owners [((67536 : word), (100 : word)), (65536, 4096)] p ≤ 1
  simp only [owners, owns_b, e1, e2, e3, e4, Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero]
  split <;> split <;> omega

/-- The duplicate-base ledger of step 8 is well formed too: the doubled
base 67536 is not page aligned, and 65536 and 69632 each have at most one
owner.
model: `vm_wf` on `wit_s8`'s ledger -/
theorem duplicate_base_ledger_is_vm_wf : vm_wf (m_vmmaps wit_s8) := by
  unfold vm_wf maps_wf
  refine ⟨?_, ?_⟩
  · unfold sizes_nonzero
    decide
  · intro p hp
    have e1 : bv_unsigned (67536 : word) = 67536 := by decide
    have e2 : bv_unsigned (100 : word) = 100 := by decide
    have e3 : bv_unsigned (67526 : word) = 67526 := by decide
    have e4 : bv_unsigned (10 : word) = 10 := by decide
    have e5 : bv_unsigned (65536 : word) = 65536 := by decide
    have e6 : bv_unsigned (1990 : word) = 1990 := by decide
    have e7 : bv_unsigned (2096 : word) = 2096 := by decide
    simp only [page_size] at hp
    show owners [((67536 : word), (100 : word)), (67526, 10), (65536, 1990), (67536, 2096)] p ≤ 1
    simp only [owners, owns_b, e1, e2, e3, e4, e5, e6, e7, Bool.and_eq_true, decide_eq_true_eq,
      Nat.add_zero]
    split <;> split <;> split <;> split <;> omega

/-- The ledger every refutation below uses: the page-aligned base 65536
recorded twice, which no reachable state holds. -/
def doubled_vm : VmMaps := wit_vm [(65536, 4096), (65536, 100)] 65536 69632 wit_limit

/-- A doubled PAGE-ALIGNED base is refused: 65536 has two owners.
model: `page_owner_unique` on a hand-built ledger -/
theorem doubled_aligned_base_is_not_page_owner_unique :
    ¬ page_owner_unique [((65536 : word), (4096 : word)), (65536, 100)] := by
  intro h
  have h1 := h 65536 (by decide)
  have h2 : owners [((65536 : word), (4096 : word)), (65536, 100)] 65536 = 2 := by decide
  omega

/-- An empty entry is refused by the companion: it would own nothing and
still answer `map_has`.
model: `sizes_nonzero` on a hand-built ledger -/
theorem empty_entry_is_not_sizes_nonzero : ¬ sizes_nonzero [((65536 : word), (0 : word))] := by
  intro h
  exact h (65536, 0) List.mem_cons_self (by decide)

/-- …so the doubled ledger is not `vm_wf`, whatever its breaks say.
model: `vm_wf` on a hand-built ledger -/
theorem doubled_vm_is_not_vm_wf : ¬ vm_wf doubled_vm := by
  intro h
  have h' : sizes_nonzero doubled_vm.vm_maps ∧ page_owner_unique doubled_vm.vm_maps := h
  exact doubled_aligned_base_is_not_page_owner_unique h'.2

/-- The invariant reads EVERY page, not every other one: the first page
above zero, doubled, has two owners at 4096 and is refused too.  The
doubled ledger above cannot tell, since 65536 is a multiple of every power
of two up to it.
model: `page_owner_unique` on a hand-built ledger at base 4096 -/
theorem doubled_first_page_is_not_page_owner_unique :
    ¬ page_owner_unique [((4096 : word), (4096 : word)), (4096, 100)] := by
  intro h
  have h1 := h 4096 (by decide)
  have h2 : owners [((4096 : word), (4096 : word)), (4096, 100)] 4096 = 2 := by decide
  omega

/-- An empty entry ALONE makes a ledger not `vm_wf`.  This isolates the
`sizes_nonzero` conjunct, which the doubled ledger never reaches: an empty
entry owns nothing, so a `maps_wf` that dropped the conjunct would accept
this ledger.
model: `vm_wf` on a hand-built ledger with one empty entry -/
theorem empty_entry_is_not_vm_wf : ¬ vm_wf (wit_vm [(65536, 0)] 65536 65536 wit_limit) :=
  fun h => empty_entry_is_not_sizes_nonzero h.1

/-- Step 5's grant is `maps_wf_cons_free` on the empty ledger: one page,
free by vacuity, over nothing — the theorem's hypotheses met on a
reachable ledger.
model: `maps_wf_cons_free` instantiated on `wit_s5`'s ledger -/
theorem step5_grant_is_wf : maps_wf (m_vmmaps wit_s5).vm_maps :=
  maps_wf_cons_free [] 65536 4096
    ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ => Nat.zero_le 1⟩ (by decide) (by decide)

/-- Step 6 is `maps_subtract` of the shrink's ten bytes from step 5's
ledger, and the split it leaves — the left remnant, then the right one
based at the old break — is the one `wit_s6` records.
model: `maps_subtract` over `wit_s5`'s ledger against `wit_s6`'s -/
theorem step6_is_a_subtract :
    maps_subtract (m_vmmaps wit_s5).vm_maps 67526 67536 = (m_vmmaps wit_s6).vm_maps := by
  decide

end Invariant

section OwnedBytes

/-! ## `owned_bytes`: the distinct-byte measure

The twin carries Rocq's five examples over the overlap and duplicate-base
ledgers; these pin the measure's own edges. -/

/-- No entry, no owned byte, over a full page.
model: `owned_bytes` on the empty ledger -/
theorem owned_bytes_of_nothing : owned_bytes [] 65536 4096 = 0 := by decide +kernel

/-- One page-sized entry owns exactly its page.
model: `owned_bytes` on a one-entry ledger -/
theorem owned_bytes_exact_on_one_entry :
    owned_bytes [((65536 : word), (4096 : word))] 65536 4096 = 4096 := by decide +kernel

/-- The window `[65535, 65537)` straddles the base: one of its two bytes is
owned, so the measure is half-open where `owns_b` is.
model: `owned_bytes` on a one-entry ledger -/
theorem owned_bytes_is_half_open_at_the_base :
    owned_bytes [((65536 : word), (4096 : word))] 65535 2 = 1 := by decide

/-- …and the window `[69631, 69633)` straddles the end the same way.
model: `owned_bytes` on a one-entry ledger -/
theorem owned_bytes_stops_at_the_end :
    owned_bytes [((65536 : word), (4096 : word))] 69631 2 = 1 := by decide

end OwnedBytes

section BaseUniqueness

/-! ## `base_entry_unique`: one entry per aligned base

Read on the duplicate-base ledger of step 8, where the aligned base 65536
names one entry and the unaligned base 67536 names two.  The second pin
is what shows the alignment hypothesis is load-bearing: drop it and the
theorem is false on a reachable state. -/

/-- At the page-aligned base 65536 the ledger holds exactly the entry
`map_has` matched, by the theorem.
model: `base_entry_unique` instantiated on `wit_s8`'s ledger -/
theorem aligned_base_names_one_entry :
    (m_vmmaps wit_s8).vm_maps.filter (fun q => bv_eqb q.1 65536) = [(65536, 1990)] :=
  base_entry_unique _ _ _ duplicate_base_ledger_is_vm_wf (by decide) (by decide)

/-- …and the computation agrees with the theorem.
model: a closed computation over `wit_s8`'s ledger -/
theorem aligned_base_names_one_entry_computed :
    (m_vmmaps wit_s8).vm_maps.filter (fun q => bv_eqb q.1 65536) = [(65536, 1990)] := by
  decide

/-- At the UNALIGNED base 67536 the same ledger holds two entries, so the
statement `base_entry_unique` makes would be false there: the alignment
hypothesis is what excludes this state, and PART 1 shows the state is
reachable.
model: a closed computation over `wit_s8`'s ledger -/
theorem unaligned_base_names_two_entries :
    (m_vmmaps wit_s8).vm_maps.filter (fun q => bv_eqb q.1 67536)
      = [(67536, 100), (67536, 2096)] := by
  decide

/-- The doubled base really is unaligned, so the two pins above are about
the hypothesis and not about a counterexample to the theorem.
model: `page_size` arithmetic on a closed address -/
theorem the_doubled_base_is_unaligned : bv_unsigned (67536 : word) % page_size ≠ 0 := by decide

/-- The ledger's budget identity, as a closed computation: dropping the
aligned entry lowers `live_bytes` by exactly its 1990 bytes.  This is
ledger arithmetic, not a kernel claim — Linux's `munmap` of that range
releases the whole page.
model: a closed computation over `wit_s8`'s ledger -/
theorem munmap_of_the_aligned_entry_returns_its_bytes :
    live_bytes (m_vmmaps wit_s8).vm_maps
      = bv_unsigned (1990 : word) + live_bytes (map_remove (m_vmmaps wit_s8).vm_maps 65536) := by
  decide

/-- The same identity by the theorem, so that a vacuous
`munmap_returns_matched_bytes` could not pass beside the computation.
model: `munmap_returns_matched_bytes` instantiated on `wit_s8`'s ledger -/
theorem munmap_of_the_aligned_entry_returns_its_bytes_by_the_theorem :
    live_bytes (m_vmmaps wit_s8).vm_maps
      = bv_unsigned (1990 : word) + live_bytes (map_remove (m_vmmaps wit_s8).vm_maps 65536) :=
  munmap_returns_matched_bytes _ _ _ duplicate_base_ledger_is_vm_wf (by decide) (by decide)

/-- The theorem WITHOUT its alignment hypothesis is false, on this very
ledger: at 67536 `map_has` matches and the filter names two entries.  The
two computations above show the counterexample; this states it as the
refutation.
model: `maps_wf`, `map_has` and the base filter on `wit_s8`'s ledger -/
theorem base_entry_unique_needs_alignment :
    ¬ ∀ (maps : List (word × word)) (a n : word), maps_wf maps → map_has maps a n = true →
        maps.filter (fun q => bv_eqb q.1 a) = [(a, n)] :=
  fun h =>
    absurd (h (m_vmmaps wit_s8).vm_maps 67536 100 duplicate_base_ledger_is_vm_wf (by decide))
      (by decide)

/-- …and the budget identity fails there too: `map_remove` at the
unaligned base drops both entries, 2196 bytes, where `map_has` matched 100.
model: `live_bytes` and `map_remove` on `wit_s8`'s ledger -/
theorem munmap_at_the_unaligned_base_is_not_matched :
    live_bytes (m_vmmaps wit_s8).vm_maps
      ≠ bv_unsigned (100 : word) + live_bytes (map_remove (m_vmmaps wit_s8).vm_maps 67536) := by
  decide

end BaseUniqueness

section StartState

/-! ## `init_model_vm_wf`: the ledger starts empty -/

/-- The witness start state is well formed, by the theorem.
model: `init_model_vm_wf` at `wit_s0`'s arguments -/
theorem witness_start_is_vm_wf : vm_wf (m_vmmaps wit_s0) := init_model_vm_wf _ _ _ _ _ _

/-- The theorem is about `init_model`'s EMPTY ledger and not about the
witness ledger builder: the same start state with the doubled ledger
installed is not well formed.
model: `vm_wf` on `with_vmmaps doubled_vm wit_s0` -/
theorem doubled_start_is_not_vm_wf : ¬ vm_wf (m_vmmaps (with_vmmaps doubled_vm wit_s0)) :=
  doubled_vm_is_not_vm_wf

/-- The ledger builder takes the start break before the break, in
`mkVmMapsFull`'s order: after step 1 the break has grown to 69632 and the
start break has not moved.  Nothing else reads these two fields until
K9's steps do.
model: `wit_vm`'s break fields on `wit_s1` -/
theorem witness_step1_moves_the_break_only :
    (m_vmmaps wit_s1).vm_start_brk = 65536 ∧ (m_vmmaps wit_s1).vm_brk = 69632 := by
  decide

/-- The start state's stack top is the window's low bound, and `wit_vm`
carries it into every later ledger: `alloc_top` reads it, so the
placement gate K9's step 5 runs through depends on it.
model: `vm_init_sp` of `wit_s0` and of `wit_s5` -/
theorem witness_stack_top_is_the_window_low :
    (m_vmmaps wit_s0).vm_init_sp = Z_to_bv 64 sp_window_lo
    ∧ (m_vmmaps wit_s5).vm_init_sp = Z_to_bv 64 sp_window_lo := ⟨rfl, rfl⟩

/-- The witness input is a `brk` call: its number is the one the registry's
`brk_arm` answers to, so the K9 step examples, which run `brk_in` through
the dispatcher, reach `brk_spec` and no other arm.  Nothing else in this
tree reads that literal until then.
model: `brk_in`'s syscall number against `Sys.Registry.Mm.Mmap.brk_arm` -/
theorem brk_in_is_a_brk_call :
    bv_unsigned (brk_in 0).in_sysno = Sys.Registry.Mm.Mmap.brk_arm.sa_no := by
  decide

end StartState

section Frame

/-! ## The frame machinery: `check_ret_only_model` and `vm_frame`

Exercised on the exit fixture of `Checks/Cases/Checks/Sys/Dispatch.lean`,
whose checker is `check_ret_only` over a `with_halted` model — a real
checker shape, and the one every `*_frame` lemma of the Rocq file starts
from. -/

/-- The return-only acceptor hands back the model it was given.
model: `check_ret_only_model` on a closed effect and the `wit_s1` model -/
theorem check_ret_only_model_on_a_closed_call (m' : Model) (evs : List event)
    (h : check_ret_only (mkEffect 0 [] []) 0 wit_s1 [] = CheckOk m' evs) : m' = wit_s1 :=
  check_ret_only_model h

/-- …and it does accept that call, so the pin above is not vacuous.
model: `check_ret_only` on a closed effect -/
theorem check_ret_only_accepts_the_bare_return :
    check_ret_only (mkEffect 0 [] []) 0 wit_s1 [] = CheckOk wit_s1 [] :=
  (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- A write in the effect is refused outright, so no model comes back to
be framed.
model: `check_ret_only` on a closed effect -/
theorem check_ret_only_refuses_a_write :
    check_ret_only (mkEffect 0 [(0, [0])] []) 0 wit_s1 [] = CheckReject := rfl

/-- The exit fixture's frame lemma, closed by `vm_frame` alone: the
wrapper arm hands the model back and `rfl` reads `m_vmmaps` through
`with_halted`.  This is the shape every `*_frame` lemma of a C ticket takes.
model: `vm_frame` on the exit fixture's checker -/
theorem fixture_check_exit_frame (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : fixture_check_exit code eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold fixture_check_exit at h
  vm_frame h

/-- A checker that installs a mapping: the return-only acceptor over a
model whose ledger has been replaced. -/
def fixture_check_moves (eff : SyscallEffect) (m : Model) : check_result :=
  check_ret_only eff 0 (with_vmmaps (wit_vm [(65536, 4096)] 65536 69632 wit_limit) m) []

/-- …and it is NOT frame: run from the empty start ledger it returns a
model with one entry, so the frame statement fails on a concrete call.
This is what a `*_frame` lemma would refuse to close for `mmap` or `brk`,
which is why those arms write `*_preserves` lemmas instead.
model: `fixture_check_moves` on `wit_s0` -/
theorem fixture_check_moves_is_not_frame :
    ¬ (∀ eff m m' evs,
        fixture_check_moves eff m = CheckOk m' evs → m_vmmaps m' = m_vmmaps m) := by
  intro h
  have hok : fixture_check_moves (mkEffect 0 [] []) wit_s0
      = CheckOk (with_vmmaps (wit_vm [(65536, 4096)] 65536 69632 wit_limit) wit_s0) [] :=
    (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  have hm := congrArg VmMaps.vm_maps (h _ _ _ _ hok)
  exact absurd hm (by decide)

/-- A checker built from every shape `vm_step` knows and nothing else: a
`match` on the effect, a `let`, an `if`, the three copy-in wrappers and
the return-only acceptor with a copy-in ledger, over a `with_halted`
model.  No real checker looks like this; each of its layers is one arm of
`vm_step`, so a `vm_frame` that closes its frame lemma has run every arm. -/
def fixture_check_stack (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU r [] [] [] [] [] =>
      let m1 := with_halted r m
      if bv_eqb r 0 then
        check_copyins [] eff
          (check_copyin_prefix [] eff
            (check_copyins_after [] eff (check_ret_only_copyins [] eff r m1 [])))
      else CheckReject
  | _ => CheckReject

/-- …and `vm_frame` closes it alone: `split` opens the `match` and the
`if`, `dsimp` inlines the `let`, the three copy-in wrappers and the
return-only acceptor each hand their result back, `cases` closes every
`CheckReject` branch, and `rfl` reads `m_vmmaps` through `with_halted`.
model: `vm_frame` over a checker exercising every arm of `vm_step` -/
theorem fixture_check_stack_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : fixture_check_stack eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold fixture_check_stack at h
  vm_frame h

/-- …and the fixture does accept a call, so the frame lemma above is not
about an empty set of runs.
model: `fixture_check_stack` on a closed effect and the `wit_s1` model -/
theorem fixture_check_stack_accepts_the_bare_return :
    fixture_check_stack (mkEffect 0 [] []) wit_s1 = CheckOk (with_halted 0 wit_s1) [] := rfl

end Frame

section VmDone

/-! ## `vm_done` and `vm_frame2`: the extension point

`check_efault_or` is the hypothesis `vm_done` exists for: not a
constructor, not one of the five wrappers, and closed to `split`, so the
`vm_step` loop stops at it.  The twin registers `check_efault_or_frame`
as the first rule after the failing default; these pins run the rule, run
`vm_frame2` through it, and pin what the default says when no rule fits. -/

/-- The first registered rule closes the hypothesis it was registered for.
model: `vm_done` through `check_efault_or_frame` on a closed fallback -/
theorem vm_done_closes_the_efault_acceptor (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_efault_or 5 eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_done h

/-- A checker whose accepting path ends in the acceptor, behind a `match`
`vm_step` opens and a `with_halted` `rfl` reads through. -/
def fixture_check_efault (eff : SyscallEffect) (m : Model) : check_result :=
  match m_halted m with
  | some _ => CheckReject
  | none => check_efault_or 5 eff (with_halted 0 m)

/-- …and `vm_frame2` closes its frame lemma: the loop splits the `match`,
`cases` closes the rejecting branch, `vm_step` has nothing for the acceptor
and `vm_done` closes it through the rule.  `vm_frame` alone cannot: the
rule is the only way through.
model: `vm_frame2` over a `match`-gated `check_efault_or` -/
theorem fixture_check_efault_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : fixture_check_efault eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold fixture_check_efault at h
  vm_frame2 h

/--
error: vm_done: no wrapper frame lemma applies to this hypothesis
eff : SyscallEffect
m m' : Model
evs : List event
h : check_ret_only eff 0 m [] = CheckOk m' evs
⊢ m_vmmaps m' = m_vmmaps m
-/
#guard_msgs in
/-- THE DEFAULT RULE SPEAKS when no registered rule fits: the return-only
acceptor is `vm_step`'s business and `check_efault_or_frame` does not
apply, so what the build prints is the default's message, and the goal.
model: `vm_done` on a hypothesis no wrapper rule fits -/
example (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_ret_only eff 0 m [] = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  vm_done h

end VmDone

section ArmPreserves

/-! ## `arm_preserves_vm`: what one arm owes

Two arms discharge it — the exit fixture through its frame lemma, the
fail-closed fixture through a checker that never accepts — and one arm
built to break the ledger does not, which is what makes the obligation an
obligation. -/

/-- The exit fixture preserves the invariant: `arm_unfold` recovers the
plain checker and the frame lemma closes the rest.  This is the arm-level
fact the generated alternation in `Checks/VmMapsDisjoint/Arms.lean` names.
model: `arm_preserves_of_frame` over `fixture_check_exit_frame` -/
theorem fixture_arm_exit_preserves_vm : arm_preserves_vm fixture_arm_exit :=
  arm_preserves_of_frame _ (fun _ _ _ _ _ h => by
    simp only [arm_unfold] at h
    exact fixture_check_exit_frame _ _ _ _ _ h)

/-- The fail-closed fixture preserves it vacuously: its checker never
answers `CheckOk`, and `vm_frame` closes the constructor mismatch.
model: `arm_preserves_of_frame` over a never-accepting checker -/
theorem fixture_arm_unmodeled_preserves_vm : arm_preserves_vm fixture_arm_unmodeled :=
  arm_preserves_of_frame _ (fun _ _ _ _ _ h => by
    rw [fixture_arm_unmodeled_declines] at h
    vm_frame h)

/-- A spec that installs the doubled ledger on every call, with the bare
return 0.  Internally consistent — its checker and witness meet all five
obligations — and wrong about the ledger. -/
def breaks_ledger_spec : Sys SyscallEffect :=
  fun _ m o => o = Ok (mkEffect 0 [] []) (with_vmmaps doubled_vm m) []

/-- The arm over it.  Every field is discharged the way the exit fixture's
are, so the record cannot tell it apart from a good arm: the ledger
obligation is EXTRA, and the generated `Checks/VmMapsDisjoint/Arms.lean` is where it is imposed. -/
def fixture_arm_breaks_ledger : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 0 breaks_ledger_spec
  ca_check := fun _ eff m => check_ret_only eff 0 (with_vmmaps doubled_vm m) []
  ca_witness := fun _ m => Ok (mkEffect 0 [] []) (with_vmmaps doubled_vm m) []
  ca_sound_ok := by
    intro i eff m m' evs h
    obtain ⟨heff, hm', hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    subst heff
    subst hm'
    subst hevs
    exact rfl
  ca_sound_unmodeled := by
    intro i eff m h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  ca_complete_ok := by
    intro i eff m m' evs h
    have h' : (Ok eff m' evs : outcome SyscallEffect)
        = Ok (mkEffect 0 [] []) (with_vmmaps doubled_vm m) [] := h
    injection h' with heff hm' hevs
    subst heff
    subst hm'
    subst hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  ca_complete_unmodeled := by
    intro i m eff h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect 0 [] []) (with_vmmaps doubled_vm m) [] := h
    cases h'
  ca_receptive := by
    intro i m
    exact rfl

/-- …and it does not preserve the invariant: from the well-formed start
state it accepts a call whose post-state is the doubled ledger.  So
`arm_preserves_vm` refuses an arm the five fields accept, which is the
reason `checked_table_preserves_vm` exists beside `checked_table`.
model: `arm_preserves_vm` on `fixture_arm_breaks_ledger` at `wit_s0` -/
theorem fixture_arm_breaks_ledger_does_not_preserve :
    ¬ arm_preserves_vm fixture_arm_breaks_ledger := by
  intro h
  have hok : fixture_arm_breaks_ledger.ca_check (brk_in 0) (mkEffect 0 [] []) wit_s0
      = CheckOk (with_vmmaps doubled_vm wit_s0) [] :=
    (check_ret_only_ok_iff (mkEffect 0 [] []) 0 (with_vmmaps doubled_vm wit_s0) []
      (with_vmmaps doubled_vm wit_s0) []).mpr ⟨rfl, rfl, rfl⟩
  exact doubled_start_is_not_vm_wf (h _ _ _ _ _ hok witness_start_is_vm_wf)

end ArmPreserves

section Lookup

/-! ## `lookup_ca_In`: the arm found is an arm of the table -/

/-- The arm the lookup finds at 93 is a member of the fixture table.
model: `lookup_ca_In` at the fixture table's lookup pin -/
theorem lookup_finds_a_member : fixture_arm_exit ∈ fixture_table :=
  lookup_ca_In fixture_table 93 fixture_arm_exit lookup_ca_finds_93

/-- The lookup never hands back an arm from outside the table: no number
finds `fixture_arm_breaks_ledger` in the fixture table, because
`lookup_ca_In` would then place it there, and it is neither of the two
members — its number is 0 where `fixture_arm_exit`'s is 93, and its
witness answers where `fixture_arm_unmodeled`'s declines.  This is the
mistake that matters for the alternation: an arm judged by
`checked_table_preserves_vm` that is not one of the arms it split over.
model: `lookup_ca_In` on the fixture table and an arm outside it -/
theorem lookup_never_invents_an_arm :
    ¬ ∃ n, lookup_ca fixture_table n = some fixture_arm_breaks_ledger := by
  intro ⟨n, hn⟩
  have hin := lookup_ca_In fixture_table n _ hn
  simp only [fixture_table, List.mem_cons, List.mem_nil_iff, or_false] at hin
  rcases hin with h | h
  · have h93 := congrArg ca_no h
    rw [ca_no_fixture_arm_exit] at h93
    exact absurd h93 (by decide)
  · have hw : (Ok (mkEffect 0 [] []) (with_vmmaps doubled_vm wit_s0) [] : outcome SyscallEffect)
        = Unmodeled :=
      congrArg (fun c : CheckedArm => c.ca_witness (brk_in 0) wit_s0) h
    cases hw

end Lookup

section Alternation

/-! ## The alternation, run on a table with arms in it

`checked_table` was empty until K6a registered `exit` and `exit_group`,
and the ledger alternation held its `| skip` alone; with arms in it,
the real alternation still cannot be run in the failing direction without
breaking the build, so the three pins below run the same split, the same shape of alternation and the same
fallback step over the two-arm fixture table: once with every arm
covered; once with the fail-closed arm's alternative removed, where the
build error the fallback raises is pinned to the letter; and once with
that alternative present but BEHIND the `| skip`, where the same error
fires because `skip` took the goal first.  The second is the negative
test the acceptance asks for ("removing one arm's frame lemma fails the
build naming the arm") and the third is its companion ("an alternative
listed behind the fail never runs"), both made committed tests rather
than manual steps: the `example` fails, `#guard_msgs` captures exactly
that failure and nothing else, and the guard would itself fail if the
message drifted or if the alternation stopped failing on an uncovered
arm. -/

/-- Both fixture arms are covered, so the split closes every goal through
the alternation and the fallback step finds no goal to fail on.
model: `vm_arms_split` and the `first` alternation over `fixture_table` -/
theorem fixture_table_preserves_vm : ∀ c ∈ fixture_table, arm_preserves_vm c := by
  vm_arms_split fixture_table
  all_goals first
    | exact fixture_arm_exit_preserves_vm
    | exact fixture_arm_unmodeled_preserves_vm
    | skip
  all_goals vm_arm_uncovered

/-- Rocq's `check_syscall_preserves_vm_wf` in the lookup form
`Checks/VmMapsDisjoint/Arms.lean` states it, over the fixture table:
whatever arm the lookup finds, an accepting run of it preserves the
invariant.  The composition is the one
`lookup_ca_preserves_vm_wf` makes, on a table with arms in it.
model: `lookup_ca_In` and `fixture_table_preserves_vm` composed as `Checks/VmMapsDisjoint/Arms.lean` composes them -/
theorem fixture_lookup_preserves_vm_wf (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (c : CheckedArm)
    (hlk : lookup_ca fixture_table (bv_unsigned i.in_sysno) = some c)
    (h : c.ca_check i eff m = CheckOk m' evs) (hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') :=
  fixture_table_preserves_vm c (lookup_ca_In fixture_table _ c hlk) i eff m m' evs h hwf

/-- …and the statement is about the arm FOUND: with the ledger-breaking
arm in a table at number 0, the lookup at 0 finds it and the fact fails.
model: the lookup form over a table holding `fixture_arm_breaks_ledger` -/
theorem a_breaking_arm_in_the_table_breaks_the_lookup_fact :
    ¬ ∀ c, lookup_ca [fixture_arm_exit, fixture_arm_breaks_ledger] 0 = some c →
        arm_preserves_vm c :=
  fun h => fixture_arm_breaks_ledger_does_not_preserve (h _ rfl)

/--
error: checked_table_preserves_vm has no case for this dispatcher arm.
Give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves one
(it writes vm_maps), state `arm_<name>_preserves_vm : arm_preserves_vm arm_<name>` from
it in the arm's file under Checks/Arms/, and let tools/gen_lean_checked.py render
`| exact arm_<name>_preserves_vm` ABOVE the alternation's closing `| skip`;
an alternative listed behind that line never runs.  The uncovered goal, which names
the arm:
⊢ arm_preserves_vm fixture_arm_unmodeled
-/
#guard_msgs in
/-- THE FALLBACK FIRES, and names the arm: the fail-closed fixture's
alternative is missing, and the message above is the whole of what the
build prints.  The covered arm's goal closes silently, so exactly one error
is captured.
model: `vm_arm_uncovered` over `fixture_table` with one alternative dropped -/
example : ∀ c ∈ fixture_table, arm_preserves_vm c := by
  vm_arms_split fixture_table
  all_goals first
    | exact fixture_arm_exit_preserves_vm
    | skip
  all_goals vm_arm_uncovered

/--
error: checked_table_preserves_vm has no case for this dispatcher arm.
Give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves one
(it writes vm_maps), state `arm_<name>_preserves_vm : arm_preserves_vm arm_<name>` from
it in the arm's file under Checks/Arms/, and let tools/gen_lean_checked.py render
`| exact arm_<name>_preserves_vm` ABOVE the alternation's closing `| skip`;
an alternative listed behind that line never runs.  The uncovered goal, which names
the arm:
⊢ arm_preserves_vm fixture_arm_unmodeled
-/
#guard_msgs in
/-- AN ALTERNATIVE BEHIND THE `| skip` NEVER RUNS: the fail-closed fixture's
alternative is present but listed after `skip`, which always succeeds
first, so its arm stays open and the fallback step names it exactly as if
the line were missing.  This is the Rocq rule "an alternative listed
behind the fail never runs", held by construction: misordering is a build
error, not a silently dead line.
model: `vm_arm_uncovered` over `fixture_table` with one alternative misordered -/
example : ∀ c ∈ fixture_table, arm_preserves_vm c := by
  vm_arms_split fixture_table
  all_goals first
    | exact fixture_arm_exit_preserves_vm
    | skip
    | exact fixture_arm_unmodeled_preserves_vm
  all_goals vm_arm_uncovered

/-! The real alternation is stated about `checked_table` itself, not about
the empty list it unfolds to today: the anchor below prints the
statement, so a theorem restated over another list fails it even while
the two are definitionally equal.  No kernel behaviour is claimed. -/

/--
info: LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms.checked_table_preserves_vm (c : CheckedArm) :
  c ∈ checked_table → arm_preserves_vm c
-/
#guard_msgs in
#check checked_table_preserves_vm

end Alternation

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.VmMapsDisjoint
