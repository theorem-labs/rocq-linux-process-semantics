import LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg
import LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Budgets

/-! rocq-baseline: e252bb488654d47eb34430e97c94769ab7dd4923 -/

/-! rocq-cases: e252bb488654d47eb34430e97c94769ab7dd4923
covers: brk_two_pages_is_budget_refused -- brk_two_pages_is_budget_refused
covers: brk_one_page_is_not_budget_refused -- brk_one_page_is_not_budget_refused
covers: brk_query_is_not_budget_refused -- brk_query_is_not_budget_refused
covers: brk_one_byte_on_spent_budget_is_budget_refused -- brk_one_byte_on_spent_budget_is_budget_refused
covers: brk_shrink_is_not_budget_refused -- brk_shrink_is_not_budget_refused
covers: brk_budget_refused_forces -- brk_budget_refused_forces
covers: brk_dispatch -- brk_dispatch
covers: brk_budget_refused_is_refusal -- brk_budget_refused_is_refusal
covers: mmap_two_pages_is_budget_refused -- mmap_two_pages_is_budget_refused
covers: mmap_one_page_is_not_budget_refused -- mmap_one_page_is_not_budget_refused
covers: mmap_noreserve_is_not_budget_refused -- mmap_noreserve_is_not_budget_refused
covers: mmap_prot_none_is_not_budget_refused -- mmap_prot_none_is_not_budget_refused
covers: mmap_overflowing_len_is_not_budget_refused -- mmap_overflowing_len_is_not_budget_refused
covers: mmap_fixed_commit_on_spent_budget_is_budget_refused -- mmap_fixed_commit_on_spent_budget_is_budget_refused
covers: mmap_fixed_commit_within_budget_is_not_budget_refused -- mmap_fixed_commit_within_budget_is_not_budget_refused
covers: mmap_noreplace_two_pages_is_budget_refused -- mmap_noreplace_two_pages_is_budget_refused
covers: mmap_noreplace_one_page_is_not_budget_refused -- mmap_noreplace_one_page_is_not_budget_refused
covers: mmap_noreplace_prot_none_is_not_budget_refused -- mmap_noreplace_prot_none_is_not_budget_refused
covers: mmap_sanitizer_budget_plus_page_is_budget_refused -- mmap_sanitizer_budget_plus_page_is_budget_refused
covers: mmap_sanitizer_budget_exact_is_not_budget_refused -- mmap_sanitizer_budget_exact_is_not_budget_refused
covers: mmap_budget_refused_is_refusal -- mmap_budget_refused_is_refusal
covers: mremap_grow_on_spent_budget_is_budget_refused -- mremap_grow_on_spent_budget_is_budget_refused
covers: mremap_grow_within_budget_is_not_budget_refused -- mremap_grow_within_budget_is_not_budget_refused
covers: mremap_equal_size_is_not_budget_refused -- mremap_equal_size_is_not_budget_refused
covers: mremap_shrink_is_not_budget_refused -- mremap_shrink_is_not_budget_refused
covers: ov_pre_state_within_budget -- ov_pre_state_within_budget
covers: ov_mark_fires_while_a_move_fits -- ov_mark_fires_while_a_move_fits
covers: ov_charges -- ov_charges
covers: un_pre_state_within_budget -- un_pre_state_within_budget
covers: un_mark_fires_on_the_move_refusal -- un_mark_fires_on_the_move_refusal
covers: un_charges -- un_charges
covers: un_inplace_gate_passes -- un_inplace_gate_passes
covers: region_free_app_r -- region_free_app_r
covers: region_free_map_remove -- region_free_map_remove
covers: page_round_up_Z_mod -- page_round_up_Z_mod
covers: page_round_up_Z_nonneg -- page_round_up_Z_nonneg
covers: page_align_is0_b_false_word -- page_align_is0_b_false_word
covers: mremap_model_next_limit -- mremap_model_next_limit
covers: mremap_budget_refused_fires_on_inplace_refusal -- mremap_budget_refused_fires_on_inplace_refusal
covers: mremap_budget_refused_refuses_move -- mremap_budget_refused_refuses_move
covers: mremap_budget_refused_refuses_inplace -- mremap_budget_refused_refuses_inplace
covers: mprotect_expose_on_spent_budget_is_budget_refused -- mprotect_expose_on_spent_budget_is_budget_refused
covers: mprotect_expose_within_budget_is_not_budget_refused -- mprotect_expose_within_budget_is_not_budget_refused
covers: mprotect_already_rw_is_not_budget_refused -- mprotect_already_rw_is_not_budget_refused
covers: mprotect_dispatch -- mprotect_dispatch
covers: mprotect_budget_refused_is_refusal -- mprotect_budget_refused_is_refusal
covers: touch_store_reports_the_page -- touch_store_reports_the_page
covers: touch_on_spent_budget_is_budget_refused -- touch_on_spent_budget_is_budget_refused
covers: touch_on_spent_budget_errors -- touch_on_spent_budget_errors
covers: touch_within_budget_is_not_budget_refused -- touch_within_budget_is_not_budget_refused
covers: ebreak_fault_is_not_budget_refused -- ebreak_fault_is_not_budget_refused
covers: wtouch_checker -- wtouch_checker
covers: wtouch_is_budget_refused -- wtouch_is_budget_refused
covers: wtouch_errors -- wtouch_errors
covers: brk_dispatches_to_its_mark -- brk_dispatches_to_its_mark
covers: brk_is_dispatched -- brk_is_dispatched
covers: mremap_is_dispatched -- mremap_is_dispatched
covers: mmap_is_dispatched -- mmap_is_dispatched
covers: mprotect_is_dispatched -- mprotect_is_dispatched
covers: brk_number_reaches_its_mark -- brk_number_reaches_its_mark
covers: getcwd_is_never_budget_refused -- getcwd_is_never_budget_refused
covers: exit_is_never_budget_refused -- exit_is_never_budget_refused
covers: exits_c_no_budget_refused -- exits_c_no_budget_refused
covers: exit0_never_budget_refused -- exit0_never_budget_refused
covers: exit0_source_within_budget -- exit0_source_within_budget
covers: mm_config -- mm_config
covers: mm_step -- mm_step
covers: mm_instr_sstep -- mm_instr_sstep
covers: mm_svc6 -- mm_svc6
covers: mm_star -- mm_star
covers: mm_ecall_is_budget_refused -- mm_ecall_is_budget_refused
covers: mm_run_budget_refused -- mm_run_budget_refused
covers: mm_not_within_budget -- mm_not_within_budget
covers: exit0_strong_universal_error_free_budgets -- exit0_strong_universal_error_free_budgets
covers: exit0_never_dies_by_signal -- exit0_never_dies_by_signal
covers: exit0_strong_universal_error_free_budgets_abort -- exit0_strong_universal_error_free_budgets_abort
covers: exit0_budgets_from_pinned -- exit0_budgets_from_pinned
covers: exit0_must_exit_at_cfg -- exit0_must_exit_at_cfg
covers: exit0_obs_cfg -- exit0_obs_cfg
covers: exit0_strong_universal_error_free_budgets_scfg -- exit0_strong_universal_error_free_budgets_scfg
covers: exit0_source_within_budget_scfg -- exit0_source_within_budget_scfg
covers: mark_is_never_spurious -- mark_is_never_spurious
covers: marked_step_is_configured -- marked_step_is_configured
covers: demo_entry_valid_ebreak -- demo_entry_valid_ebreak
covers: ebreak_source_within_budget -- ebreak_source_within_budget
covers: ebreak_errors -- ebreak_errors
covers: ebreak_errors_cfg -- ebreak_errors_cfg
covers: ebreak_refutes_error_free_budgets -- ebreak_refutes_error_free_budgets
covers: ebreak_refutes_error_free_scfg_budgets -- ebreak_refutes_error_free_scfg_budgets
covers: demo_entry_valid_exit0_abort -- demo_entry_valid_exit0_abort
covers: exit0_never_dies_by_signal_cfg -- exit0_never_dies_by_signal_cfg
covers: exit0_strong_universal_error_free_budgets_scfg_abort -- exit0_strong_universal_error_free_budgets_scfg_abort
covers: ebreak_config_abort -- ebreak_config_abort
covers: ebreak_only_abort -- ebreak_only_abort
covers: ebreak_fault_is_not_budget_refused_any -- ebreak_fault_is_not_budget_refused_any
covers: demo_entry_valid_ebreak_abort -- demo_entry_valid_ebreak_abort
covers: ebreak_source_within_budget_abort -- ebreak_source_within_budget_abort
covers: ebreak_errors_cfg_abort -- ebreak_errors_cfg_abort
covers: ebreak_refutes_error_free_scfg_budgets_abort -- ebreak_refutes_error_free_scfg_budgets_abort
-/

/-! # The budget marks, on cases chosen by hand

Mirrors `Checks/BudgetPremise.v`: allocation grants, first touches,
the dispatcher, and the run level (PARTs 4–6). Not part of the trusted specification:
this file is QA on the budget marks, written to be READ. No case here is
one the conformance harness can reach: the mark is a statement about what
the BUDGET leaves the kernel — a model constant and model-internal state —
and the run-level cases quantify over every execution.

`Equivalence.source_within_budget` excludes every input whose run reaches a marked
state. An unsound mark firing where the spec permits a non-refusal would
therefore exclude permitted runs from the budget-family statements.
PART 1's per-arm soundness lemmas rule this out on their stated surfaces;
the concrete cases pin each mark's firing in both directions on states
chosen by hand. Mremap deliberately over-approximates: a move can succeed
where its mark fires, and excluding that input is the safe direction.
Its in-place soundness argument needs the grown range to carry no backing
metadata beyond the source's own.

The cases restated here under Rocq's names exist because a `covers:` line
must name a theorem of this file (`tools/check_lean_cases_parity.py`).
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.BudgetPremise

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem (reg_get)
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples (exit_sysno)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
  (m_tight_brk brk_reserved brk_in)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
  (mmap_in mmap_noreserve_in mmap_noaccess_in mmap_overflow_i fixed_rw_model
   mmap_fixed_rw_in mmap_noreplace_in mprotect_in)
open LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg (getcwd_i mmap_dispatch exits_c_must_exit_at_cfg)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
  (ebreak_segments ebreak_ms ebreak_model ebreak_faults)
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
  (region_free_In region_free_intro)
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence (sanitizer_source_limit)

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-! Ledger arithmetic for `mremap_move_charge_at_fresh`, ported from
`theories/LinuxProcessSem/Sys/Mm/Mremap.v`. Empty entries need byte-count
identities: subtraction may drop them even when it preserves all bytes. -/

theorem mremap_word_range (w : word) : 0 ≤ bv_unsigned w ∧ bv_unsigned w < two_pow_64 := by
  have := w.isLt
  unfold bv_unsigned two_pow_64
  omega

theorem mremap_u64 (z : Int) (h : 0 ≤ z ∧ z < two_pow_64) :
    bv_unsigned (Z_to_bv 64 z) = z := bv_unsigned_Z_to_bv_small z h.1 h.2


theorem live_bytes_app (l1 l2 : List (word × word)) :
    live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2 := by
  induction l1 with
  | nil => simp [live_bytes]
  | cons p r ih => simp [live_bytes, ih, Int.add_assoc]

theorem live_bytes_nonneg (l : List (word × word)) : 0 ≤ live_bytes l := by
  induction l with
  | nil => exact Int.le_refl _
  | cons p r ih => have := (mremap_word_range p.2).1; simp only [live_bytes]; omega

theorem maps_subtract_app (l1 l2 : List (word × word)) (lo hi : Int) :
    maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi := by
  induction l1 with
  | nil => rfl
  | cons p r ih => simp [maps_subtract, ih, List.append_assoc]

theorem maps_subtract_all_app (cuts l1 l2 : List (word × word)) :
    maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts := by
  induction cuts generalizing l1 l2 with
  | nil => rfl
  | cons p r ih => simp only [maps_subtract_all, maps_subtract_app, ih]

theorem iv_subtract_disjoint (a sz : word) (lo hi : Int)
    (hp : 0 < bv_unsigned sz) (hh : lo ≤ hi)
    (hd : bv_unsigned a + bv_unsigned sz ≤ lo ∨ hi ≤ bv_unsigned a) :
    iv_subtract a sz lo hi = [(a, sz)] := by
  unfold iv_subtract
  dsimp only
  split <;> split <;> rename_i h1 h2
  · omega
  · have he : min (bv_unsigned sz) (lo - bv_unsigned a) = bv_unsigned sz := by omega
    simp only [he, List.append_nil, List.cons.injEq, and_true]
    simp [Z_to_bv, bv_unsigned]
  · have he : max (bv_unsigned a) hi = bv_unsigned a := by omega
    have hs : bv_unsigned a + bv_unsigned sz - bv_unsigned a = bv_unsigned sz := by omega
    simp only [he, hs, List.nil_append, List.cons.injEq, and_true, Prod.mk.injEq]
    simp [Z_to_bv, bv_unsigned]
  · omega


theorem maps_subtract_all_disjoint_entry (cuts : List (word × word)) (a sz : word)
    (hp : 0 < bv_unsigned sz) (hf : region_free cuts a sz = true) :
    maps_subtract_all [(a, sz)] cuts = [(a, sz)] := by
  have hfree_iff (l : List (word × word)) (a n : word) :
      region_free l a n = true ↔ ∀ b s, (b, s) ∈ l →
        bv_unsigned b + bv_unsigned s ≤ bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned b := by
    induction l with
    | nil => simp [region_free]
    | cons p r ih =>
      simp only [region_free, Bool.and_eq_true, Bool.not_eq_true', iv_overlap,
        Bool.and_eq_false_iff, decide_eq_false_iff_not, ih]
      constructor
      · rintro ⟨hp, hr⟩ b s hm
        rcases List.mem_cons.mp hm with he | he
        · cases he; dsimp only at hp; omega
        · exact hr b s he
      · intro h
        exact ⟨by have := h p.1 p.2 (by simp); omega,
          fun b s hm => h b s (List.mem_cons_of_mem _ hm)⟩
  induction cuts with
  | nil => rfl
  | cons p r ih =>
    have hd := (hfree_iff _ _ _).1 hf p.1 p.2 (by simp)
    have hr : region_free r a sz = true := (Bool.and_eq_true_iff.mp hf).2
    have hn := (mremap_word_range p.2).1
    simp only [maps_subtract_all, maps_subtract, List.append_nil]
    rw [iv_subtract_disjoint a sz _ _ hp (by omega) (by omega)]
    exact ih hr

theorem live_bytes_iv_subtract_le (a sz : word) (lo hi : Int) (hh : lo ≤ hi) :
    live_bytes (iv_subtract a sz lo hi) ≤ bv_unsigned sz := by
  have ha := mremap_word_range a
  have hn := mremap_word_range sz
  unfold iv_subtract
  dsimp only
  split <;> split <;> simp only [List.append_nil, List.cons_append, List.nil_append, live_bytes]
  all_goals try rw [mremap_u64 _ (by omega)]
  all_goals try rw [mremap_u64 _ (by omega)]
  all_goals omega

theorem live_bytes_maps_subtract_le (l : List (word × word)) (lo hi : Int) (hh : lo ≤ hi) :
    live_bytes (maps_subtract l lo hi) ≤ live_bytes l := by
  induction l with
  | nil => exact Int.le_refl _
  | cons p r ih =>
    simp only [maps_subtract, live_bytes_app, live_bytes]
    have := live_bytes_iv_subtract_le p.1 p.2 lo hi hh
    omega

theorem live_bytes_maps_subtract_all_le (cuts l : List (word × word)) :
    live_bytes (maps_subtract_all l cuts) ≤ live_bytes l := by
  induction cuts generalizing l with
  | nil => exact Int.le_refl _
  | cons p r ih =>
    have hn := (mremap_word_range p.2).1
    exact Int.le_trans (ih _) (live_bytes_maps_subtract_le l _ _ (by omega))

theorem live_bytes_subtract_free (cuts l : List (word × word)) (lo hi : Int) (hh : lo ≤ hi)
    (hf : ∀ b s, (b, s) ∈ l → bv_unsigned b + bv_unsigned s ≤ lo ∨ hi ≤ bv_unsigned b) :
    live_bytes (maps_subtract_all (maps_subtract l lo hi) cuts) = live_bytes (maps_subtract_all l cuts) := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    change live_bytes (maps_subtract_all (iv_subtract p.1 p.2 lo hi ++ maps_subtract r lo hi) cuts) =
      live_bytes (maps_subtract_all ([(p.1, p.2)] ++ r) cuts)
    rw [maps_subtract_all_app, maps_subtract_all_app, live_bytes_app, live_bytes_app,
      ih (by intro b s h; exact hf b s (List.mem_cons_of_mem _ h))]
    congr 1
    by_cases hz : bv_unsigned p.2 = 0
    · have h1 := live_bytes_maps_subtract_all_le cuts (iv_subtract p.1 p.2 lo hi)
      have h2 := live_bytes_maps_subtract_all_le cuts [(p.1, p.2)]
      have h3 := live_bytes_nonneg (maps_subtract_all (iv_subtract p.1 p.2 lo hi) cuts)
      have h4 := live_bytes_nonneg (maps_subtract_all [(p.1, p.2)] cuts)
      have h5 := live_bytes_iv_subtract_le p.1 p.2 lo hi hh
      simp only [live_bytes] at h2
      omega
    · have hn := (mremap_word_range p.2).1
      rw [iv_subtract_disjoint _ _ _ _ (by omega) hh (hf _ _ (by simp))]

theorem iv_subtract_within (a sz : word) (lo hi : Int) (b s : word)
    (hfit : bv_unsigned a + bv_unsigned sz ≤ two_pow_64)
    (hin : (b, s) ∈ iv_subtract a sz lo hi) :
    bv_unsigned a ≤ bv_unsigned b ∧ bv_unsigned b + bv_unsigned s ≤ bv_unsigned a + bv_unsigned sz := by
  have ha := mremap_word_range a
  have hn := mremap_word_range sz
  unfold iv_subtract at hin
  simp only [List.mem_append] at hin
  rcases hin with hin | hin
  all_goals split at hin <;> simp only [List.mem_singleton, List.not_mem_nil] at hin
  all_goals try contradiction
  all_goals cases hin
  · rw [mremap_u64 _ (by omega)]; omega
  · rw [mremap_u64 _ (by omega), mremap_u64 _ (by omega)]; omega

theorem maps_subtract_In (l : List (word × word)) (lo hi : Int) (b s : word)
    (hin : (b, s) ∈ maps_subtract l lo hi) :
    ∃ a sz, (a, sz) ∈ l ∧ (b, s) ∈ iv_subtract a sz lo hi := by
  induction l with
  | nil => cases hin
  | cons p r ih =>
    rcases List.mem_append.mp hin with h | h
    · exact ⟨p.1, p.2, by simp, h⟩
    · obtain ⟨a, sz, hm, hs⟩ := ih h
      exact ⟨a, sz, List.mem_cons_of_mem _ hm, hs⟩

theorem maps_subtract_all_within (cuts l : List (word × word)) (b s : word)
    (hfit : ∀ a sz, (a, sz) ∈ l → bv_unsigned a + bv_unsigned sz ≤ two_pow_64)
    (hin : (b, s) ∈ maps_subtract_all l cuts) :
    ∃ a sz, (a, sz) ∈ l ∧ bv_unsigned a ≤ bv_unsigned b ∧
      bv_unsigned b + bv_unsigned s ≤ bv_unsigned a + bv_unsigned sz := by
  induction cuts generalizing l with
  | nil => exact ⟨b, s, hin, Int.le_refl _, Int.le_refl _⟩
  | cons p r ih =>
    have hfit' : ∀ a sz, (a, sz) ∈ maps_subtract l (bv_unsigned p.1) (bv_unsigned p.1 + bv_unsigned p.2) →
        bv_unsigned a + bv_unsigned sz ≤ two_pow_64 := by
      intro a sz hm
      obtain ⟨a0, s0, h0, hs⟩ := maps_subtract_In _ _ _ _ _ hm
      have h0fit := hfit _ _ h0
      have := iv_subtract_within _ _ _ _ _ _ h0fit hs
      omega
    obtain ⟨a, sz, hm, hw⟩ := ih _ hfit' hin
    obtain ⟨a0, s0, h0, hs⟩ := maps_subtract_In _ _ _ _ _ hm
    have := iv_subtract_within _ _ _ _ _ _ (hfit _ _ h0) hs
    exact ⟨a0, s0, h0, by omega, by omega⟩

theorem iv_subtract_misses_cut (c sz : word) (lo hi : Int) (b s : word)
    (_hl : 0 ≤ lo) (hh : hi < two_pow_64) (hin : (b, s) ∈ iv_subtract c sz lo hi) :
    bv_unsigned b + bv_unsigned s ≤ lo ∨ hi ≤ bv_unsigned b := by
  have hc := mremap_word_range c
  have hn := mremap_word_range sz
  unfold iv_subtract at hin
  simp only [List.mem_append] at hin
  rcases hin with hin | hin
  all_goals split at hin <;> simp only [List.mem_singleton, List.not_mem_nil] at hin
  all_goals try contradiction
  all_goals cases hin
  · rw [mremap_u64 _ (by omega)]; omega
  · rw [mremap_u64 (max _ _) (by omega)]; omega

theorem maps_subtract_misses_cut (l : List (word × word)) (lo hi : Int) (b s : word)
    (hl : 0 ≤ lo) (hh : hi < two_pow_64) (hin : (b, s) ∈ maps_subtract l lo hi) :
    bv_unsigned b + bv_unsigned s ≤ lo ∨ hi ≤ bv_unsigned b := by
  obtain ⟨a, sz, _, hs⟩ := maps_subtract_In _ _ _ _ _ hin
  exact iv_subtract_misses_cut a sz lo hi b s hl hh hs

theorem iv_subtract_self (a n : word) :
    iv_subtract a n (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = [] := by
  simp [iv_subtract]

theorem maps_subtract_all_nil (cuts : List (word × word)) : maps_subtract_all [] cuts = [] := by
  induction cuts with
  | nil => rfl
  | cons p r ih => exact ih

theorem lazy_interior_aligned (a n : word)
    (ha : bv_unsigned a % page_size = 0) (hn : bv_unsigned n % page_size = 0)
    (hp : 0 < bv_unsigned n) : lazy_interior a n = [(a, n)] := by
  have hlo : (bv_unsigned a + page_size - 1) / page_size * page_size = bv_unsigned a := by
    unfold page_size at *; omega
  have hhi : (bv_unsigned a + bv_unsigned n) / page_size * page_size = bv_unsigned a + bv_unsigned n := by
    unfold page_size at *; omega
  have hlt : bv_unsigned a < bv_unsigned a + bv_unsigned n := by omega
  have hs : bv_unsigned a + bv_unsigned n - bv_unsigned a = bv_unsigned n := by omega
  simp only [lazy_interior, hlo, hhi, hlt, hs, ↓reduceIte]
  simp [Z_to_bv, bv_unsigned]


/-- At a fresh destination with no backing metadata, the post-state charge
is destination independent. The ledger hypotheses match the Rocq theorem;
this does not establish their preservation by every syscall. -/
theorem mremap_move_charge_at_fresh (m : Model) (old old_n dst new_n : word)
    (halign : bv_unsigned dst % page_size = 0)
    (hnalign : bv_unsigned new_n % page_size = 0)
    (hpos : 0 < bv_unsigned new_n)
    (hend : bv_unsigned dst + bv_unsigned new_n < two_pow_64)
    (hfit : ∀ a sz, (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      bv_unsigned a + bv_unsigned sz ≤ two_pow_64)
    (hmaps : region_free (map_remove (m_vmmaps m).vm_maps old) dst new_n = true)
    (hnoacc : region_free (m_vmmaps m).vm_noaccess dst new_n = true)
    (hlazy : maps_subtract
      (maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
      (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n) =
      maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
    (hpages : ((m_vm_materialized m).filter
      (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))).filter
      (page_outside_range (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)) =
      (m_vm_materialized m).filter
        (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))) :
    vm_backing_used (mremap_model_next m old old_n dst new_n) =
      mremap_move_charge m old old_n new_n := by
  have hfree_iff (l : List (word × word)) (a n : word) :
      region_free l a n = true ↔ ∀ b s, (b, s) ∈ l →
        bv_unsigned b + bv_unsigned s ≤ bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned b := by
    induction l with
    | nil => simp [region_free]
    | cons p r ih =>
      simp only [region_free, Bool.and_eq_true, Bool.not_eq_true', iv_overlap,
        Bool.and_eq_false_iff, decide_eq_false_iff_not, ih]
      constructor
      · rintro ⟨hp, hr⟩ b s hm
        rcases List.mem_cons.mp hm with he | he
        · cases he; dsimp only at hp; omega
        · exact hr b s he
      · intro h
        exact ⟨by have := h p.1 p.2 (by simp); omega,
          fun b s hm => h b s (List.mem_cons_of_mem _ hm)⟩
  let kl := maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)
  let kp := (m_vm_materialized m).filter
    (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
  let r0 := map_remove (m_vmmaps m).vm_maps old
  let na := (m_vmmaps m).vm_noaccess
  have hkl : region_free kl dst new_n = true := by
    apply (hfree_iff _ _ _).2
    intro a n hin
    change (a, n) ∈ kl at hin
    change maps_subtract kl _ _ = kl at hlazy
    rw [← hlazy] at hin
    exact maps_subtract_misses_cut _ _ _ _ _ (mremap_word_range dst).1 hend hin
  have hr : ∀ b s, (b, s) ∈ maps_subtract_all r0 na →
      bv_unsigned b + bv_unsigned s ≤ bv_unsigned dst ∨
      bv_unsigned dst + bv_unsigned new_n ≤ bv_unsigned b := by
    intro b s hin
    obtain ⟨a, sz, hin0, hw⟩ := maps_subtract_all_within na r0 b s hfit hin
    have := (hfree_iff _ _ _).1 hmaps a sz hin0
    omega
  unfold vm_backing_used mremap_move_charge mremap_model_next vm_resize_backing mremap_maps_next
  simp only [m_vmmaps, m_vm_lazy, m_vm_materialized, with_vm_backing, with_vmmaps,
    vm_backed_maps]
  simp only [m_vm_lazy] at hlazy
  simp only [m_vm_materialized] at hpages
  rw [hlazy, hpages]
  change live_bytes (maps_subtract_all
      (maps_subtract_all ([(dst, new_n)] ++ r0) na)
      (if mremap_source_lazy_b m old old_n then lazy_interior dst new_n ++ kl else kl)) +
      (((if mremap_source_lazy_b m old old_n then
        ((m_vm_materialized m).filter (fun p => page_in_half_open (bv_unsigned old)
          (bv_unsigned old + bv_unsigned old_n) p && bv_unsigned p - bv_unsigned old < bv_unsigned new_n)).map
          (move_page_base old dst) else []) ++ kp).length : Int) * page_size = _
  rw [maps_subtract_all_app, maps_subtract_all_disjoint_entry na dst new_n hpos hnoacc]
  cases mremap_source_lazy_b m old old_n
  · simp only [ Bool.false_eq_true, ↓reduceIte, List.nil_append, List.length_nil,
      Nat.zero_add, maps_subtract_all_app, live_bytes_app,
      maps_subtract_all_disjoint_entry kl dst new_n hpos hkl, live_bytes]
    dsimp only [r0, na, kl, kp, m_vmmaps, m_vm_lazy, m_vm_materialized]
    omega
  · simp only [↓reduceIte, lazy_interior_aligned dst new_n halign hnalign hpos,
      List.length_append, List.length_map, List.cons_append, List.nil_append,
      maps_subtract_all, maps_subtract, iv_subtract_self]
    rw [live_bytes_subtract_free kl (maps_subtract_all r0 na) _ _ (by omega) hr]
    dsimp only [r0, na, kl, kp, m_vmmaps, m_vm_lazy, m_vm_materialized]
    omega

/-- (Rocq: `m_tight_brk_grown`.) The one-page brk grant has spent the budget. -/
def m_tight_brk_grown : Model :=
  with_vmmaps (mkVmMaps brk_reserved [(65536, 4096)] 65536 69632 4096) m_tight_brk

/-- A fresh model with no live grant, isolating the premise at
`Equivalence.sanitizer_source_limit` from any earlier allocation. -/
def sanitizer_budget_model (lim : Int) : Model :=
  with_vmmaps (mkVmMaps [] [] 0 0 lim)
    (init_model [] 0 0 demo_sp lim (demo_input [] IEof))

/-- (Rocq: `mremap_model`.) One eager page under the given budget. -/
def mremap_model (lim : Int) : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 lim)
    (init_model [] 0 0 demo_sp lim (demo_input [] IEof))

/-- (Rocq: `mremap_in`.) Resize the page at 65536 with MAYMOVE set. -/
def mremap_in (old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [65536, old_size, new_size, 1, 0, 0]
    (fun _ => none) (fun _ => none)

/-- (Rocq: `mremap_two_page_model`.) Two eager pages under the given budget. -/
def mremap_two_page_model (lim : Int) : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 lim)
    (init_model [] 0 0 demo_sp lim (demo_input [] IEof))

/-- The OVER witness: an eager source beside a MAP_NORESERVE neighbour
whose first page is touched. Growing across the neighbour clears its lazy
metadata in the hypothetical in-place post-state and charges it eagerly.
The grow's charges are not ordered uniformly across states, so the mark
must test both budget gates. -/
def ov_model : Model :=
  with_vm_backing [(0x11000, 8192)] [0x11000]
    (with_vmmaps (mkVmMaps [] [(0x10000, 4096), (0x11000, 8192)] 0 0 16384)
      (init_model [] 0 0 demo_sp 16384 (demo_input [] IEof)))

/-- The UNDER witness of issue 701. The PROT_NONE neighbour is recorded
in both `vm_maps` and `vm_noaccess`, as the NULL-hint PROT_NONE arm of
`mmap_spec` records it: two ordinary mmaps from a fresh process reach this
state. Its protected bytes are subtracted from backing, so only the eager
source charges the budget. -/
def un_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(0x10000, 4096), (0x11000, 8192)] [(0x11000, 8192)]
      0 0 8192 (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo))
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

/-- A two-page grow exceeds the one-page brk budget. -/
theorem brk_two_pages_is_budget_refused :
  brk_budget_refused_b m_tight_brk 73728 = true := by decide

/-- A one-page grow exactly fits the brk budget. -/
theorem brk_one_page_is_not_budget_refused :
  brk_budget_refused_b m_tight_brk 69632 = false := by decide

/-- Querying the break consumes no backing. -/
theorem brk_query_is_not_budget_refused :
  brk_budget_refused_b m_tight_brk 0 = false := by decide

/-- After the first grant, even one more byte exceeds the budget. -/
theorem brk_one_byte_on_spent_budget_is_budget_refused :
  brk_budget_refused_b m_tight_brk_grown 69633 = true := by decide

/-- Shrinking releases backing rather than requesting a grant. -/
theorem brk_shrink_is_not_budget_refused :
  brk_budget_refused_b m_tight_brk_grown 65536 = false := by decide

/-- Two new pages exceed the one-page remainder. -/
theorem mmap_two_pages_is_budget_refused :
  alloc_budget_refused_b (mmap_in 8192) tight_model = true := by decide

/-- Within budget, -ENOMEM remains possible
(`Checks.SpuriousCfg.mmap_enomem_spurious_within_budget`): the “forged budget
refusal”. The mark reads the request and state, never the answer, so it
does not carry that refusal. -/
theorem mmap_one_page_is_not_budget_refused :
  alloc_budget_refused_b (mmap_in 4096) tight_model = false := by decide

/-- MAP_NORESERVE is free at grant time even beyond budget: its pages
are charged on first touch, exercised in PART 2. -/
theorem mmap_noreserve_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noreserve_in 8192) tight_model = false := by decide

/-- A PROT_NONE reservation consumes no backing at grant time. -/
theorem mmap_prot_none_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noaccess_in 8192) tight_model = false := by decide

/-- The mark is `false` on this request through its MAP_FIXED PROT_NONE
branch, whatever the length, so this case does not pin the overflow gate. -/
theorem mmap_overflowing_len_is_not_budget_refused :
  alloc_budget_refused_b mmap_overflow_i noaccess_base = false := by decide

/-- Exposing a PROT_NONE page needs backing even under MAP_FIXED. -/
theorem mmap_fixed_commit_on_spent_budget_is_budget_refused :
  alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 0) = true := by decide

/-- A page of remaining budget pays for the contained commit. -/
theorem mmap_fixed_commit_within_budget_is_not_budget_refused :
  alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 4096) = false := by decide

/-- The free-range MAP_FIXED_NOREPLACE branch landed while the mark was
under review and escaped it until the guard's branch count was added.
This is the charging case that guard must keep covered. -/
theorem mmap_noreplace_two_pages_is_budget_refused :
  alloc_budget_refused_b (mmap_noreplace_in 3 8192) tight_model = true := by decide

/-- NOREPLACE uses ordinary grant accounting; covering the previously
missed branch must not turn every such request into a budget refusal. -/
theorem mmap_noreplace_one_page_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noreplace_in 3 4096) tight_model = false := by decide

/-- The NOREPLACE branch's PROT_NONE spelling consumes no backing;
branch coverage must preserve the distinction from its writable grant. -/
theorem mmap_noreplace_prot_none_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noreplace_in 0 8192) tight_model = false := by decide

/-- The premise bites at the 2 GiB `Equivalence.sanitizer_source_limit`
too, on a fresh model with no live grant. The ledger compares page-rounded
byte sizes, not a page count. -/
theorem mmap_sanitizer_budget_plus_page_is_budget_refused :
  alloc_budget_refused_b
    (mmap_in (Z_to_bv 64 (sanitizer_source_limit + page_size)))
    (sanitizer_budget_model sanitizer_source_limit) = true := by decide

/-- The matching boundary case at `Equivalence.sanitizer_source_limit`
keeps the fresh-model byte accounting from treating exact exhaustion as
excess. -/
theorem mmap_sanitizer_budget_exact_is_not_budget_refused :
  alloc_budget_refused_b
    (mmap_in (Z_to_bv 64 sanitizer_source_limit))
    (sanitizer_budget_model sanitizer_source_limit) = false := by decide

/-- Growing an eager mapping requires backing for the added page. -/
theorem mremap_grow_on_spent_budget_is_budget_refused :
  alloc_budget_refused_b (mremap_in 4096 8192) (mremap_model 4096) = true := by decide

/-- A two-page budget holds the grown two-page mapping. -/
theorem mremap_grow_within_budget_is_not_budget_refused :
  alloc_budget_refused_b (mremap_in 4096 8192) (mremap_model 8192) = false := by decide

/-- An equal-size request leaves before the budget-dependent branch. -/
theorem mremap_equal_size_is_not_budget_refused :
  alloc_budget_refused_b (mremap_in 4096 4096) (mremap_model 4096) = false := by decide

/-- A shrink leaves before the budget-dependent branch. -/
theorem mremap_shrink_is_not_budget_refused :
  alloc_budget_refused_b (mremap_in 8192 4096) (mremap_two_page_model 8192) = false := by decide

/-- The pre-state half fills its budget: exclusion comes from the grow's
hypothetical charge, not an already over-budget ledger. -/
theorem ov_pre_state_within_budget :
  vm_backing_within_limit ov_model = true := by decide

/-- The mark fires although in-place growth is unavailable because the
tail is occupied, and a move to a free destination fits exactly at budget.
Linux moves and succeeds; the premise excludes the input anyway. This is
over-approximation, the safe direction: keep this case so a later change
cannot use the move's gate alone and silently turn it into under-approximation. -/
theorem ov_mark_fires_while_a_move_fits :
  mremap_budget_refused_b 0x10000 4096 12288 1 ov_model = true
  ∧ mremap_inplace_grow_b ov_model 0x10000 4096 12288 4096 12288 = false
  ∧ mremap_fresh_b ov_model 4096 12288 0x10000 4096 0x100000 12288 = true := by decide

/-- Clearing the neighbour's lazy metadata pushes the hypothetical
in-place charge past budget; moving preserves that neighbour and fits
exactly. The destination-free charge read by the mark is the moved one's. -/
theorem ov_charges :
  vm_backing_used (mremap_model_next ov_model 0x10000 4096 0x10000 12288) = 20480
  ∧ vm_backing_used (mremap_model_next ov_model 0x10000 4096 0x100000 12288) = 16384
  ∧ mremap_move_charge ov_model 0x10000 4096 12288 = 16384 := by decide

/-- The protected neighbour leaves budget for the eager source; the
missed refusal is exposed by growing, not by an invalid initial charge. -/
theorem un_pre_state_within_budget :
  vm_backing_within_limit un_model = true := by decide

/-- The occupied tail prevents in-place growth. Moving re-creates the
whole grown mapping and exceeds budget, checked here at destination
0x100000. The every-destination claim is Rocq's
`mremap_move_charge_at_fresh`, not ported. Testing the move's gate catches
the refusal. -/
theorem un_mark_fires_on_the_move_refusal :
  mremap_budget_refused_b 0x10000 4096 12288 1 un_model = true
  ∧ mremap_inplace_grow_b un_model 0x10000 4096 12288 4096 12288 = false
  ∧ mremap_fresh_b un_model 4096 12288 0x10000 4096 0x100000 12288 = false := by decide

/-- The tail lies under `vm_noaccess`, so `State.vm_backed_maps`
subtracts its bytes from the hypothetical in-place post-state. A fresh move
pays for the whole grown mapping; the destination-free charge the mark reads
is that moved charge. -/
theorem un_charges :
  vm_backing_used (mremap_model_next un_model 0x10000 4096 0x10000 12288) = 4096
  ∧ vm_backing_used (mremap_model_next un_model 0x10000 4096 0x100000 12288) = 12288
  ∧ mremap_move_charge un_model 0x10000 4096 12288 = 12288 := by decide

/-- The old mark read only this in-place budget gate. Subtracting the
protected tail leaves it silent at every limit that fits the pre-state:
the silence exposed by issue 701. -/
theorem un_inplace_gate_passes :
  mremap_final_budget_b un_model 0x10000 4096 0x10000 12288 = true := by decide

/-- Exposing PROT_NONE memory fails the charge on a spent budget. -/
theorem mprotect_expose_on_spent_budget_is_budget_refused :
  alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 0) = true := by decide

/-- A page of remaining budget pays for exposing the reservation. -/
theorem mprotect_expose_within_budget_is_not_budget_refused :
  alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 4096) = false := by decide

/-- An already writable mapping needs no additional backing. -/
theorem mprotect_already_rw_is_not_budget_refused :
  alloc_budget_refused_b (mprotect_in 65536 4096 3) (mremap_model 4096) = false := by decide

/-- Soundness of the brk mark starts at `brk_r_ok`: its only permitted
answer when marked is the unmoved break. This is brk's refusal encoding,
needed to connect the arm to `Run.refusal_b`. -/
theorem brk_budget_refused_forces (m : Model) (req r : word) :
    brk_budget_refused_b m req = true → brk_r_ok m req r = true →
    r = (m_vmmaps m).vm_brk := by
  intro hm hr
  simp only [brk_budget_refused_b, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not] at hm
  rcases hm with ⟨⟨⟨⟨hzero, hmin⟩, hpos⟩, hgrow⟩, hbudget⟩
  have hnshrink : ¬ bv_unsigned req < bv_unsigned (m_vmmaps m).vm_brk := by omega
  simp only [brk_r_ok, hzero, decide_eq_false hmin, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, hnshrink, Bool.and_eq_true,
    Bool.or_eq_true, bv_eqb_eq] at hr
  rcases hr with ⟨hr | hr, hok⟩
  · subst r
    simp only [brk_grow_ok, hpos, hgrow, decide_true, Bool.true_and,
      ↓reduceIte, hbudget, Bool.and_false, Bool.false_eq_true] at hok
  · exact hr

/-- The brk syscall number selects the brk arm. -/
theorem brk_dispatch (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    bv_unsigned i.in_sysno = 214 →
    (syscall_spec i m o ↔ brk_spec (in_arg i 0) i m o) := by
  intro h
  unfold syscall_spec
  apply dispatch_arm spec_table i m o Sys.Registry.Mm.Mmap.brk_arm
  simp only [lookup_arm, spec_table, h]
  rfl

/-- Freeness of a concatenation implies freeness of its right ledger. -/
theorem region_free_app_r (l1 l2 : List (word × word)) (lo n : word) :
    region_free (l1 ++ l2) lo n = true → region_free l2 lo n = true := by
  intro h
  apply region_free_intro
  intro a sz hin
  exact region_free_In _ _ _ _ _ h (List.mem_append_right _ hin)

/-- Dropping a mapping preserves freeness. -/
theorem region_free_map_remove (maps : List (word × word)) (old lo n : word) :
    region_free maps lo n = true → region_free (map_remove maps old) lo n = true := by
  intro h
  apply region_free_intro
  intro a sz hin
  exact region_free_In _ _ _ _ _ h (List.mem_filter.mp hin).1

/-- Rounded lengths are page multiples, including for negative integers. -/
theorem page_round_up_Z_mod (z : Int) : page_round_up_Z z % page_size = 0 := by
  unfold page_round_up_Z
  exact Int.mul_emod_left _ _

/-- Rounding a nonnegative length preserves nonnegativity. -/
theorem page_round_up_Z_nonneg (z : Int) : 0 ≤ z → 0 ≤ page_round_up_Z z :=
  Checks.Sys.Mm.Mmap.page_round_up_Z_nonneg z

/-- A length passing the wrap gate has an exact word round trip. -/
theorem page_align_is0_b_false_word (len : word) :
    page_align_is0_b len = false →
    bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) =
      page_round_up_Z (bv_unsigned len) := by
  intro h
  simp only [page_align_is0_b, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  apply bv_unsigned_Z_to_bv_small
  · apply page_round_up_Z_nonneg
    unfold bv_unsigned
    omega
  · change page_round_up_Z (bv_unsigned len) < two_pow_64
    omega

/-- Resizing preserves the declared budget. -/
theorem mremap_model_next_limit (m : Model) (old old_n dst new_n : word) :
    (m_vmmaps (mremap_model_next m old old_n dst new_n)).vm_limit =
      (m_vmmaps m).vm_limit := rfl

/-- The two-gate rule: either budget gate of a grow must fire the mark.
This is the in-place half, with no side condition beyond the mark's argument
gates. -/
theorem mremap_budget_refused_fires_on_inplace_refusal
    (old old_size new_size flags : word) (m : Model) :
    (bv_unsigned flags == MREMAP_MAYMOVE) = true →
    (bv_unsigned old % page_size == 0) = true →
    page_align_is0_b new_size = false →
    page_round_up_Z (bv_unsigned new_size) ≤ TASK_SIZE →
    page_align_is0_b old_size = false →
    (mremap_source_b (m_vmmaps m) old
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
      (page_round_up_Z (bv_unsigned old_size)) &&
     mremap_backing_uniform_b m old
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))) = true →
    page_round_up_Z (bv_unsigned old_size) < page_round_up_Z (bv_unsigned new_size) →
    mremap_final_budget_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = false →
    mremap_budget_refused_b old old_size new_size flags m = true := by
  intro hf ha hn hb ho hs hg hgate
  have hb' : ¬ TASK_SIZE < page_round_up_Z (bv_unsigned new_size) := by omega
  have hg' : ¬ page_round_up_Z (bv_unsigned new_size) ≤
      page_round_up_Z (bv_unsigned old_size) := by omega
  simp only [mremap_budget_refused_b, hf, ha, hn, hb', ho, hs, hg', hgate,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false]

/-- The move gate's refusal fires the mark at every fresh destination.
The ledger hypotheses are those of the Rocq case: this does not prove
that arbitrary model states satisfy the ownership invariants. -/
theorem mremap_budget_refused_refuses_move
    (old old_size new_size flags : word) (m : Model) (dst : word) :
    let old_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))
    let new_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))
    (bv_unsigned flags == MREMAP_MAYMOVE) = true →
    (bv_unsigned old % page_size == 0) = true →
    page_align_is0_b new_size = false →
    page_round_up_Z (bv_unsigned new_size) ≤ TASK_SIZE →
    page_align_is0_b old_size = false →
    (mremap_source_b (m_vmmaps m) old old_n (page_round_up_Z (bv_unsigned old_size)) &&
      mremap_backing_uniform_b m old old_n) = true →
    page_round_up_Z (bv_unsigned old_size) < page_round_up_Z (bv_unsigned new_size) →
    bv_unsigned dst % page_size = 0 →
    bv_unsigned dst + page_round_up_Z (bv_unsigned new_size) ≤ alloc_top (m_vmmaps m) →
    region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) dst new_n = true →
    (∀ a sz, (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      bv_unsigned a + bv_unsigned sz ≤ two_pow_64) →
    region_free (m_vmmaps m).vm_noaccess dst new_n = true →
    maps_subtract
      (maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
      (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n) =
      maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n) →
    ((m_vm_materialized m).filter
      (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))).filter
      (page_outside_range (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)) =
      (m_vm_materialized m).filter
        (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) →
    mremap_final_budget_b m old old_n dst new_n = false →
    mremap_budget_refused_b old old_size new_size flags m = true := by
  dsimp only
  intro hf ha hn hb ho hs hg hda hdt hdf hfit hna hl hp hgate
  have hnw := page_align_is0_b_false_word new_size hn
  have hnn := page_round_up_Z_nonneg (bv_unsigned old_size) (mremap_word_range old_size).1
  have htop := alloc_top_lt (m_vmmaps m)
  have hcharge := mremap_move_charge_at_fresh m old _ dst _ hda
    (by rw [hnw]; exact page_round_up_Z_mod _)
    (by rw [hnw]; omega) (by rw [hnw]; omega) hfit
    (region_free_map_remove _ _ _ _ (region_free_app_r _ _ _ _ hdf)) hna hl hp
  simp only [mremap_final_budget_b, vm_backing_within_limit,
    mremap_model_next_limit, hcharge] at hgate
  have hb' : ¬ TASK_SIZE < page_round_up_Z (bv_unsigned new_size) := by omega
  have hg' : ¬ page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size) := by omega
  simp only [mremap_budget_refused_b, hf, ha, hn, hb', ho, hs, hg',
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, mremap_move_budget_b,
    hgate, Bool.and_false, Bool.not_false]

/-- In-place soundness needs the grown range to carry only the source's
backing metadata. Under those hypotheses the move and in-place charges
agree; the UNDER fixture shows why the hypotheses cannot be dropped. -/
theorem mremap_budget_refused_refuses_inplace
    (old old_size new_size flags : word) (m : Model) :
    let old_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))
    let new_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))
    (∀ a sz, (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      bv_unsigned a + bv_unsigned sz ≤ two_pow_64) →
    region_free (m_vmmaps m).vm_noaccess old new_n = true →
    maps_subtract
      (maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
      (bv_unsigned old) (bv_unsigned old + bv_unsigned new_n) =
      maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n) →
    ((m_vm_materialized m).filter
      (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))).filter
      (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned new_n)) =
      (m_vm_materialized m).filter
        (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) →
    mremap_budget_refused_b old old_size new_size flags m = true →
    mremap_inplace_grow_b m old old_n new_n
      (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = false := by
  dsimp only
  intro hfit hna hl hp hm
  unfold mremap_budget_refused_b at hm
  dsimp only at hm
  by_cases hf : (!(bv_unsigned flags == MREMAP_MAYMOVE)) = true
  · rw [ite_eq_left hf] at hm
    cases hm
  rw [ite_eq_right hf] at hm
  by_cases ha : (!(bv_unsigned old % page_size == 0)) = true
  · rw [ite_eq_left ha] at hm
    cases hm
  rw [ite_eq_right ha] at hm
  by_cases hn : page_align_is0_b new_size = true
  · rw [ite_eq_left hn] at hm
    cases hm
  rw [ite_eq_right hn] at hm
  by_cases hb : TASK_SIZE < page_round_up_Z (bv_unsigned new_size)
  · rw [ite_eq_left hb] at hm
    cases hm
  rw [ite_eq_right hb] at hm
  by_cases ho : page_align_is0_b old_size = true
  · rw [ite_eq_left ho] at hm
    cases hm
  rw [ite_eq_right ho] at hm
  by_cases hs : (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (page_round_up_Z (bv_unsigned old_size)) && mremap_backing_uniform_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) = true
  · rw [ite_eq_left hs] at hm
    cases hm
  rw [ite_eq_right hs] at hm
  by_cases hg : page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size)
  · rw [ite_eq_left hg] at hm
    cases hm
  rw [ite_eq_right hg] at hm
  apply Bool.eq_false_iff.mpr
  intro hip
  simp only [mremap_inplace_grow_b, Bool.and_eq_true, decide_eq_true_eq] at hip
  obtain ⟨⟨htop, hfree⟩, hgate⟩ := hip
  have hnw := page_align_is0_b_false_word new_size (Bool.eq_false_iff.mpr hn)
  have hnn := page_round_up_Z_nonneg (bv_unsigned old_size) (mremap_word_range old_size).1
  have halloc := alloc_top_lt (m_vmmaps m)
  have halign : bv_unsigned old % page_size = 0 := by simpa using ha
  have hcharge := mremap_move_charge_at_fresh m old _ old _ halign
    (by rw [hnw]; exact page_round_up_Z_mod _)
    (by rw [hnw]; omega) (by rw [hnw]; omega) hfit
    (region_free_app_r _ _ _ _ hfree) hna hl hp
  rw [hgate] at hm
  simp only [mremap_final_budget_b, vm_backing_within_limit,
    mremap_model_next_limit, hcharge] at hgate
  simp only [mremap_move_budget_b, hgate, Bool.true_and, Bool.not_true, Bool.false_eq_true] at hm

/-- The mprotect syscall number selects the protection arm. -/
theorem mprotect_dispatch (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    bv_unsigned i.in_sysno = 226 →
    (syscall_spec i m o ↔ mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o) := by
  intro h
  unfold syscall_spec
  apply dispatch_arm spec_table i m o Sys.Registry.Mm.Mprotect.mprotect_arm
  simp only [lookup_arm, spec_table, h]
  rfl

/-- Soundness of the brk mark through dispatch: where it fires, every
outcome the spec permits is one of `Run.refusal_b`'s refusals. The arm's
unmoved-break argument supplies the connection. -/
theorem brk_budget_refused_is_refusal (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) :
    bv_unsigned i.in_sysno = 214 → alloc_budget_refused_b i m = true →
    syscall_spec i m (Ok eff m' evs) → refusal_b i m eff.eff_ret = true := by
  intro hno hm hs
  simp +decide only [alloc_budget_refused_b, hno, ↓reduceIte] at hm
  rw [brk_dispatch i m _ hno] at hs
  simp only [brk_spec, bind_get_model_iff, bind_choose_iff, bind_modify_iff,
    Monad.pure, outcome.Ok.injEq] at hs
  obtain ⟨r, hr, heff, _, _⟩ := hs
  have hr' := brk_budget_refused_forces m (in_arg i 0) r hm hr
  rw [heff, hr']
  simp only [brk_budget_refused_b, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not] at hm
  obtain ⟨⟨⟨⟨hz, hmin⟩, _⟩, hgrow⟩, _⟩ := hm
  have hne : bv_eqb (in_arg i 0) (m_vmmaps m).vm_brk = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have he' : in_arg i 0 = (m_vmmaps m).vm_brk := by
      simpa only [bv_eqb_eq] using he
    rw [he'] at hgrow
    exact (Int.lt_irrefl _ hgrow)
  simp only [refusal_b, hno, ↓reduceIte, brk_refusal_b, hz, decide_eq_false hmin,
    hne, Bool.not_false, Bool.true_and, bv_eqb_eq]

scoped macro "budget_outcomes " hm:ident hs:ident : tactic =>
  `(tactic| (
    simp only [Bool.not_eq_true'] at $hm:ident
    simp only [mmap_spec, mprotect_spec, *, ↓reduceIte, bind_get_model_iff,
      alt, bind_errno_from_iff, mmap_errnos, mprotect_errnos, List.mem_singleton,
      exists_eq_left, err_ret, ret_only, Monad.pure, bind_choose_iff,
      bind_modify_iff, outcome.Ok.injEq, Bool.false_eq_true,
      and_false, false_and, exists_false, or_false, false_or, Bool.true_and] at $hs:ident
    solve
      | (obtain ⟨he, _, _⟩ := $hs:ident; rw [he]; rfl)
      | (rcases $hs:ident with ⟨he, _, _⟩ | ⟨he, _, _⟩ <;> rw [he] <;> rfl)))

/-- Soundness of the mmap mark over the whole arm: where it fires,
every outcome the spec permits is one of `Run.refusal_b`'s refusals.
The proof walks `mmap_spec` in the mark's order, since both use the same
`if` chain. In each charging branch the success resolution's budget
conjunct contradicts the mark; errno resolutions answer `mmap_errnos`. -/
theorem mmap_budget_refused_is_refusal (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) :
    bv_unsigned i.in_sysno = 222 → alloc_budget_refused_b i m = true →
    syscall_spec i m (Ok eff m' evs) → refusal_b i m eff.eff_ret = true := by
  intro hno hm hs
  simp +decide only [alloc_budget_refused_b, hno, ↓reduceIte] at hm
  rw [mmap_dispatch i m _ hno] at hs
  simp only [refusal_b, hno]
  change ret_in_errnos mmap_errnos eff.eff_ret = true
  unfold mmap_budget_refused_b at hm
  dsimp only at hm
  by_cases h1 : (!mmap_off_aligned_b (in_arg i 5)) = true
  · rw [ite_eq_left h1] at hm
    cases hm
  rw [ite_eq_right h1] at hm
  by_cases h2 : (!mmap_anon_b (in_arg i 3)) = true
  · rw [ite_eq_left h2] at hm
    cases hm
  rw [ite_eq_right h2] at hm
  by_cases h3 : w_is0 (in_arg i 1) = true
  · rw [ite_eq_left h3] at hm
    cases hm
  rw [ite_eq_right h3] at hm
  by_cases h4 : mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h4] at hm
    budget_outcomes hm hs
  rw [ite_eq_right h4] at hm
  by_cases h5 : mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h5] at hm
    cases hm
  rw [ite_eq_right h5] at hm
  by_cases h6 : mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h6] at hm
    cases hm
  rw [ite_eq_right h6] at hm
  by_cases h7 : mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h7] at hm
    by_cases h8 : two_pow_64 ≤ bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1))
    · rw [ite_eq_left h8] at hm
      cases hm
    rw [ite_eq_right h8] at hm
    by_cases h9 : (!(bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left h9] at hm
      cases hm
    rw [ite_eq_right h9] at hm
    by_cases h10 : (!(bv_unsigned (in_arg i 0) % page_size == 0)) = true
    · rw [ite_eq_left h10] at hm
      cases hm
    rw [ite_eq_right h10] at hm
    by_cases h11 : (!(0 < bv_unsigned (in_arg i 0))) = true
    · rw [ite_eq_left h11] at hm
      cases hm
    rw [ite_eq_right h11] at hm
    by_cases h12 : (region_free (m_vmmaps m).vm_reserved (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) && map_contains (m_vmmaps m).vm_maps (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) = true
    · rw [ite_eq_left h12] at hm
      budget_outcomes hm hs
    rw [ite_eq_right h12] at hm
    by_cases h13 : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true
    · rw [ite_eq_left h13] at hm
      budget_outcomes hm hs
    rw [ite_eq_right h13] at hm
    by_cases h14 : region_free (m_vmmaps m).vm_reserved (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true
    · rw [ite_eq_left h14] at hm
      simp only [h14, Bool.true_and] at h12
      budget_outcomes hm hs
    rw [ite_eq_right h14] at hm
    cases hm
  rw [ite_eq_right h7] at hm
  by_cases h15 : mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h15] at hm
    cases hm
  rw [ite_eq_right h15] at hm
  by_cases h16 : mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h16] at hm
    by_cases h17 : two_pow_64 ≤ bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1))
    · rw [ite_eq_left h17] at hm
      cases hm
    rw [ite_eq_right h17] at hm
    by_cases h18 : (!(bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left h18] at hm
      cases hm
    rw [ite_eq_right h18] at hm
    by_cases h19 : (!(bv_unsigned (in_arg i 0) % page_size == 0)) = true
    · rw [ite_eq_left h19] at hm
      cases hm
    rw [ite_eq_right h19] at hm
    by_cases h20 : (!(0 < bv_unsigned (in_arg i 0))) = true
    · rw [ite_eq_left h20] at hm
      cases hm
    rw [ite_eq_right h20] at hm
    by_cases h21 : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true
    · rw [ite_eq_left h21] at hm
      budget_outcomes hm hs
    rw [ite_eq_right h21] at hm
    cases hm
  rw [ite_eq_right h16] at hm
  cases hm

/-- Soundness of the mprotect mark over the whole arm: where it fires,
every outcome the spec permits is one of `Run.refusal_b`'s refusals. -/
theorem mprotect_budget_refused_is_refusal (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) :
    bv_unsigned i.in_sysno = 226 → alloc_budget_refused_b i m = true →
    syscall_spec i m (Ok eff m' evs) → refusal_b i m eff.eff_ret = true := by
  intro hno hm hs
  simp +decide only [alloc_budget_refused_b, hno, ↓reduceIte] at hm
  rw [mprotect_dispatch i m _ hno] at hs
  simp only [refusal_b, hno]
  change ret_in_errnos mprotect_errnos eff.eff_ret = true
  unfold mprotect_budget_refused_b at hm
  dsimp only at hm
  by_cases h22 : mprotect_grows_conflict_b (in_arg i 2) = true
  · rw [ite_eq_left h22] at hm
    cases hm
  rw [ite_eq_right h22] at hm
  by_cases h23 : (!(bv_unsigned (in_arg i 0) % page_size == 0)) = true
  · rw [ite_eq_left h23] at hm
    cases hm
  rw [ite_eq_right h23] at hm
  by_cases h24 : w_is0 (in_arg i 1) = true
  · rw [ite_eq_left h24] at hm
    cases hm
  rw [ite_eq_right h24] at hm
  by_cases h25 : two_pow_64 ≤ bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1))
  · rw [ite_eq_left h25] at hm
    cases hm
  rw [ite_eq_right h25] at hm
  by_cases h26 : mprotect_modeled_b (in_arg i 2) = true
  · rw [ite_eq_left h26] at hm
    by_cases h27 : (map_contains (m_vmmaps m).vm_noaccess (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) && map_contains (m_vmmaps m).vm_maps (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) = true
    · rw [ite_eq_left h27] at hm
      budget_outcomes hm hs
    rw [ite_eq_right h27] at hm
    cases hm
  rw [ite_eq_right h26] at hm
  cases hm

/-! ## First touches -/

/-- The store `sd x0, 0(a0)` (0x00053023) at 0x100 supplies an instruction
touch independently of the syscall allocator. -/
def touch_segment : Segment :=
  { seg_base := 0x100, seg_size := 4, seg_perms := "r-x", seg_bytes := ["23300500"] }

/-- The store's one-segment image. -/
def touch_segments : List Segment := [touch_segment]

/-- The store targets a page writable in the machine but lazy in the
model, isolating backing exhaustion from an interpreter access fault. -/
def touch_page : Int := 0x10000

/-- Built by hand so memory is a small function rather than an entry
stack image; `a0` directs the store into the writable lazy page. -/
def touch_ms : machine_state :=
  { ms_regs := bvmap_set 10 (Z_to_bv 64 touch_page) bvmap_empty,
    ms_fregs := bvmap_empty, ms_pc_val := Z_to_bv 64 0x100,
    ms_svc_pending := none, ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem := fun a =>
      if touch_page ≤ bv_unsigned a && bv_unsigned a < touch_page + page_size
      then some (Z_to_bv 8 0) else none,
    ms_rom := fun addr =>
      match memory_read touch_segments addr 1 with
      | some (b :: _) => some b
      | _ => none }

/-- Synthetic: the lazy range has no `vm_maps` entry, which no grant
produces. This exercises the instruction clause of the mark, not the
allocator; it is not a reachable allocation witness. -/
def touch_model (lim : Int) : Model :=
  with_vm_backing [(Z_to_bv 64 touch_page, Z_to_bv 64 page_size)] []
    (init_model (segments_reserved touch_segments) 0 0 demo_sp lim (demo_input [] IEof))

/-- Project the interpreter's step to the access report alone, the scalar
the first-touch clause reads. -/
def touch_accesses : Option (List memory_access) :=
  match step_accesses touch_segments touch_ms with
  | MachineOk r => some r.accessed_ranges
  | MachineFault | MachineUnmodeled => none

/-- The interpreter succeeds before backing is charged: its scalar
access report isolates materialization as the possible source of refusal. -/
theorem touch_store_reports_the_page :
    touch_accesses = some [(Z_to_bv 64 touch_page, 8)] := by
  simp +decide only [touch_accesses, step_accesses, decode_exec_accesses, touch_ms,
    LinuxProcessSemantics.Riscv.Sem.exec, LinuxProcessSemantics.Riscv.Sem.rget,
    reg_get, bvmap_get_set, bvmap_get_empty, ↓reduceIte]
  rfl

/-- A successful instruction access can still fail when the model
materializes its lazy page; this is the instruction clause of the mark. -/
theorem touch_on_spent_budget_is_budget_refused :
    budget_refused_at touch_segments (config.mkCfg touch_ms (touch_model 0)) := by
  refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
  have h := touch_store_reports_the_page
  unfold touch_accesses at h
  cases he : step_accesses touch_segments touch_ms with
  | MachineOk r =>
    rw [he] at h
    have hr := Option.some.inj h
    exact ⟨r, rfl, by rw [hr]; decide⟩
  | MachineFault => rw [he] at h; contradiction
  | MachineUnmodeled => rw [he] at h; contradiction

/-- Connect the instruction mark to execution: failed materialization
must actually take the error transition, not merely set a diagnostic mark. -/
theorem touch_on_spent_budget_errors :
    sstep touch_segments (config.mkCfg touch_ms (touch_model 0)) [] SError := by
  obtain ⟨_, (⟨_, r, he, hm⟩ | ⟨x8, hx8, _⟩)⟩ := touch_on_spent_budget_is_budget_refused
  · exact budget_fault_instr_sstep_error _ _ _ r rfl rfl he hm
  · cases hx8

/-- The matching touch with backing available prevents the instruction
clause from treating laziness alone as a refusal. -/
theorem touch_within_budget_is_not_budget_refused :
    ¬ budget_refused_at touch_segments (config.mkCfg touch_ms (touch_model page_size)) := by
  rintro ⟨_, (⟨_, r, he, hm⟩ | ⟨x8, hx8, _⟩)⟩
  · have h := touch_store_reports_the_page
    unfold touch_accesses at h
    rw [he] at h
    have hr := Option.some.inj h
    rw [hr] at hm
    have hn : materialize_model_accesses (touch_model page_size)
        [(Z_to_bv 64 touch_page, 8)] ≠ none := by decide
    exact hn hm
  · cases hx8

/-- An interpreter fault for its own reasons is not a budget refusal
at any budget. -/
theorem ebreak_fault_is_not_budget_refused (lim : Int) :
    ¬ budget_refused_at ebreak_segments (config.mkCfg ebreak_ms (ebreak_model lim)) := by
  rintro ⟨_, (⟨_, r, he, _⟩ | ⟨x8, hx8, _⟩)⟩
  · have hd := drop_step_accesses ebreak_segments ebreak_ms
    rw [he, ebreak_faults] at hd
    cases hd
  · cases hx8

/-- `write(1, 0x1000, 1)` touches the second lazy page through copy-in,
exercising the syscall-effect clause rather than an allocation arm. -/
def wtouch_ms : machine_state :=
  { ms_regs := bvmap_set 10 (Z_to_bv 64 1)
      (bvmap_set 11 (Z_to_bv 64 0x1000) (bvmap_set 12 (Z_to_bv 64 1) bvmap_empty)),
    ms_fregs := bvmap_empty, ms_pc_val := Z_to_bv 64 0x100,
    ms_svc_pending := some (Z_to_bv 64 64), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem := fun a => if bv_eqb a (Z_to_bv 64 0x1000) then some (Z_to_bv 8 0) else none,
    ms_rom := fun _ => none }

/-- The lazy reservation covers the first two pages; page 0 is already
charged and the budget is one page. Copying from the next page therefore
needs backing the remaining budget cannot supply. -/
def wtouch_model : Model :=
  with_vm_backing [(0, 0x2000)] [0]
    (init_model [] 0 0 demo_sp 0x1000 (demo_input [] IEof))

/-- The successful write records its copy-in access in the effect;
that access is what later materialization must charge. -/
def wtouch_eff : SyscallEffect :=
  SyscallEffect.mkEffectU 1 [] [] [] [] [(Z_to_bv 64 0x1000, 1)]

/-- The checker accepts the write before its effect is materialized,
so syscall checking alone cannot catch this exhausted first touch. -/
theorem wtouch_checker :
    check_syscall (sys_input [] wtouch_ms (Z_to_bv 64 64)) wtouch_eff wtouch_model =
      Checks.Sys.Prelude.check_result.CheckOk wtouch_model [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 0)] := by
  simp +decide only [sys_input, syscall_args, ms_gpr, wtouch_ms, reg_get,
    bvmap_get_set, bvmap_get_empty, ↓reduceIte]
  rfl

/-- Materializing the accepted write's effect fails: the effect clause
must carry the budget refusal even though write has no allocation mark. -/
theorem wtouch_is_budget_refused :
    budget_refused_at [] (config.mkCfg wtouch_ms wtouch_model) := by
  refine ⟨rfl, Or.inr ⟨Z_to_bv 64 64, rfl, Or.inr ?_⟩⟩
  exact ⟨wtouch_eff, wtouch_model, [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 0)],
    check_syscall_sound_ok _ _ _ _ _ wtouch_checker, rfl, rfl⟩

/-- Connect the effect mark to execution: an accepted syscall effect
whose materialization fails must still produce the error transition. -/
theorem wtouch_errors :
    sstep [] (config.mkCfg wtouch_ms wtouch_model) [] SError :=
  budget_fault_syscall_sstep_error [] wtouch_ms wtouch_model (Z_to_bv 64 64)
    wtouch_eff wtouch_model [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 0)]
    rfl rfl (check_syscall_sound_ok _ _ _ _ _ wtouch_checker) rfl rfl

/-! ## The allocation dispatcher -/

/-- The concrete brk refusal reaches the mark through dispatch. -/
theorem brk_dispatches_to_its_mark :
    alloc_budget_refused_b (brk_in 73728) m_tight_brk = true := by decide

/-- `Run.alloc_family_dispatched` says every `FamAlloc` number is on the
list. The brk instance is `Checks/Cases/Run.lean`'s, restated under Rocq's
name for the register. The converse dispatch connection is
`Run.alloc_mark_sysnos_dispatched`. -/
theorem brk_is_dispatched : (214 : Int) ∈ alloc_mark_sysnos := Cases.Run.brk_is_dispatched

/-- `Run.alloc_family_dispatched` says every `FamAlloc` number is on the
list. The mremap instance is `Checks/Cases/Run.lean`'s, restated under Rocq's
name for the register. The converse dispatch connection is
`Run.alloc_mark_sysnos_dispatched`. -/
theorem mremap_is_dispatched : (216 : Int) ∈ alloc_mark_sysnos := Cases.Run.mremap_is_dispatched

/-- `Run.alloc_family_dispatched` says every `FamAlloc` number is on the
list. The mmap instance is `Checks/Cases/Run.lean`'s, restated under Rocq's
name for the register. The converse dispatch connection is
`Run.alloc_mark_sysnos_dispatched`. -/
theorem mmap_is_dispatched : (222 : Int) ∈ alloc_mark_sysnos := Cases.Run.mmap_is_dispatched

/-- `Run.alloc_family_dispatched` says every `FamAlloc` number is on the
list. The mprotect instance is `Checks/Cases/Run.lean`'s, restated under Rocq's
name for the register. The converse dispatch connection is
`Run.alloc_mark_sysnos_dispatched`. -/
theorem mprotect_is_dispatched : (226 : Int) ∈ alloc_mark_sysnos := Cases.Run.mprotect_is_dispatched

/-- The other dispatcher half, `Run.alloc_mark_sysnos_dispatched`:
listed numbers reach their arm's mark. Instantiating it here complements
`Run.alloc_family_dispatched`'s coverage of registered allocation arms. -/
theorem brk_number_reaches_its_mark (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 214 →
    alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0) :=
  (alloc_mark_sysnos_dispatched i m).1

/-- Getcwd never fires an allocation mark, whatever the state. -/
theorem getcwd_is_never_budget_refused (m : Model) :
    alloc_budget_refused_b getcwd_i m = false := rfl

/-- Neither exit syscall fires an allocation mark, whatever the state. -/
theorem exit_is_never_budget_refused (i : SyscallInput) (m : Model) :
    exit_sysno i.in_sysno → alloc_budget_refused_b i m = false := by
  rintro (h | h) <;> simp +decide only [alloc_budget_refused_b, h, ↓reduceIte]

/-! ## PART 4 — run level -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
  (exits_c exits_c_must_exit_at exit_dispatch_halts exit_dispatch_not_killed
   exit0_image exit0_segments demo_entry demo_proc_input)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
open LinuxProcessSemantics.EquivalenceDefinition.Classifier (verdict_accept)
open LinuxProcessSemantics.LinuxProcessSem.StackLayout (EntryDraw)
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence

/-- The reflective evaluator accepts only instructions followed by an exit.
With no lazy mappings, instructions cannot exhaust backing, and the exit
neither allocates nor leaves a running successor. This is the budget
counterpart of `exits_c_must_exit_at`. -/
theorem exits_c_no_budget_refused (segs : List Segment) (code : word) (fuel : Nat) :
    ∀ (ms : machine_state) (model : Model),
    m_halted model = none → m_vm_lazy model = [] →
    exits_c segs code fuel ms = true →
    ¬ reaches_budget_refused segs (config.mkCfg ms model) := by
  induction fuel with
  | zero =>
    intro ms model _ _ hc
    simp only [exits_c, Bool.false_eq_true] at hc
  | succ fuel ih =>
    intro ms model hh hlazy hc
    cases hsvc : ms.ms_svc_pending with
    | some x8 =>
      simp only [exits_c, hsvc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      have hno : exit_sysno (sys_input segs ms x8).in_sysno := hc.1
      rintro ⟨tr, c, hstar, hb⟩
      cases hstar with
      | star_refl =>
        obtain ⟨_, (⟨hnone, _⟩ | ⟨y8, hy8, hm | ⟨eff, m', evs, hs, hh', _⟩⟩)⟩ := hb
        · rw [hsvc] at hnone; cases hnone
        · change ms.ms_svc_pending = some y8 at hy8
          rw [hsvc] at hy8; cases hy8
          rw [exit_is_never_budget_refused _ _ hno] at hm; cases hm
        · change ms.ms_svc_pending = some y8 at hy8
          rw [hsvc] at hy8; cases hy8
          rw [exit_dispatch_halts _ _ _ _ _ hno hs] at hh'; cases hh'
      | star_step _ evs c2 tr' _ hss htail =>
        cases hss with
        | sstep_instr _ _ _ _ _ hv _ => rw [hsvc] at hv; cases hv
        | sstep_syscall _ _ _ _ _ _ _ _ hv hs hh' _ =>
          rw [hsvc] at hv; cases hv
          rw [exit_dispatch_halts _ _ _ _ _ hno hs] at hh'; cases hh'
        | sstep_exit _ _ _ _ _ _ _ _ hv _ hh' _ =>
          rw [hsvc] at hv; cases hv
          obtain ⟨_, rfl⟩ := star_from_halted _ _ _ _ htail (by rw [hh']; nofun)
          have hn := hb.1
          change m_halted _ = none at hn
          rw [hh'] at hn; cases hn
        | sstep_killed _ _ _ _ _ _ _ _ hv hs hk =>
          rw [hsvc] at hv; cases hv
          rw [exit_dispatch_not_killed _ _ _ _ _ hno hs] at hk; cases hk
    | none =>
      simp only [exits_c, hsvc] at hc
      cases hs : RiscvSemantics.step segs ms with
      | MachineOk ms' =>
        rw [hs] at hc
        rintro ⟨tr, c, hstar, hb⟩
        cases hstar with
        | star_refl => exact budget_refused_at_no_lazy_instr segs ms model hlazy hsvc hb
        | star_step _ evs c2 tr' _ hss htail =>
          obtain ⟨_, heq⟩ := sstep_instr_only segs ms model ms' hlazy hsvc hs _ _ hss
          cases heq
          exact ih ms' model hh hlazy hc ⟨tr', c, htail, hb⟩
      | MachineFault => simp only [hs, Bool.false_eq_true] at hc
      | MachineUnmodeled => simp only [hs, Bool.false_eq_true] at hc

/-- The entry model has no lazy mapping, and `exit0_exits_c` does not
restrict placement or input. The budget premise therefore holds at every
budget for this image. -/
theorem exit0_never_budget_refused (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ run_budget_refused exit0_image lim en inp := by
  cases en
  exact exits_c_no_budget_refused _ verdict_accept 8 _ _ rfl rfl
    (exit0_exits_c _ _ _ _ _ _)

/-- Discharging the run mark is exactly the premise used by the budget
family; no allocation limit is hidden in the exit fixture. -/
theorem exit0_source_within_budget (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    source_within_budget lim exit0_image en inp := exit0_never_budget_refused lim en inp

/-- The instruction sequence requests an anonymous writable mmap larger
than its budget. The zero entry registers supply the address and offset;
none of these instructions accesses data memory. -/
def mm_segment : Segment :=
  { seg_base := 0x100, seg_size := 24, seg_perms := "r-x",
    seg_bytes := ["9308e00db725000013063000930620021307f0ff73000000"] }

/-- The allocating program's one executable segment. -/
def mm_segments : List Segment := [mm_segment]

/-- The fixture uses the same entry metadata as the other demo images. -/
def mm_image : Image := Image.mkImage mm_segments 0x100 demo_phdrs

/-- The request exceeds this backing allowance at its ecall. -/
def mm_budget : Int := page_size

/-- The demo launch supplies the zero registers used by the mmap request. -/
def mm_ms0 : machine_state :=
  init_machine_state mm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
    demo_proc_input.in_hwcap

/-- Retain the initial state if the interpreter cannot complete the walk;
the step proofs below rule out that fallback on the fixture's path. -/
def mm_msk (k : Nat) : machine_state :=
  match run_steps k mm_segments mm_ms0 with
  | some ms => ms
  | none => mm_ms0

/-- Abstract memory as in `Checks.Omni`: the straight-line instructions
leave it unchanged. -/
def mm_s (k : Nat) : machine_state := with_mem (mm_msk k) mm_ms0.ms_mem

/-- Charge the allocating run against the explicit fixture budget. -/
def mm_model : Model :=
  init_model (segments_reserved mm_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) mm_budget demo_proc_input

/-- Pair the abstracted entry state with the allocation ledger. -/
def mm_c : config := config.mkCfg (mm_s 0) mm_model

/-- Memory abstraction preserves the real initial configuration, so the
later mark is reachable from a run rather than only a hand-built state. -/
theorem mm_config :
    init_config mm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw mm_budget demo_proc_input
      = mm_c := rfl

open LinuxProcessSemantics.Common.PropExec (mkst step_of_fetch decode_exec_of_interp)

/-- Local instruction reduction over arbitrary memory: the fetch comes
from the executable image and the operation only changes register state. -/
private theorem mm_step_100 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step mm_segments (mkst r 0x100 m rom) =
      MachineOk (mkst (bvmap_set 17 222 r) 0x104 m rom) := by
  rw [step_of_fetch mm_segments (mkst r 0x100 m rom) 0x0de00893
    (by change fetch_word mm_segments 0x100 = some 0x0de00893; decide +kernel)]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 17 0 222)
    (by decide +kernel) (by decide +kernel)
  rfl

/-- Local instruction reduction over arbitrary memory: the fetch comes
from the executable image and the operation only changes register state. -/
private theorem mm_step_104 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step mm_segments (mkst r 0x104 m rom) =
      MachineOk (mkst (bvmap_set 11 8192 r) 0x108 m rom) := by
  rw [step_of_fetch mm_segments (mkst r 0x104 m rom) 0x000025b7
    (by change fetch_word mm_segments 0x104 = some 0x000025b7; decide +kernel)]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.Lui 11 2)
    (by decide +kernel) (by decide +kernel)
  rfl

/-- Local instruction reduction over arbitrary memory: the fetch comes
from the executable image and the operation only changes register state. -/
private theorem mm_step_108 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step mm_segments (mkst r 0x108 m rom) =
      MachineOk (mkst (bvmap_set 12 3 r) 0x10c m rom) := by
  rw [step_of_fetch mm_segments (mkst r 0x108 m rom) 0x00300613
    (by change fetch_word mm_segments 0x108 = some 0x00300613; decide +kernel)]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 12 0 3)
    (by decide +kernel) (by decide +kernel)
  rfl

/-- Local instruction reduction over arbitrary memory: the fetch comes
from the executable image and the operation only changes register state. -/
private theorem mm_step_10c (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step mm_segments (mkst r 0x10c m rom) =
      MachineOk (mkst (bvmap_set 13 34 r) 0x110 m rom) := by
  rw [step_of_fetch mm_segments (mkst r 0x10c m rom) 0x02200693
    (by change fetch_word mm_segments 0x10c = some 0x02200693; decide +kernel)]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 13 0 34)
    (by decide +kernel) (by decide +kernel)
  rfl

/-- Local instruction reduction over arbitrary memory: the fetch comes
from the executable image and the operation only changes register state. -/
private theorem mm_step_110 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step mm_segments (mkst r 0x110 m rom) =
      MachineOk (mkst (bvmap_set 14 (Z_to_bv 64 (-1)) r) 0x114 m rom) := by
  rw [step_of_fetch mm_segments (mkst r 0x110 m rom) 0xfff00713
    (by change fetch_word mm_segments 0x110 = some 0xfff00713; decide +kernel)]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 14 0 (-1))
    (by decide +kernel) (by decide +kernel)
  change interp_eff mm_segments
    (LinuxProcessSemantics.Riscv.Sem.eff.EDone
      (LinuxProcessSemantics.Riscv.Sem.rset 14 ((0 : word) + sext 64 (-1 : BitVec 12))
        (LinuxProcessSemantics.Riscv.Sem.core.Core r bvmap_empty 0x114 0 none))) m = _
  rw [show (0 : word) + sext 64 (-1 : BitVec 12) = Z_to_bv 64 (-1) from by decide +kernel]
  rfl

/-- The fetch comes from the executable image; the ecall leaves registers
and pc unchanged and records a7 (`reg_get r 17`) as the pending syscall. -/
private theorem mm_step_114 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step mm_segments (mkst r 0x114 m rom) =
      MachineOk ({ mkst r 0x114 m rom with ms_svc_pending := some (reg_get r 17) }) := by
  rw [step_of_fetch mm_segments (mkst r 0x114 m rom) 0x00000073
    (by change fetch_word mm_segments 0x114 = some 0x00000073; decide +kernel)]
  rfl

/-- Local bridge from the real entry state to the abstract register form;
subsequent interpreter rewrites must preserve its stack and ROM functions. -/
private theorem mm_ms0_step :
    RiscvSemantics.step mm_segments mm_ms0 =
      MachineOk (mkst (bvmap_set 17 222 mm_ms0.ms_regs) 0x104 mm_ms0.ms_mem mm_ms0.ms_rom) :=
  mm_step_100 mm_ms0.ms_regs mm_ms0.ms_mem mm_ms0.ms_rom

/-- Local normal form of the interpreter walk, exposing registers while
keeping the entry stack memory abstract for subsequent rewrites. -/
private theorem mm_msk_0 : mm_msk 0 = mkst mm_ms0.ms_regs 0x100 mm_ms0.ms_mem mm_ms0.ms_rom := by
  rfl

/-- Local normal form of the interpreter walk, exposing registers while
keeping the entry stack memory abstract for subsequent rewrites. -/
private theorem mm_msk_1 : mm_msk 1 = mkst (bvmap_set 17 222 mm_ms0.ms_regs) 0x104 mm_ms0.ms_mem mm_ms0.ms_rom := by
  unfold mm_msk
  rw [run_steps_ok _ _ _ _ mm_ms0_step]
  rfl

/-- Local normal form of the interpreter walk, exposing registers while
keeping the entry stack memory abstract for subsequent rewrites. -/
private theorem mm_msk_2 : mm_msk 2 = mkst (bvmap_set 11 8192 (bvmap_set 17 222 mm_ms0.ms_regs)) 0x108 mm_ms0.ms_mem mm_ms0.ms_rom := by
  unfold mm_msk
  rw [run_steps_ok _ _ _ _ mm_ms0_step,
    run_steps_ok _ _ _ _ (mm_step_104 _ _ _)]
  rfl

/-- Local normal form of the interpreter walk, exposing registers while
keeping the entry stack memory abstract for subsequent rewrites. -/
private theorem mm_msk_3 : mm_msk 3 = mkst (bvmap_set 12 3 (bvmap_set 11 8192 (bvmap_set 17 222 mm_ms0.ms_regs))) 0x10c mm_ms0.ms_mem mm_ms0.ms_rom := by
  unfold mm_msk
  rw [run_steps_ok _ _ _ _ mm_ms0_step,
    run_steps_ok _ _ _ _ (mm_step_104 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_108 _ _ _)]
  rfl

/-- Local normal form of the interpreter walk, exposing registers while
keeping the entry stack memory abstract for subsequent rewrites. -/
private theorem mm_msk_4 : mm_msk 4 = mkst (bvmap_set 13 34 (bvmap_set 12 3 (bvmap_set 11 8192 (bvmap_set 17 222 mm_ms0.ms_regs)))) 0x110 mm_ms0.ms_mem mm_ms0.ms_rom := by
  unfold mm_msk
  rw [run_steps_ok _ _ _ _ mm_ms0_step,
    run_steps_ok _ _ _ _ (mm_step_104 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_108 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_10c _ _ _)]
  rfl

/-- Local normal form of the interpreter walk, exposing registers while
keeping the entry stack memory abstract for subsequent rewrites. -/
private theorem mm_msk_5 : mm_msk 5 = mkst (bvmap_set 14 (Z_to_bv 64 (-1)) (bvmap_set 13 34 (bvmap_set 12 3 (bvmap_set 11 8192 (bvmap_set 17 222 mm_ms0.ms_regs))))) 0x114 mm_ms0.ms_mem mm_ms0.ms_rom := by
  unfold mm_msk
  rw [run_steps_ok _ _ _ _ mm_ms0_step,
    run_steps_ok _ _ _ _ (mm_step_104 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_108 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_10c _ _ _),
    run_steps_ok _ _ _ _ (mm_step_110 _ _ _)]
  rfl

/-- Local normal form of the interpreter walk, exposing registers while
keeping the entry stack memory abstract for subsequent rewrites. -/
private theorem mm_msk_6 : mm_msk 6 = { mkst (bvmap_set 14 (Z_to_bv 64 (-1)) (bvmap_set 13 34 (bvmap_set 12 3 (bvmap_set 11 8192 (bvmap_set 17 222 mm_ms0.ms_regs))))) 0x114 mm_ms0.ms_mem mm_ms0.ms_rom with ms_svc_pending := some (reg_get (bvmap_set 14 (Z_to_bv 64 (-1)) (bvmap_set 13 34 (bvmap_set 12 3 (bvmap_set 11 8192 (bvmap_set 17 222 mm_ms0.ms_regs))))) 17) } := by
  unfold mm_msk
  rw [run_steps_ok _ _ _ _ mm_ms0_step,
    run_steps_ok _ _ _ _ (mm_step_104 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_108 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_10c _ _ _),
    run_steps_ok _ _ _ _ (mm_step_110 _ _ _),
    run_steps_ok _ _ _ _ (mm_step_114 _ _ _)]
  rfl

/-- The straight-line walk leaves arbitrary data memory untouched;
only register setup and the pending ecall matter to this witness. -/
theorem mm_step (k : Nat) (hk : k < 6) (mem : word → Option byte) :
    RiscvSemantics.step mm_segments (with_mem (mm_msk k) mem) =
      MachineOk (with_mem (mm_msk (k + 1)) mem) := by
  match k, hk with
  | 0, _ => rw [mm_msk_0, mm_msk_1]; exact mm_step_100 _ _ _
  | 1, _ => rw [mm_msk_1, mm_msk_2]; exact mm_step_104 _ _ _
  | 2, _ => rw [mm_msk_2, mm_msk_3]; exact mm_step_108 _ _ _
  | 3, _ => rw [mm_msk_3, mm_msk_4]; exact mm_step_10c _ _ _
  | 4, _ => rw [mm_msk_4, mm_msk_5]; exact mm_step_110 _ _ _
  | 5, _ => rw [mm_msk_5, mm_msk_6]; exact mm_step_114 _ _ _
  | k + 6, hk => omega

/-- No first touch intervenes before the mmap request: the initial ledger
has no lazy mappings, so the instruction walk is also a run walk. -/
theorem mm_instr_sstep (k : Nat) (hk : k < 6) :
    sstep mm_segments (config.mkCfg (mm_s k) mm_model) []
      (SNext (config.mkCfg (mm_s (k + 1)) mm_model)) := by
  apply sstep.sstep_instr
  · rfl
  · match k, hk with
    | 0, _ => unfold mm_s; rw [mm_msk_0]; rfl
    | 1, _ => unfold mm_s; rw [mm_msk_1]; rfl
    | 2, _ => unfold mm_s; rw [mm_msk_2]; rfl
    | 3, _ => unfold mm_s; rw [mm_msk_3]; rfl
    | 4, _ => unfold mm_s; rw [mm_msk_4]; rfl
    | 5, _ => unfold mm_s; rw [mm_msk_5]; rfl
    | k + 6, hk => omega
  · no_lazy
    rw [show RiscvSemantics.step mm_segments (mm_s k) = MachineOk (mm_s (k + 1)) from
      mm_step k hk _]

/-- The final instruction raises the mmap ecall rather than an unrelated
syscall, connecting the instruction fixture to the allocation mark. -/
theorem mm_svc6 : (mm_s 6).ms_svc_pending = some (Z_to_bv 64 222) := by
  unfold mm_s
  rw [mm_msk_6]
  decide +kernel

/-- Compose the instruction transitions without a syscall answer: the
premise excludes reaching the mark, independently of the refusal chosen. -/
theorem mm_star : star mm_segments mm_c [] (config.mkCfg (mm_s 6) mm_model) := by
  exact star.star_step _ [] _ [] _ (mm_instr_sstep 0 (by decide))
    (star.star_step _ [] _ [] _ (mm_instr_sstep 1 (by decide))
    (star.star_step _ [] _ [] _ (mm_instr_sstep 2 (by decide))
    (star.star_step _ [] _ [] _ (mm_instr_sstep 3 (by decide))
    (star.star_step _ [] _ [] _ (mm_instr_sstep 4 (by decide))
    (star.star_step _ [] _ [] _ (mm_instr_sstep 5 (by decide)) (star.star_refl _))))))

/-- At the ecall the grant clause fires; this is allocation exhaustion,
rather than an instruction fault or a first-touch refusal. -/
theorem mm_ecall_is_budget_refused :
    budget_refused_at mm_segments (config.mkCfg (mm_s 6) mm_model) := by
  refine ⟨rfl, Or.inr ⟨Z_to_bv 64 222, mm_svc6, Or.inl ?_⟩⟩
  unfold mm_s
  rw [mm_msk_6]
  decide +kernel

/-- The allocating witness is a valid launch, so its excluded run exercises
an input quantified by the budget-family contract. -/
theorem demo_entry_valid_mm (inp : ProcInput) (hi : valid_input inp) :
    valid_entry mm_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)]
  have hargv : valid_argv inp.in_argv := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have henvp : valid_envp inp.in_envp := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega


/-- Pin the actual image, entry and input together, independently of the
reachability proof's unvalidated parameters. -/
theorem mm_valid_launch :
    valid_input demo_proc_input ∧ valid_entry mm_image demo_entry demo_proc_input :=
  ⟨demo_input_valid, demo_entry_valid_mm _ demo_input_valid⟩

/-- Reject an entry whose break lies below this image, so the validity
pin cannot be replaced by an unconditional claim about demo launches. -/
theorem mm_entry_below_image_rejected :
    ¬ valid_entry mm_image { demo_entry with en_brk := 0 } demo_proc_input := by
  intro h
  have hb := h.2.1
  have hn : ¬ valid_brk mm_segments 0 := by unfold valid_brk; decide +kernel
  exact hn hb

/-- The concrete walk witnesses reachability from the image's demo entry,
so the budget premise has a real excluded run. -/
theorem mm_run_budget_refused :
    run_budget_refused mm_image mm_budget demo_entry demo_proc_input := by
  change reaches_budget_refused mm_segments
    (init_config mm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw mm_budget demo_proc_input)
  rw [mm_config]
  exact reaches_budget_refused_star _ _ _ _ mm_star
    (reaches_budget_refused_intro _ _ mm_ecall_is_budget_refused)

/-- The budget family is not the constant-pinned family under another
name: its source premise excludes this allocating run. -/
theorem mm_not_within_budget :
    ¬ source_within_budget mm_budget mm_image demo_entry demo_proc_input :=
  fun h => h mm_run_budget_refused

/-- The exit image never touches the heap, so its error-free budget contract
holds at every pair of limits. The seal theorems below state it at the shipped
constants, the ascription a generated Checker would make;
`tools/gen_checker.py` does not emit that ascription yet. -/
theorem exit0_strong_universal_error_free_budgets (lim_source lim_target : Int) :
    strong_universal_error_free_T_budgets lim_source lim_target exit0_image exit0_image := by
  rintro ⟨sps, brks, mbs, rnds⟩ ⟨spt, brkt, mbt, rndt⟩ inp _ _ _ _
  refine ⟨(error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _),
    (error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _), ?_⟩
  intro tr
  exact (exit0_obs _ _ _ _ _ _ tr).trans (exit0_obs _ _ _ _ _ _ tr).symm

/-! `EquivalenceDefinition/Equivalence/Budgets.lean` registers the budget module
types (`SPEC_*_BUDGETS*`) and the `ShippedBudgets` instance as `unported`, with
no Lean surface. The seals here are therefore theorems at the shipped constants
`source_alloc_limit` / `target_alloc_limit`. -/

/-- The content of Rocq's `Exit0BudgetsChecked` module seal. -/
theorem exit0_budgets_checked :
    strong_universal_error_free_T_budgets source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  exit0_strong_universal_error_free_budgets source_alloc_limit target_alloc_limit

/-- The exit trace contains no signal death. This supplies the extra
obligation of the abort-declared contract without relying on its input
validity premise. -/
theorem exit0_never_dies_by_signal (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ dies_by_signal (run exit0_image lim en inp) := by
  rcases en with ⟨sp, brk0, mbase, rnd⟩
  rintro ⟨tr, sig, fs, htr, hin⟩
  have hp := (exit0_obs _ _ _ _ _ _ tr).1 htr
  cases tr with
  | nil => cases hin
  | cons e tr =>
    obtain ⟨rfl, hp⟩ := hp
    cases tr with
    | nil => simp only [List.mem_singleton] at hin; cases hin
    | cons _ _ => exact hp.elim

/-- The abort twin needs both error freedom and absence of signal death.
The exit image's exact trace supplies the latter at every placement. -/
theorem exit0_strong_universal_error_free_budgets_abort (lim_source lim_target : Int) :
    strong_universal_error_free_T_budgets_abort lim_source lim_target exit0_image exit0_image := by
  rintro ⟨sps, brks, mbs, rnds⟩ ⟨spt, brkt, mbt, rndt⟩ inp _ _ _ _
  refine ⟨⟨(error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _),
    exit0_never_dies_by_signal _ _ _⟩,
    ⟨(error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _),
    exit0_never_dies_by_signal _ _ _⟩, ?_⟩
  intro tr
  exact (exit0_obs _ _ _ _ _ _ tr).trans (exit0_obs _ _ _ _ _ _ tr).symm

/-- The content of Rocq's `Exit0BudgetsAbortChecked` module seal. -/
theorem exit0_budgets_abort_checked :
    strong_universal_error_free_T_budgets_abort source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  exit0_strong_universal_error_free_budgets_abort source_alloc_limit target_alloc_limit

/-- A task's constant-pinned error-free proof transfers to the budget
surface at the shipped constants without proving the run again. -/
theorem exit0_budgets_from_pinned :
    strong_universal_error_free_T exit0_image exit0_image →
    strong_universal_error_free_T_budgets source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  strong_universal_error_free_T_budgets_of_pinned _ _

/-! ## PART 5 — the configured family and the either pair -/

/-- Instructions and the exit have no injected refusal to filter. A
configured exit witness therefore survives under every configuration. -/
theorem exit0_must_exit_at_cfg (cfg : SpuriousCfg) (sp brk0 mbase : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) :
    must_exit_at_cfg cfg exit0_segments verdict_accept
      (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) :=
  exits_c_must_exit_at_cfg _ _ _ 8 _ _ rfl rfl (exit0_exits_c _ _ _ _ _ _)

/-- Filtering gives the forward inclusion. Realizing the configured exit
supplies the reverse inclusion, so a configuration cannot silently delete
the exit image's observable behavior. -/
theorem exit0_obs_cfg (cfg : SpuriousCfg) (sp brk0 mbase : word) (rnd : EntryDraw)
    (lim : Int) (inp : ProcInput) (tr : List event) :
    obs_trace_cfg exit0_segments cfg
      (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) tr ↔
    is_prefix tr [ExitEv verdict_accept inp.in_fs] := by
  constructor
  · intro h
    exact (exit0_obs _ _ _ _ _ _ _).1 (obs_trace_cfg_sub _ _ _ _ h)
  · intro hp
    obtain ⟨tr0, fs, c', hstar, _⟩ := must_exit_at_cfg_realizes _ _ _ _
      (exit0_must_exit_at_cfg cfg sp brk0 mbase rnd lim inp) rfl
    have hfull := (exit0_obs _ _ _ _ _ _ _).1
      (obs_trace_cfg_sub _ _ _ _ ⟨tr0 ++ [ExitEv verdict_accept fs], c', hstar,
        is_prefix_refl _⟩)
    cases tr0 with
    | nil =>
      have heq := hfull.1
      cases heq
      exact ⟨_, c', hstar, hp⟩
    | cons e tr0 =>
      cases tr0 with
      | nil => exact hfull.2.elim
      | cons _ _ => exact hfull.2.elim

/-- The filtered trace set is still the exit event's prefixes, while
filtering preserves error freedom. Neither budget nor configuration
needs to be pinned for this pair. -/
theorem exit0_strong_universal_error_free_budgets_scfg
    (cfg : SpuriousCfg) (lim_source lim_target : Int) :
    strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target exit0_image exit0_image := by
  rintro ⟨sps, brks, mbs, rnds⟩ ⟨spt, brkt, mbt, rndt⟩ inp _ _ _ _
  refine ⟨error_free_scfg_of_error_free _ _ _ _ _
    ((error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _)),
    error_free_scfg_of_error_free _ _ _ _ _
    ((error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _)), ?_⟩
  intro tr
  exact (exit0_obs_cfg _ _ _ _ _ _ _ tr).trans (exit0_obs_cfg _ _ _ _ _ _ _ tr).symm

/-- The content of Rocq's `Exit0ScfgBudgetsChecked` module seal.
Rocq's `ForcedOnlyCfg` seal (theories/LinuxProcessSem/Checks/BudgetPremise.v:1435-1437)
is the choice `cfg := forced_only_cfg`, which this theorem and the other
scfg seal theorems in this file instantiate directly. -/
theorem exit0_scfg_budgets_checked :
    strong_universal_error_free_T_scfg_budgets Run.forced_only_cfg source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  exit0_strong_universal_error_free_budgets_scfg _ _ _

/-- The content of Rocq's `Exit0ScfgBudgetsBaselineChecked` module seal. -/
theorem exit0_scfg_budgets_baseline_checked :
    strong_universal_T_scfg_budgets Run.forced_only_cfg source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  strong_universal_error_free_T_scfg_budgets_implies _ _ _ _ _ exit0_scfg_budgets_checked

/-- The unfiltered premise suffices under every configuration. A caller
need not reprove the absence of marks after filtering executions. -/
theorem exit0_source_within_budget_scfg (cfg : SpuriousCfg) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    source_within_budget_scfg cfg lim exit0_image en inp :=
  source_within_budget_scfg_of_source_within_budget _ _ _ _ _
    (exit0_source_within_budget lim en inp)

/-- The content of Rocq's `Exit0BudgetsEitherChecked` module seal. -/
theorem exit0_budgets_either_checked :
    strong_universal_error_free_T_budgets_either source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  ⟨exit0_strong_universal_error_free_budgets _ _,
    exit0_strong_universal_error_free_budgets_abort _ _⟩

/-- The content of Rocq's `Exit0BudgetsEitherBaselineChecked` module seal. -/
theorem exit0_budgets_either_baseline_checked :
    strong_universal_T_budgets_either source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  strong_universal_error_free_T_budgets_either_implies _ _ _ _ exit0_budgets_either_checked

/-- A filter removes a refusal only when a non-refusal is possible at the
same state. The whole-arm soundness facts rule that out for these marks.
Mremap is deliberately absent: its mark can fire while a move still fits. -/
theorem mark_is_never_spurious (cfg : SpuriousCfg) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) :
    bv_unsigned i.in_sysno ∈ ([214, 222, 226] : List Int) →
    alloc_budget_refused_b i m = true → ¬ spurious_refusal_cfg cfg i m eff := by
  rintro hno hm ⟨_, _, eff', m', evs', hs, hnr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
  rcases hno with hno | hno | hno
  · rw [brk_budget_refused_is_refusal _ _ _ _ _ hno hm hs] at hnr; cases hnr
  · rw [mmap_budget_refused_is_refusal _ _ _ _ _ hno hm hs] at hnr; cases hnr
  · rw [mprotect_budget_refused_is_refusal _ _ _ _ _ hno hm hs] at hnr; cases hnr

/-- A marked allocation step cannot be filtered away: the refusal is
forced. Terminal and uncovered transitions already survive every filter. -/
theorem marked_step_is_configured (cfg : SpuriousCfg) (segs : List Segment)
    (ms : machine_state) (model : Model) (x8 : word) (evs : List event) (st : step_to) :
    ms.ms_svc_pending = some x8 → bv_unsigned x8 ∈ ([214, 222, 226] : List Int) →
    alloc_budget_refused_b (sys_input segs ms x8) model = true →
    sstep segs (config.mkCfg ms model) evs st →
    sstep_cfg segs cfg (config.mkCfg ms model) evs st := by
  intro hv hn hm hs
  cases hs with
  | sstep_instr _ _ _ _ _ hv' _ => rw [hv] at hv'; cases hv'
  | sstep_instr_fault _ _ _ hv' _ => rw [hv] at hv'; cases hv'
  | sstep_instr_unmodeled _ _ _ hv' _ => rw [hv] at hv'; cases hv'
  | sstep_syscall _ _ _ eff m' m'' evs' hh hv' hspec hh' hmat =>
    rw [hv] at hv'; cases hv'
    exact sstep_cfg.sstep_cfg_syscall _ _ _ _ _ _ _ hh hv hspec
      (mark_is_never_spurious _ _ _ _ hn hm) hh' hmat
  | sstep_syscall_materialization_fault _ _ _ eff m' evs' hh hv' hspec hh' hmat =>
    rw [hv] at hv'; cases hv'
    exact sstep_cfg.sstep_cfg_syscall_materialization_fault _ _ _ _ _ _ hh hv hspec
      (mark_is_never_spurious _ _ _ _ hn hm) hh' hmat
  | sstep_exit _ _ _ eff m' evs' code hh hv' hspec hh' hk =>
    exact sstep_cfg.sstep_cfg_exit _ _ _ _ _ _ _ hh hv' hspec hh' hk
  | sstep_killed _ _ _ eff m' evs' sig hh hv' hspec hk =>
    exact sstep_cfg.sstep_cfg_killed _ _ _ _ _ _ _ hh hv' hspec hk
  | sstep_syscall_unmodeled _ _ _ hh hv' hspec =>
    exact sstep_cfg.sstep_cfg_syscall_unmodeled _ _ _ hh hv' hspec

/-- Twin of Rocq's `Checks/Examples.v` `demo_entry_valid_exit0`, which no Lean
module ports yet; needed for a valid target in the refutations.
The image lies in the first page; the argument and environment bounds
provide the entry-stack room, independently of the program's behavior. -/
private theorem demo_entry_valid_exit0 (inp : ProcInput) (hi : valid_input inp) :
    valid_entry exit0_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)]
  have hargv : valid_argv inp.in_argv := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have henvp : valid_envp inp.in_envp := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- A refutation must fire at a valid triple, rather than merely state
unreachable hypotheses. The faulting image fits the demo entry and its
stack bound follows from the launch's argument and environment validity. -/
theorem demo_entry_valid_ebreak (inp : ProcInput) (hi : valid_input inp) :
    valid_entry ebreak_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)]
  have hargv : valid_argv inp.in_argv := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have henvp : valid_envp inp.in_envp := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- Ebreak allocates nothing and faults immediately. The identical error
transition used by exhausted touches must not make this a budget refusal. -/
theorem ebreak_source_within_budget (lim : Int) :
    source_within_budget lim ebreak_image demo_entry demo_proc_input := by
  change ¬ reaches_budget_refused ebreak_segments
    (init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input)
  rw [ebreak_config]
  rintro ⟨tr, c, hs, hb⟩
  cases hs with
  | star_refl => exact ebreak_fault_is_not_budget_refused lim hb
  | star_step _ _ _ _ _ hss _ =>
    have he := (ebreak_only _ _ _ hss).2
    cases he

/-- The fault is a real source error at every budget, so it can exercise
the error-free contract's refutation lemma while satisfying its premise. -/
theorem ebreak_errors (lim : Int) :
    (run ebreak_image lim demo_entry demo_proc_input).bh_errors := by
  change reaches_error ebreak_segments
    (init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input)
  rw [ebreak_config]
  refine ⟨[], _, [], star.star_refl _, sstep.sstep_instr_fault _ _ rfl rfl ?_⟩
  no_lazy
  rw [ebreak_faults]

/-- Filtering syscall refusals cannot remove an instruction fault. This
keeps the configured refutation non-vacuous under every configuration. -/
theorem ebreak_errors_cfg (cfg : SpuriousCfg) (lim : Int) :
    (run_scfg cfg ebreak_image lim demo_entry demo_proc_input).bh_errors := by
  change reaches_error_cfg ebreak_segments cfg
    (init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input)
  rw [ebreak_config]
  refine ⟨[], _, [], star_cfg.star_cfg_refl _, sstep_cfg.sstep_cfg_instr_fault _ _ rfl rfl ?_⟩
  no_lazy
  rw [ebreak_faults]

/-- Fire the refutation against a target with a valid entry: no budget the
premise accepts excuses an unrelated instruction error. -/
theorem ebreak_refutes_error_free_budgets (lim_source lim_target : Int) :
    ¬ strong_universal_error_free_T_budgets lim_source lim_target ebreak_image exit0_image :=
  strong_universal_error_free_T_budgets_refuted_by_source_error _ _ _ _
    demo_entry demo_entry demo_proc_input
    (demo_entry_valid_ebreak _ demo_input_valid) (demo_entry_valid_exit0 _ demo_input_valid)
    demo_input_valid (ebreak_source_within_budget _) (ebreak_errors _)

/-- Fire the configured refutation too. A filter on injected refusals
cannot turn this erroring source into an error-free pair. -/
theorem ebreak_refutes_error_free_scfg_budgets (cfg : SpuriousCfg)
    (lim_source lim_target : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target
      ebreak_image exit0_image :=
  strong_universal_error_free_T_scfg_budgets_refuted_by_source_error _ _ _ _ _
    demo_entry demo_entry demo_proc_input
    (demo_entry_valid_ebreak _ demo_input_valid) (demo_entry_valid_exit0 _ demo_input_valid)
    demo_input_valid
    (source_within_budget_scfg_of_source_within_budget _ _ _ _ _ (ebreak_source_within_budget _))
    (ebreak_errors_cfg _ _)

/-! ## PART 6 — the abort-declared configured budget cell -/

/-- `Checks.Cases.Run.hwcap_abort_input demo_hwcap` agrees with Rocq's
`Checks/AbortWitness.v` `abrt_input`. Only the abort declaration differs
from the ordinary demo launch. -/
abbrev abrt_input : ProcInput := Cases.Run.hwcap_abort_input demo_hwcap

/-- The declared fixture supplies a valid abort-stance launch, so the
later refutation actually tests that stance rather than an invalid input. -/
private theorem abrt_input_valid : valid_input_abort abrt_input :=
  valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Cases.Run.hwcap_abort_input_gc_declared

/-- Entry validity reads the argument and environment clauses shared by
both stances. Declaring abort terminal therefore does not invalidate the
exit image's demo entry. -/
theorem demo_entry_valid_exit0_abort (inp : ProcInput) (hi : valid_input_abort inp) :
    valid_entry exit0_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_abort_va_size inp hi)]
  have hargv : valid_argv inp.in_argv := by
    unfold valid_input_abort at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have henvp : valid_envp inp.in_envp := by
    unfold valid_input_abort at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- The configured exit trace has no signal event. The abort declaration
changes no instruction or exit step of this image. -/
theorem exit0_never_dies_by_signal_cfg (cfg : SpuriousCfg) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    ¬ dies_by_signal (run_scfg cfg exit0_image lim en inp) := by
  rcases en with ⟨sp, brk0, mbase, rnd⟩
  rintro ⟨tr, sig, fs, htr, hin⟩
  have hp := (exit0_obs_cfg _ _ _ _ _ _ _ tr).1 htr
  cases tr with
  | nil => cases hin
  | cons e tr =>
    obtain ⟨rfl, hp⟩ := hp
    cases tr with
    | nil => simp only [List.mem_singleton] at hin; cases hin
    | cons _ _ => exact hp.elim

/-- Error freedom survives filtering and the exit trace excludes signal
death. Together these discharge the abort-declared configured contract
without pinning the configuration or either budget. -/
theorem exit0_strong_universal_error_free_budgets_scfg_abort (cfg : SpuriousCfg)
    (lim_source lim_target : Int) :
    strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target
      exit0_image exit0_image := by
  rintro ⟨sps, brks, mbs, rnds⟩ ⟨spt, brkt, mbt, rndt⟩ inp _ _ _ _
  refine ⟨⟨error_free_scfg_of_error_free _ _ _ _ _
    ((error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _)),
    exit0_never_dies_by_signal_cfg _ _ _ _⟩,
    ⟨error_free_scfg_of_error_free _ _ _ _ _
    ((error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _)),
    exit0_never_dies_by_signal_cfg _ _ _ _⟩, ?_⟩
  intro tr
  exact (exit0_obs_cfg _ _ _ _ _ _ _ tr).trans (exit0_obs_cfg _ _ _ _ _ _ _ tr).symm

/-- The content of Rocq's `Exit0ScfgBudgetsAbortChecked` module seal. -/
theorem exit0_scfg_budgets_abort_checked :
    strong_universal_error_free_T_scfg_budgets_abort Run.forced_only_cfg
      source_alloc_limit target_alloc_limit exit0_image exit0_image :=
  exit0_strong_universal_error_free_budgets_scfg_abort _ _ _

/-- The content of Rocq's `Exit0ScfgBudgetsAbortBaselineChecked` module seal. -/
theorem exit0_scfg_budgets_abort_baseline_checked :
    strong_universal_T_scfg_budgets_abort Run.forced_only_cfg
      source_alloc_limit target_alloc_limit exit0_image exit0_image :=
  strong_universal_error_free_T_scfg_budgets_abort_implies _ _ _ _ _
    exit0_scfg_budgets_abort_checked

/-- Ebreak faults before any syscall; the abort declaration only changes
the model's flag and never comes into play in this instruction walk. -/
def ebreak_model_abort (lim : Int) : Model :=
  init_model (segments_reserved ebreak_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim abrt_input

/-- The entry does not read the abort flag, so the declared launch has the
ordinary ebreak machine state; only its model carries the declaration. -/
theorem ebreak_config_abort (lim : Int) :
    init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim abrt_input =
      config.mkCfg ebreak_ms (ebreak_model_abort lim) := rfl

/-- The declaration cannot create another transition before the faulting
instruction. No syscall is reached at which the flag could matter. -/
theorem ebreak_only_abort (lim : Int) (evs : List event) (st : step_to) :
    sstep ebreak_segments (config.mkCfg ebreak_ms (ebreak_model_abort lim)) evs st →
    evs = [] ∧ st = SError :=
  sstep_fault_only _ _ _ rfl rfl ebreak_faults evs st

/-- Generalize the ordinary ebreak budget control to any adjacent model:
the interpreter faults before any successful access report can request
backing, and there is no pending syscall. -/
theorem ebreak_fault_is_not_budget_refused_any (model : Model) :
    ¬ budget_refused_at ebreak_segments (config.mkCfg ebreak_ms model) := by
  rintro ⟨_, (⟨_, r, he, _⟩ | ⟨x8, hx8, _⟩)⟩
  · have hd := drop_step_accesses ebreak_segments ebreak_ms
    rw [he, ebreak_faults] at hd
    cases hd
  · cases hx8

/-- The abort refutation also needs a valid source entry. As for the exit
image, the shared argument and environment bounds supply stack room;
the declaration does not affect this placement argument. -/
theorem demo_entry_valid_ebreak_abort (inp : ProcInput) (hi : valid_input_abort inp) :
    valid_entry ebreak_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_abort_va_size inp hi)]
  have hargv : valid_argv inp.in_argv := by
    unfold valid_input_abort at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have henvp : valid_envp inp.in_envp := by
    unfold valid_input_abort at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- The declared source still satisfies the budget premise: its only
instruction faults for its own reason before any allocation or touch. -/
theorem ebreak_source_within_budget_abort (lim : Int) :
    source_within_budget lim ebreak_image demo_entry abrt_input := by
  change ¬ reaches_budget_refused ebreak_segments
    (init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim abrt_input)
  rw [ebreak_config_abort]
  rintro ⟨tr, c, hs, hb⟩
  cases hs with
  | star_refl => exact ebreak_fault_is_not_budget_refused_any _ hb
  | star_step _ _ _ _ _ hss _ =>
    have he := (ebreak_only_abort _ _ _ hss).2
    cases he

/-- The abort declaration leaves the instruction error untouched, and no
configuration filters it. This supplies the actual error witness for the
abort-declared refutation. -/
theorem ebreak_errors_cfg_abort (cfg : SpuriousCfg) (lim : Int) :
    (run_scfg cfg ebreak_image lim demo_entry abrt_input).bh_errors := by
  change reaches_error_cfg ebreak_segments cfg
    (init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim abrt_input)
  rw [ebreak_config_abort]
  refine ⟨[], _, [], star_cfg.star_cfg_refl _, sstep_cfg.sstep_cfg_instr_fault _ _ rfl rfl ?_⟩
  no_lazy
  rw [ebreak_faults]

/-- Fire the refutation under the abort declaration at a valid source,
target and input. No budget the premise accepts hides the unrelated
instruction fault in this configured cell either. -/
theorem ebreak_refutes_error_free_scfg_budgets_abort (cfg : SpuriousCfg)
    (lim_source lim_target : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target
      ebreak_image exit0_image :=
  strong_universal_error_free_T_scfg_budgets_abort_refuted_by_source_error _ _ _ _ _
    demo_entry demo_entry abrt_input
    (demo_entry_valid_ebreak_abort _ abrt_input_valid) (demo_entry_valid_exit0_abort _ abrt_input_valid)
    abrt_input_valid
    (source_within_budget_scfg_of_source_within_budget _ _ _ _ _ (ebreak_source_within_budget_abort _))
    (ebreak_errors_cfg_abort _ _)

end LinuxProcessSemantics.LinuxProcessSem.Checks.BudgetPremise
