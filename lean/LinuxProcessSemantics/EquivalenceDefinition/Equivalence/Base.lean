-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/Equivalence.v
import LinuxProcessSemantics.LinuxProcessSem.Run

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # The baseline program-equivalence contract

Mirrors the corresponding declarations of `theories/EquivalenceDefinition/Equivalence.v`.
Image checks are predicates about loaded bytes, separate from the universal
program theorem; neither can replace the other.
-/

namespace LinuxProcessSemantics.EquivalenceDefinition.Equivalence

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

def trace_equiv (T1 T2 : List event → Prop) : Prop := ∀ tr, T1 tr ↔ T2 tr

def equiv (source target : behavior) : Prop :=
  source.bh_all_errors ∨
    (trace_equiv source.bh_traces target.bh_traces ∧ ¬ target.bh_errors)

def modeled (b : behavior) : Prop := ¬ b.bh_unmodeled
def error_free (b : behavior) : Prop := ¬ b.bh_errors

def strong_equiv (source_image target_image : Image) (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  modeled (run source_image source_alloc_limit en_source inp) ∧
  equiv (run source_image source_alloc_limit en_source inp)
    (run target_image target_alloc_limit en_target inp)

def strong_universal_T (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → strong_equiv source_image target_image en_source en_target inp

def image_entry_fetchable (segs : List Segment) (pc : Nat) : Bool :=
  let addr := Z_to_bv 64 (pc : Int)
  match fetch_word segs addr with
  | some _ => true
  | none =>
    match fetch_word_wx segs addr with
    | some _ => true
    | none => (fetch_tail_any segs (fun _ => none) addr).isSome

def image_phdrs_readable (segs : List Segment) (ph : PhdrInfo) : Bool :=
  decide (0 < ph.ph_num) && decide (0 < ph.ph_ent) &&
    (memory_read segs (Z_to_bv 64 (ph.ph_addr : Int)) (ph.ph_num * ph.ph_ent)).isSome

def image_brk_witness (segs : List Segment) : Int :=
  page_size * ((reserved_top (segments_reserved segs) + (page_size - 1)) / page_size)

def image_brk_satisfiable (segs : List Segment) : Bool :=
  decide (image_brk_witness segs < 2 ^ 64)

/-- The entry check bites: nothing is fetchable in an image with no
segments, at any entry point. The checkers assert
`image_entry_fetchable = true`, so a predicate that held of every image
would say nothing. -/
theorem image_entry_fetchable_nil (pc : Nat) : image_entry_fetchable [] pc = false := by
  have hfw : ∀ addr : word, fetch_word [] addr = none := by
    intro addr
    unfold fetch_word
    split <;> rfl
  have hfwx : ∀ addr : word, fetch_word_wx [] addr = none := by
    intro addr
    unfold fetch_word_wx
    split <;> rfl
  have hta : ∀ (m : word → Option byte) (addr : word), fetch_tail_any [] m addr = none := by
    intro m addr
    unfold fetch_tail_any
    split <;> rfl
  simp [image_entry_fetchable, hfw, hfwx, hta]

/-- The header check bites on its read half: nothing is readable in an
image with no loaded segment. -/
theorem image_phdrs_readable_nil (ph : PhdrInfo) : image_phdrs_readable [] ph = false := by
  have hmem : ∀ (addr : word) (n : Nat), memory_read [] addr n = none := fun _ _ => rfl
  simp [image_phdrs_readable, hmem]

/-- The header check bites on its count half: an image that claims no
program header is rejected however its segments look. -/
theorem image_phdrs_readable_zero_num (segs : List Segment) (ph : PhdrInfo)
    (hnum : ph.ph_num = 0) : image_phdrs_readable segs ph = false := by
  simp [image_phdrs_readable, hnum]

/-- The top of the page-rounded reservations is never negative: the empty
list gives zero, and each entry takes a maximum with the rest. -/
theorem reserved_top_nonneg : ∀ maps : List (word × word), 0 ≤ reserved_top maps :=
  List.rec (by decide) (fun _ _ ih => Int.le_trans ih (Int.le_max_right _ _))

/-- The witness sits in the window: at or above `reserved_top`, less than
a page above it, and page-aligned. -/
theorem image_brk_witness_bounds (segs : List Segment) :
    (reserved_top (segments_reserved segs) ≤ image_brk_witness segs ∧
      image_brk_witness segs < reserved_top (segments_reserved segs) + page_size) ∧
    image_brk_witness segs % page_size = 0 := by
  simp only [image_brk_witness, page_size]
  omega

/-- What the checkers buy with the boolean: a `true` verdict yields a
valid break. That is the image-only half; a valid `Run.ExecEntry` also
needs the input, which `image_brk_satisfiable_entry` adds. -/
theorem image_brk_satisfiable_sound (segs : List Segment)
    (h : image_brk_satisfiable segs = true) : ∃ brk, valid_brk segs brk := by
  have hsmall : image_brk_witness segs < 2 ^ 64 := of_decide_eq_true h
  have htop := reserved_top_nonneg (segments_reserved segs)
  have hnonneg : 0 ≤ image_brk_witness segs := by
    simp only [image_brk_witness, page_size]
    omega
  have hround := bv_unsigned_Z_to_bv_small _ hnonneg hsmall
  refine ⟨Z_to_bv 64 (image_brk_witness segs), ?_⟩
  simp only [valid_brk, hround]
  simp only [image_brk_witness, page_size, brk_aslr_max]
  omega

/-- The entry premises are satisfiable for a given valid input: the
witness stack pointer is the bottom of the sp window, which leaves room
below `State.sp_window_hi` for a block the argv and envp limits cap at
`Run.entry_stack_span_max`. -/
theorem image_brk_satisfiable_entry (img : Image) (inp : ProcInput)
    (hv : valid_input inp) (h : image_brk_satisfiable img.img_segments = true) :
    ∃ en, valid_entry img en inp := by
  have hsize := valid_input_va_size inp hv
  have hspan := entry_stack_span_bound _ _ (valid_input_argv inp hv) (valid_input_envp inp hv)
  obtain ⟨brk, hbrk⟩ := image_brk_satisfiable_sound img.img_segments h
  refine ⟨ExecEntry.mkEntry (Z_to_bv 64 sp_window_lo) brk (Z_to_bv 64 mmap_base_max)
    (LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw.mkDraw
      (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)), ?_⟩
  rw [valid_entry_sv48 _ _ _ hsize]
  have hsp : valid_sp (Z_to_bv 64 sp_window_lo) := by
    simp only [valid_sp]
    decide
  have hmmap : valid_mmap_base (Z_to_bv 64 mmap_base_max) := by
    simp only [valid_mmap_base]
    decide
  have hroom : bv_unsigned (Z_to_bv 64 sp_window_lo) + entry_stack_span_max ≤ sp_window_hi := by
    decide
  have hfits : entry_stack_fits (Z_to_bv 64 sp_window_lo) inp.in_argv inp.in_envp := by
    simp only [entry_stack_fits]
    omega
  exact ⟨hsp, hbrk, hmmap, hfits⟩

/-- The break check bites: an image whose reservations reach the top of
the address space fails it. -/
theorem image_brk_satisfiable_bites (segs : List Segment)
    (htop : 2 ^ 64 ≤ reserved_top (segments_reserved segs)) :
    image_brk_satisfiable segs = false := by
  have hwin := (image_brk_witness_bounds segs).1.1
  simp only [image_brk_satisfiable, decide_eq_false_iff_not, Int.not_lt]
  omega

/-- The three obligations of the reference `IMAGE_WF` module type. -/
structure IMAGE_WF (img : Image) : Prop where
  entry_fetchable : image_entry_fetchable img.img_segments img.img_init_pc = true
  phdrs_readable : image_phdrs_readable img.img_segments img.img_phdrs = true
  brk_satisfiable : image_brk_satisfiable img.img_segments = true

/-- The obligation of the reference `SPEC` module type, using explicit images. -/
structure SPEC (source target : Image) : Prop where
  strong_universal : strong_universal_T source target

theorem all_source_traces_error_equiv_any (source target : behavior)
    (h : source.bh_all_errors) : equiv source target := Or.inl h

theorem source_not_all_errors_target_never_errors (source target : behavior)
    (he : equiv source target) (hn : ¬ source.bh_all_errors) : ¬ target.bh_errors := by
  rcases he with ha | ⟨_, he⟩
  · exact False.elim (hn ha)
  · exact he

/-- Coverage remains a conclusion; an unsupported source cannot establish
the contract even if the all-error escape could establish bare equivalence. -/
theorem unmodeled_source_refutes_strong_equiv (source target : Image)
    (es et : ExecEntry) (inp : ProcInput)
    (h : (run source source_alloc_limit es inp).bh_unmodeled) :
    ¬ strong_equiv source target es et inp := fun hstrong => hstrong.1 h

def terminating_behavior (code : word) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) : behavior :=
  { bh_traces := fun tr => is_prefix tr [ExitEv code fs]
    bh_errors := False
    bh_all_errors := False
    bh_unmodeled := False }

def silent_behavior : behavior :=
  { bh_traces := fun tr => tr = []
    bh_errors := False
    bh_all_errors := False
    bh_unmodeled := False }

theorem same_exit_equiv (code : word) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) :
    equiv (terminating_behavior code fs) (terminating_behavior code fs) :=
  Or.inr ⟨fun _ => Iff.rfl, fun h => h⟩

theorem different_exit_code (code code' : word)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (hne : code ≠ code') :
    ¬ equiv (terminating_behavior code fs) (terminating_behavior code' fs) := by
  rintro (h | ⟨he, _⟩)
  · exact h
  · have hp := (he [ExitEv code fs]).1 (is_prefix_refl _)
    have hh : ExitEv code fs = ExitEv code' fs := hp.1
    cases hh
    exact hne rfl

theorem exit_vs_divergence (code : word) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) :
    ¬ equiv (terminating_behavior code fs) silent_behavior := by
  rintro (h | ⟨he, _⟩)
  · exact h
  · have h := (he [ExitEv code fs]).1 (is_prefix_refl _)
    cases h

end LinuxProcessSemantics.EquivalenceDefinition.Equivalence
