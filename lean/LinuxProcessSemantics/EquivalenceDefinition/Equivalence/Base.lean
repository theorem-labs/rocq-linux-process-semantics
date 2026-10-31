import LinuxProcessSemantics.LinuxProcessSem.Run

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
