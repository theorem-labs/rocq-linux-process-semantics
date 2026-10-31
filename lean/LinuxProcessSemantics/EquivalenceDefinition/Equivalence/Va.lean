-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/Equivalence.v
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Base

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # The declared address-space size: one statement per size, and the one that pins none

Mirrors the `SpecVa` section of `theories/EquivalenceDefinition/Equivalence.v`.
`strong_universal_T` quantifies over `Run.valid_input`, which pins
`State.in_va_size` to `Sv48`. The statements here are the same obligation
under the other two declarations and under none; the quantifier and one
conjunct are the whole difference. `valid_entry` reads the size off the
input, so an Sv39 statement ranges over entries inside the Sv39 window.

The conjunct is there because the spec arms compare against the Sv48
`State.TASK_SIZE`, so `Run.run` is the Sv48 run whatever the input declares.
`strong_equiv_va` requires the declaration to be `Sv48` first, which makes
`strong_universal_T_sv39` and `strong_universal_T_sv57` false whenever the
entry predicates are inhabited (`strong_universal_T_sv39_refuted`,
`strong_universal_T_sv57_refuted`). A task on such a kernel is refused by
name rather than graded against the Sv48 window, until the arms read the
declared size
(linux-process-semantics@ff0313ba4f:bugs/va-size-declines-every-non-sv48-run.md;
scope: SCOPE.md#where-the-model-is-narrower, the "Address-space size"
row). This does not gate `Run.run` itself: an obligation written over it
directly is a statement about the Sv48 run, the residual that
linux-process-semantics@ff0313ba4f:bugs/va-size-declines-every-non-sv48-run.md
records.
-/

namespace LinuxProcessSemantics.EquivalenceDefinition.Equivalence

open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

/-- The entry predicates are inhabited under every declaration, by the
witness Rocq's `image_brk_satisfiable_entry` uses, moved to the declared
size's window. Stated over `valid_input_va_any` and the size read off the
input, so that one lemma serves the three pinned predicates. -/
theorem image_brk_satisfiable_entry_va (img : Image) (inp : ProcInput)
    (hv : valid_input_va_any inp) (h : image_brk_satisfiable img.img_segments = true) :
    ∃ en, valid_entry img en inp := by
  obtain ⟨hargv, henvp, -⟩ := hv
  have hspan := entry_stack_span_bound _ _ hargv henvp
  have hbounds :
      reserved_top (segments_reserved img.img_segments) ≤ image_brk_witness img.img_segments ∧
      image_brk_witness img.img_segments <
        reserved_top (segments_reserved img.img_segments) + page_size := by
    simp only [image_brk_witness, page_size]
    omega
  have hnonneg : 0 ≤ image_brk_witness img.img_segments := by
    have := reserved_top_nonneg (segments_reserved img.img_segments)
    omega
  have hsmall : image_brk_witness img.img_segments < 2 ^ 64 := by
    exact of_decide_eq_true h
  have hround := LinuxProcessSemantics.LinuxProcessSem.BvBase.bv_unsigned_Z_to_bv_small
    _ hnonneg hsmall
  have hbrk : valid_brk img.img_segments
      (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (image_brk_witness img.img_segments)) := by
    simp only [valid_brk, hround]
    simp only [image_brk_witness, page_size, brk_aslr_max] at hbounds ⊢
    omega
  have hgeometry : ∀ v,
      valid_sp_va v (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (va_sp_window_lo v)) ∧
      valid_mmap_base_va v (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (va_mmap_base_max v)) ∧
      LinuxProcessSemantics.Riscv.Prelude.bv_unsigned
        (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (va_sp_window_lo v)) + entry_stack_span_max ≤ va_sp_window_hi v := by
    exact fun v => by
      rcases v with _ | _ | _ <;>
        simp only [valid_sp_va, valid_mmap_base_va] <;> decide
  obtain ⟨hsp, hmmap, hroom⟩ := hgeometry inp.in_va_size
  have hfits : entry_stack_fits_va inp.in_va_size
      (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (va_sp_window_lo inp.in_va_size)) inp.in_argv inp.in_envp := by
    simp only [entry_stack_fits_va]
    omega
  exact ⟨ExecEntry.mkEntry
    (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (va_sp_window_lo inp.in_va_size))
    (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (image_brk_witness img.img_segments))
    (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (va_mmap_base_max inp.in_va_size))
    (LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw.mkDraw
      (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 128 0) (fun _ => LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 8 0)),
    hsp, hbrk, hmmap, hfits⟩

/-- `strong_equiv` behind the declaration the arms implement. Under
`Run.valid_input` the first conjunct is the pinned field and the predicate is
`strong_equiv` (`strong_equiv_va_sv48`); under any other declaration it is
false, which is the refusal. -/
def strong_equiv_va (source_image target_image : Image) (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  inp.in_va_size = .Sv48 ∧ strong_equiv source_image target_image en_source en_target inp

theorem strong_equiv_va_sv48 (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) (hv : inp.in_va_size = .Sv48) :
    strong_equiv_va source_image target_image en_source en_target inp ↔
      strong_equiv source_image target_image en_source en_target inp :=
  ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩

def strong_universal_T_sv39 (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_sv39 inp → strong_equiv_va source_image target_image en_source en_target inp

def strong_universal_T_sv57 (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_sv57 inp → strong_equiv_va source_image target_image en_source en_target inp

/-- No size pinned: the obligation over every input the shared clauses
accept. It is the conjunction of the three pinned statements
(`strong_universal_T_va_any_splits`), so a task that says nothing about its
kernel is held to all three readings. -/
def strong_universal_T_va_any (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_va_any inp → strong_equiv_va source_image target_image en_source en_target inp

theorem strong_universal_T_va_any_splits (source_image target_image : Image) :
    strong_universal_T_va_any source_image target_image ↔
      (strong_universal_T source_image target_image ∧
        strong_universal_T_sv39 source_image target_image ∧
        strong_universal_T_sv57 source_image target_image) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro es et inp hs ht hv
      exact (strong_equiv_va_sv48 _ _ _ _ _ (valid_input_va_size inp hv)).1
        (h es et inp hs ht (valid_input_va_any_of_valid_input inp hv))
    · intro es et inp hs ht hv
      exact h es et inp hs ht (valid_input_va_any_of_valid_input_sv39 inp hv)
    · intro es et inp hs ht hv
      exact h es et inp hs ht (valid_input_va_any_of_valid_input_sv57 inp hv)
  · rintro ⟨h48, h39, h57⟩ es et inp hs ht hv
    rcases valid_input_va_any_splits inp hv with hv' | hv' | hv'
    · exact (strong_equiv_va_sv48 _ _ _ _ _ (valid_input_va_size inp hv')).2
        (h48 es et inp hs ht hv')
    · exact h39 es et inp hs ht hv'
    · exact h57 es et inp hs ht hv'

/-- One Sv39 triple the predicates accept refutes the Sv39 statement, because
the declaration is not the one the arms implement. The Cases twin of this
file fires it on a concrete image. -/
theorem strong_universal_T_sv39_refuted (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hv : valid_input_sv39 inp) : ¬ strong_universal_T_sv39 source_image target_image := by
  intro h
  have h48 := (h en_source en_target inp hs ht hv).1
  rw [valid_input_sv39_va_size inp hv] at h48
  cases h48

theorem strong_universal_T_sv57_refuted (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hv : valid_input_sv57 inp) : ¬ strong_universal_T_sv57 source_image target_image := by
  intro h
  have h48 := (h en_source en_target inp hs ht hv).1
  rw [valid_input_sv57_va_size inp hv] at h48
  cases h48

/-- The sealing surface for a task declared on an Sv39 kernel, beside
`SPEC`. Which surface a checker ascribes is the task's declaration: a
proof made under `Run.valid_input` does not fit this one. -/
structure SPEC_SV39 (source target : Image) : Prop where
  strong_universal : strong_universal_T_sv39 source target

/-- The same for a task declared on an Sv57 kernel. -/
structure SPEC_SV57 (source target : Image) : Prop where
  strong_universal : strong_universal_T_sv57 source target

/-- The surface for a task that declares no size and is held to all three
readings. -/
structure SPEC_VA_ANY (source target : Image) : Prop where
  strong_universal : strong_universal_T_va_any source target

end LinuxProcessSemantics.EquivalenceDefinition.Equivalence
