-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:theories/Images.v
-- over rocq-linux-process-semantics f1006fe8's Lean twin.
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence

/-! # OssFuzzTheorems.Core.Images: well-formed images

The Lean twin of `theories/Images.v` of theorem-labs/oss-verify-proofs-internal
(`origin/ossv/recipes` `9b0ac6f0e6780f75e0353041e71b055f15384ff0`), over the
Lean twin of the Rocq model the released statements pin.

The three computable checks linux-process-semantics asks every consumer to make
about an image before quantifying over its valid entries
(`image_entry_fetchable`, `image_phdrs_readable`, `image_brk_satisfiable`; the
model states them as the structure `Equivalence.IMAGE_WF`). Without them, an
image malformed enough to have no valid entry, or to fault on its first
instruction, would satisfy every "on every run" statement for no reason.

One difference from the Rocq file, and it is not in what is claimed. Rocq's
`image_wf` is a conjunction and `check_image_wf` (`theories/Images.v:61`) closes
it with `vm_compute; reflexivity` through the whole image. The Lean kernel
UTF-8 encodes a string literal at every read, so the same computation does not
finish on a real image: 10.7 GB and still growing on this one (OSSV-265 gaps
ledger row T-13). The twin's `IMAGE_WF` is the same three equations, and
`tools/gen_image.py` closes them through the byte certificates of
`LinuxProcessSemantics.Common.ImageBytes` instead. `image_wf_iff_IMAGE_WF`
below is the bridge, by `Iff.rfl`. -/

namespace OssFuzzTheorems.Core.Images

open LinuxProcessSemantics.LinuxProcessSem.MemImageType (Segment Image PhdrInfo)
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
  (IMAGE_WF image_entry_fetchable image_phdrs_readable image_brk_satisfiable)

/-- The image's entry point holds a fetchable instruction, its program-header
table lies inside one readable loaded segment, and there is room above its
segments for a program break (`theories/Images.v:21-27`). -/
def image_wf (i : Image) : Prop :=
  image_entry_fetchable i.img_segments i.img_init_pc = true
  ∧ image_phdrs_readable i.img_segments i.img_phdrs = true
  ∧ image_brk_satisfiable i.img_segments = true

/-- The same three checks as one boolean (`theories/Images.v:30-35`). -/
def image_wf_b (i : Image) : Bool :=
  image_entry_fetchable i.img_segments i.img_init_pc
  && image_phdrs_readable i.img_segments i.img_phdrs
  && image_brk_satisfiable i.img_segments

theorem image_wf_b_sound (i : Image) : image_wf_b i = true → image_wf i := by
  intro h
  simp only [image_wf_b, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem image_wf_b_complete (i : Image) : image_wf i → image_wf_b i = true := by
  intro ⟨h1, h2, h3⟩
  simp only [image_wf_b, h1, h2, h3, Bool.and_self]

/-- `image_wf` of a module snapshot is exactly the model's `IMAGE_WF`
obligations for that module (`theories/Images.v:52-57`). -/
theorem image_wf_of_memimage (segs : List Segment) (pc : Nat) (ph : PhdrInfo) :
    image_wf (Image.mkImage segs pc ph)
    ↔ (image_entry_fetchable segs pc = true
       ∧ image_phdrs_readable segs ph = true
       ∧ image_brk_satisfiable segs = true) := Iff.rfl

/-- The twin's `IMAGE_WF` structure and this predicate are the same three
equations. Rocq's `Images.v` has no such lemma because there `image_wf` is
stated over the module type directly. -/
theorem image_wf_iff_IMAGE_WF (i : Image) : image_wf i ↔ IMAGE_WF i :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

/-- The three fetch forms `image_entry_fetchable` tries all answer `none` on
the empty segment list: `find_segment` has no segment to find, and the
overlay the entry check passes is empty. `image_entry_fetchable_nil` is a
lemma of the Rocq MODEL, which `theories/Images.v:67` rewrites with; it is
declared nowhere in `theories/Images.v`, and the Lean twin of the model
carries no lemma of that name, so it is proved here. -/
theorem image_entry_fetchable_nil (pc : Nat) : image_entry_fetchable [] pc = false := by
  have hw : LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word []
      (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (pc : Int)) = none := by
    unfold LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word
    split <;> rfl
  have hwx : LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word_wx []
      (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (pc : Int)) = none := by
    unfold LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word_wx
    split <;> rfl
  have ht : LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_tail_any []
      (fun _ => none) (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 (pc : Int)) = none := by
    unfold LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_tail_any
    split
    · rfl
    · unfold LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_half_any
      rfl
  simp [image_entry_fetchable, hw, hwx, ht]

/-- The check bites: the image with no segments is not well formed, at any
entry point (`theories/Images.v:65-68`). -/
theorem image_wf_nil (pc : Nat) (ph : PhdrInfo) : ¬ image_wf (Image.mkImage [] pc ph) := by
  intro ⟨h, _, _⟩
  rw [image_entry_fetchable_nil] at h
  exact Bool.noConfusion h

end OssFuzzTheorems.Core.Images
