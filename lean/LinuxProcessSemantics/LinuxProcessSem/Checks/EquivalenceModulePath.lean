import LinuxProcessSemantics.EquivalenceDefinition.Equivalence

/-! # Checks.EquivalenceModulePath — the BET import contract

Not part of the trusted specification.
The BET packager lives outside this repository.
It generates a Lean file that imports `LinuxProcessSemantics.EquivalenceDefinition.Equivalence`.
That generated file names these constants by full name.
These examples stop elaborating if the module path or a full name moves. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.EquivalenceModulePath

example (s t : LinuxProcessSemantics.LinuxProcessSem.MemImageType.Image)
    (h : LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPEC s t) :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_T s t :=
  h.strong_universal

example (img : LinuxProcessSemantics.LinuxProcessSem.MemImageType.Image)
    (h : LinuxProcessSemantics.EquivalenceDefinition.Equivalence.IMAGE_WF img) :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.image_entry_fetchable
      img.img_segments img.img_init_pc = true :=
  h.entry_fetchable

end LinuxProcessSemantics.LinuxProcessSem.Checks.EquivalenceModulePath
