import LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_source
import LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_target
import LinuxProcessSemantics.Common.ShapeAlg

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/arena_tee_ns/Proof.v` at the baseline above:
`omni_strong_universal` and `strong_universal` keep their names and
statements. Both binaries realize the one outcome set
`arena_tee_ns_defs.arena_outcomes`, so `Common.ShapeAlg.shape_omni_strong_equiv`
closes the omni theorem in a single application. The legacy theorem follows
through `strong_universal_iff`.

Which dispatcher arms the theorem rests on: the proof meets the syscall
table through `Common/StreamSim.lean`'s `syscall_spec_read`,
`Common/CatSim.lean`'s `syscall_spec_write`, `Common/ExitSim.lean`'s
`syscall_spec_exit` and `Common/MmapSim.lean`'s `syscall_spec_mmap`. The
exit lemma accepts 93 or 94; these binaries use 93. The lookups here are
read (63), write (64), exit (93) and mmap (222).
Those are the numbers `testing/syscall-check/traces/examples.json` records
for this example's two binaries.
-/

namespace LinuxProcessSemantics.Examples.arena_tee_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.arena_tee_ns.SourceMemImage
open LinuxProcessSemantics.Examples.arena_tee_ns.TargetMemImage
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_code
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_defs
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_source
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_target

theorem omni_strong_universal : omni_strong_universal_T Source.image Target.image := by
  intro es et inp hs ht hi
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  -- The input declares Sv48, so use the literal Sv48 entry bounds.
  have hsv48 := valid_input_va_size inp hi
  have hs' := (valid_entry_sv48 _ _ _ hsv48).1 hs
  have ht' := (valid_entry_sv48 _ _ _ hsv48).1 ht
  apply shape_omni_strong_equiv
    source_segs SourceMemImage_init_pc SourceMemImage_phdrs
    sp_source brk_source mb_source rnd_source
    target_segs TargetMemImage_init_pc TargetMemImage_phdrs
    sp_target brk_target mb_target rnd_target
    (arena_outcomes inp.in_fs inp.in_stdin) inp
  · exact source_realizes inp hi.1 hi.2.1 sp_source rnd_source hs'.1.1 hs'.1.2.1
      brk_source mb_source
  · exact target_realizes inp sp_target rnd_target ht'.1.1 ht'.1.2.1
      brk_target mb_target

theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

/-- The ascriptions the generated Rocq `Checker.v` makes (`Module Checked <:
Equivalence.SPEC`), as `rwx_flag_ns/Proof.lean` states them. -/
theorem specification : SPEC Source.image Target.image := ⟨strong_universal⟩
theorem omni_specification : OMNI_SPEC Source.image Target.image := ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.arena_tee_ns.Proof
