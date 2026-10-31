import LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_source
import LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_target

/-! rocq-baseline: 8bef2933e7063c3b77d628343969f2352008c3ca -/

/-! Mirrors `theories/Examples/cat1024_ns/Proof.v` at the baseline above:
`omni_strong_universal` and `strong_universal` keep their names and their
statements, the first glues the two per-binary derivations with
`Common.StreamSim.stream_omni_strong_equiv` at `cnt = Z_to_bv 64 1024`, and
the second is derived from the first through `strong_universal_iff`.

Which dispatcher arms the theorem rests on: the proof meets the syscall
table only through `Common/StreamSim.lean`'s `syscall_spec_read`,
`Common/CatSim.lean`'s `syscall_spec_write` and `Common/ExitSim.lean`'s
`syscall_spec_exit`, which look up read (63), write (64) and exit (93/94).
Those are the numbers `testing/syscall-check/traces/examples.json` records
for this example's two binaries.
-/

namespace LinuxProcessSemantics.Examples.cat1024_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.cat1024_ns.SourceMemImage
open LinuxProcessSemantics.Examples.cat1024_ns.TargetMemImage
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_code
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_source
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_target

theorem omni_strong_universal : omni_strong_universal_T Source.image Target.image := by
  intro es et inp hs ht hi
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  -- the input declares Sv48 (`Run.valid_input` pins it), so the entry
  -- predicate is the literal Sv48 one (`Run.valid_entry_sv48`)
  have hsv48 := valid_input_va_size inp hi
  have hs' := (valid_entry_sv48 _ _ _ hsv48).1 hs
  have ht' := (valid_entry_sv48 _ _ _ hsv48).1 ht
  exact stream_omni_strong_equiv (Z_to_bv 64 1024) cat_Hcnt
    source_segs
    (src_LH inp.in_argv inp.in_envp sp_source rnd_source inp.in_uid inp.in_hwcap)
    SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
    target_segs tgt_LH
    TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
    inp
    (src_LH_to_rd inp.in_argv inp.in_envp sp_source rnd_source
      hs'.1.1 hs'.1.2.1 inp.in_uid inp.in_hwcap)
    (fun ms h => tgt_LH_to_rd ms h)
    (src_init_to_rd inp.in_argv inp.in_envp hi.1 hi.2.1 sp_source rnd_source
      hs'.1.1 hs'.1.2.1 inp.in_uid inp.in_hwcap)
    (tgt_init_to_rd inp.in_argv inp.in_envp sp_target rnd_target ht'.1.1 ht'.1.2.1
      inp.in_uid inp.in_hwcap)

theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

/-- The ascriptions the generated Rocq `Checker.v` makes (`Module Checked <:
Equivalence.SPEC`), as `rwx_flag_ns/Proof.lean` states them. -/
theorem specification : SPEC Source.image Target.image := ⟨strong_universal⟩
theorem omni_specification : OMNI_SPEC Source.image Target.image := ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.cat1024_ns.Proof
