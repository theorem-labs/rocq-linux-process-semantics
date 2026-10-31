import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_source
import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_target

/-! rocq-baseline: 36031418350290d5d51fae6e71cbf0b73d7cc91e -/

/-! Mirrors `theories/Examples/conditional_bug_ns/Proof.v` at the baseline
above: `omni_strong_universal` and `strong_universal` keep their names and
their statements. Both binaries dispatch on the first byte of argv[1]: argc < 2,
'n' and any other byte end with no output and exit 2, 0 and 3, glued with
`Common.CatSim.cat_omni_strong_equiv_te`; 'h' writes "hello\n" and exits 0,
glued with `Common.WallSim.wall_omni_strong_equiv`; on 'o' every source
execution faults on the load from unmapped address 64, so
`Common.ErrEscape.err_escape_omni_strong_equiv` frees the target. The entry
stack pointers and draws of the two binaries are quantified independently.

Which dispatcher arms the theorem rests on: the proof meets the syscall
table only through `Common/CatSim.lean`'s `syscall_spec_write` and
`Common/ExitSim.lean`'s `syscall_spec_exit`, which look up write (64) and
exit (93/94). Those are the numbers
`testing/syscall-check/traces/examples.json` records for this example's two
binaries.
-/

namespace LinuxProcessSemantics.Examples.conditional_bug_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.ErrEscape
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.conditional_bug_ns.SourceMemImage
open LinuxProcessSemantics.Examples.conditional_bug_ns.TargetMemImage
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_code
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_source
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_target

theorem omni_strong_universal : omni_strong_universal_T Source.image Target.image := by
  intro es et inp hs ht hi
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  have hsv48 := valid_input_va_size inp hi
  have hs' := (valid_entry_sv48 _ _ _ hsv48).1 hs
  have ht' := (valid_entry_sv48 _ _ _ hsv48).1 ht
  by_cases Hge2 : 2 ≤ inp.in_argv.length
  · by_cases Ho : byte_at (inp.in_argv.getD 1 []) 0 = Z_to_bv 8 111
    · obtain ⟨ms', Hm, Hsvc, Hill⟩ := source_err_o inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap hi.1 hi.2.1 sp_source rnd_source hs'.1.1 hs'.1.2.1 Hge2 Ho
      exact err_escape_omni_strong_equiv source_segs SourceMemImage_init_pc
        SourceMemImage_phdrs sp_source brk_source mb_source rnd_source inp _ _ ms' Hm Hsvc Hill
    · by_cases Hn : byte_at (inp.in_argv.getD 1 []) 0 = Z_to_bv 8 110
      · apply cat_omni_strong_equiv_te
          source_segs SourceMemImage_init_pc SourceMemImage_phdrs
                    sp_source brk_source mb_source rnd_source
                    target_segs TargetMemImage_init_pc TargetMemImage_phdrs
                    sp_target brk_target mb_target rnd_target
          [] (Z_to_bv 64 0) inp
        · exact source_wexit_n inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
            hi.1 hi.2.1 sp_source rnd_source hs'.1.1 hs'.1.2.1 Hge2 Hn
        · exact target_wexit_n inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
            hi.1 hi.2.1 sp_target rnd_target ht'.1.1 ht'.1.2.1 Hge2 Hn
        · exact nil_bufs_modeled
      · by_cases Hh : byte_at (inp.in_argv.getD 1 []) 0 = Z_to_bv 8 104
        · apply wall_omni_strong_equiv
            source_segs SourceMemImage_init_pc SourceMemImage_phdrs
            sp_source brk_source mb_source rnd_source
            target_segs TargetMemImage_init_pc TargetMemImage_phdrs
            sp_target brk_target mb_target rnd_target
            [hello] (Z_to_bv 64 0) inp
          · exact source_wexit_h inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
              hi.1 hi.2.1 sp_source rnd_source hs'.1.1 hs'.1.2.1 Hge2 Hh
          · exact target_wexit_h inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
              hi.1 hi.2.1 sp_target rnd_target ht'.1.1 ht'.1.2.1 Hge2 Hh
          · exact hello_bufs_modeled
        · apply cat_omni_strong_equiv_te
            source_segs SourceMemImage_init_pc SourceMemImage_phdrs
            sp_source brk_source mb_source rnd_source
            target_segs TargetMemImage_init_pc TargetMemImage_phdrs
            sp_target brk_target mb_target rnd_target
            [] (Z_to_bv 64 3) inp
          · exact source_wexit_other inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
              hi.1 hi.2.1 sp_source rnd_source hs'.1.1 hs'.1.2.1 Hge2 Hn Hh Ho
          · exact target_wexit_other inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
              hi.1 hi.2.1 sp_target rnd_target ht'.1.1 ht'.1.2.1 Hge2 Hn Hh Ho
          · exact nil_bufs_modeled
  · apply cat_omni_strong_equiv_te
      source_segs SourceMemImage_init_pc SourceMemImage_phdrs
      sp_source brk_source mb_source rnd_source
      target_segs TargetMemImage_init_pc TargetMemImage_phdrs
      sp_target brk_target mb_target rnd_target
      [] (Z_to_bv 64 2) inp
    · exact source_wexit_lt2 inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
        hi.1 hi.2.1 sp_source rnd_source hs'.1.1 hs'.1.2.1 (by omega)
    · exact target_wexit_lt2 inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
        hi.1 hi.2.1 sp_target rnd_target ht'.1.1 ht'.1.2.1 (by omega)
    · exact nil_bufs_modeled

theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

/-- The ascriptions the generated Rocq `Checker.v` makes (`Module Checked <:
Equivalence.SPEC`), as `rwx_flag_ns/Proof.lean` states them. -/
theorem specification : SPEC Source.image Target.image := ⟨strong_universal⟩
theorem omni_specification : OMNI_SPEC Source.image Target.image := ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.conditional_bug_ns.Proof
