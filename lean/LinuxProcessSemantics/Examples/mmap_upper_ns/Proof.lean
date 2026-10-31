import LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_source
import LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_target
import LinuxProcessSemantics.Common.ShapeAlg

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/mmap_upper_ns/Proof.v` at the baseline above:
`no_writes_modeled`, `out_buf_modeled`, `omni_strong_universal` and
`strong_universal` keep their names and statements. The omni theorem glues
the two per-binary derivations with `Common.ShapeAlg.shape_omni_strong_equiv`:
too few arguments realize the exit-2 shape, an argument longer than 4095
bytes realizes the exit-3 shape, and the remaining inputs realize the same
`t_alt2` of mmap failure and success. `wall_realizes` and `tmw_realizes`
bridge the per-binary witnesses to those shapes. The legacy theorem follows
through `strong_universal_iff`.

Which dispatcher arms the theorem rests on: the proof meets the syscall
table through `Common/CatSim.lean`'s `syscall_spec_write`,
`Common/ExitSim.lean`'s `syscall_spec_exit`, and `Common/MmapSim.lean`'s
`syscall_spec_munmap` and `syscall_spec_mmap`. The exit lemma accepts 93 or
94; these binaries use 93. The lookups here are write (64), exit (93),
munmap (215), and mmap (222).
Those are the numbers `testing/syscall-check/traces/examples.json` records
for this example's two binaries.
-/

namespace LinuxProcessSemantics.Examples.mmap_upper_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.mmap_upper_ns.SourceMemImage
open LinuxProcessSemantics.Examples.mmap_upper_ns.TargetMemImage
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_code
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_defs
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_source
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_target

/-- The failure summand and both short-exit branches write nothing. -/
theorem no_writes_modeled : bufs_modeled [] := by
  intro b hb
  exact False.elim (List.not_mem_nil hb)

/-- The success branch's one buffer has at most 4096 bytes. -/
theorem out_buf_modeled (s : List byte) (hs : s.length ≤ 4095) :
    bufs_modeled [out_buf s] := by
  apply bufs_modeled_single
  unfold buf_modeled
  rw [length_out_buf]
  unfold LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.rw_bytes_max
  omega

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
  by_cases h2 : 2 ≤ inp.in_argv.length
  · by_cases hn : (inp.in_argv.getD 1 []).length ≤ 4095
    · apply shape_omni_strong_equiv
        source_segs SourceMemImage_init_pc SourceMemImage_phdrs
        sp_source brk_source mb_source rnd_source
        target_segs TargetMemImage_init_pc TargetMemImage_phdrs
        sp_target brk_target mb_target rnd_target
        (t_alt2 (t_writes [] (t_exit (Z_to_bv 64 4) inp.in_fs))
          (t_writes [out_buf (inp.in_argv.getD 1 [])] (t_exit (Z_to_bv 64 0) inp.in_fs))) inp
      · unfold init_config
        refine tmw_realizes _ _ _ _ _ _ _ rfl rfl rfl ?_
          no_writes_modeled (out_buf_modeled _ hn)
        rw [source_init_pc_val]
        exact source_tmw inp sp_source rnd_source hi.1 hi.2.1 hs'.1.1 hs'.1.2.1
          brk_source mb_source h2 hn
      · unfold init_config
        refine tmw_realizes _ _ _ _ _ _ _ rfl rfl rfl ?_
          no_writes_modeled (out_buf_modeled _ hn)
        rw [target_init_pc_val]
        exact target_tmw inp sp_target rnd_target hi.1 hi.2.1 ht'.1.1 ht'.1.2.1
          brk_target mb_target h2 hn
    · have hgt : 4095 < (inp.in_argv.getD 1 []).length := by omega
      apply shape_omni_strong_equiv
        source_segs SourceMemImage_init_pc SourceMemImage_phdrs
        sp_source brk_source mb_source rnd_source
        target_segs TargetMemImage_init_pc TargetMemImage_phdrs
        sp_target brk_target mb_target rnd_target
        (t_writes [] (t_exit (Z_to_bv 64 3) inp.in_fs)) inp
      · unfold init_config
        refine wall_realizes _ _ _ _ _ rfl rfl rfl ?_ no_writes_modeled
        rw [source_init_pc_val]
        exact source_wexit_len3 inp sp_source rnd_source hi.1 hi.2.1
          hs'.1.1 hs'.1.2.1 h2 hgt
      · unfold init_config
        refine wall_realizes _ _ _ _ _ rfl rfl rfl ?_ no_writes_modeled
        rw [target_init_pc_val]
        exact target_wexit_len3 inp sp_target rnd_target hi.1 hi.2.1
          ht'.1.1 ht'.1.2.1 h2 hgt
  · have hlt : inp.in_argv.length < 2 := by omega
    apply shape_omni_strong_equiv
      source_segs SourceMemImage_init_pc SourceMemImage_phdrs
      sp_source brk_source mb_source rnd_source
      target_segs TargetMemImage_init_pc TargetMemImage_phdrs
      sp_target brk_target mb_target rnd_target
      (t_writes [] (t_exit (Z_to_bv 64 2) inp.in_fs)) inp
    · unfold init_config
      refine wall_realizes _ _ _ _ _ rfl rfl rfl ?_ no_writes_modeled
      rw [source_init_pc_val]
      exact source_wexit_lt2 inp sp_source rnd_source hi.1 hi.2.1 hs'.1.1 hs'.1.2.1 hlt
    · unfold init_config
      refine wall_realizes _ _ _ _ _ rfl rfl rfl ?_ no_writes_modeled
      rw [target_init_pc_val]
      exact target_wexit_lt2 inp sp_target rnd_target hi.1 hi.2.1 ht'.1.1 ht'.1.2.1 hlt

theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

/-- The ascriptions the generated Rocq `Checker.v` makes (`Module Checked <:
Equivalence.SPEC`), as `rwx_flag_ns/Proof.lean` states them. -/
theorem specification : SPEC Source.image Target.image := ⟨strong_universal⟩
theorem omni_specification : OMNI_SPEC Source.image Target.image := ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.mmap_upper_ns.Proof
