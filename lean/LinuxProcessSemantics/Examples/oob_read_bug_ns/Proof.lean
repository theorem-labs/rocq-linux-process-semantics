import LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_source
import LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target
import LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target_outcomes

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/oob_read_bug_ns/Proof.v` at the baseline above:
`omni_strong_universal` and `strong_universal` keep their names and their
statements.  The first splits on `argc` and on the length cap, as the Rocq
proof does: `argc < 2` and `n > 65536` are deterministic exits glued with
`Common.CatSim.cat_omni_strong_equiv_te`, and `n ≤ 65536` is the shared
`brk` outcome set `{([], 4)} ∪ {(outbufs s, 0)}` glued with
`Common.AllocSim.alloc_omni_strong_equiv`.  The second is derived from the
first through `strong_universal_iff`.

Which dispatcher arms the theorem rests on: the proof meets the syscall
table only through `Common/AllocSim.lean`'s `syscall_spec_brk`,
`Common/CatSim.lean`'s `syscall_spec_write` and `Common/ExitSim.lean`'s
`syscall_spec_exit`, which look up brk (214), write (64) and exit (93; the
arm admits exit_group 94 too).  brk, write and exit are the numbers
`testing/syscall-check/traces/examples.json` records for this example's two
binaries.
-/

namespace LinuxProcessSemantics.Examples.oob_read_bug_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.oob_read_bug_ns.SourceMemImage
open LinuxProcessSemantics.Examples.oob_read_bug_ns.TargetMemImage
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_code
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_defs
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_source
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_target_outcomes

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
  obtain ⟨⟨hr_lo, hr_hi, _⟩, ⟨hbr_lo, hbr_hi, hbr_mod⟩, _, _⟩ := hs'
  obtain ⟨⟨ha_lo, ha_hi, _⟩, ⟨hba_lo, hba_hi, hba_mod⟩, _, _⟩ := ht'
  obtain ⟨hva, hve, _⟩ := hi
  show omni_strong_equiv (Image.mkImage source_segs SourceMemImage_init_pc source_phdrs)
    (Image.mkImage target_segs TargetMemImage_init_pc target_phdrs) _ _ inp
  rw [source_init_pc_val, target_init_pc_val]
  by_cases hge2 : 2 ≤ inp.in_argv.length
  · by_cases hcap : (nn inp.in_argv : Int) ≤ 65536
    · -- n ≤ 65536 : the shared brk outcome set
      exact alloc_omni_strong_equiv
        source_segs 0x111c8 source_phdrs sp_source brk_source mb_source rnd_source
        target_segs 0x100115c target_phdrs sp_target brk_target mb_target rnd_target
        (oobU (nN inp.in_argv) (outbufs (arg1 inp.in_argv))) inp
        (source_outcomes inp sp_source rnd_source brk_source mb_source hva hve hr_lo hr_hi
          hbr_lo hbr_hi hge2 hbr_mod hcap)
        (target_outcomes inp sp_target rnd_target brk_target mb_target hva hve ha_lo ha_hi
          hba_lo hba_hi hge2 hba_mod hcap)
    · -- n > 65536 : no output, exit 3
      exact cat_omni_strong_equiv_te
        source_segs 0x111c8 source_phdrs sp_source brk_source mb_source rnd_source
        target_segs 0x100115c target_phdrs sp_target brk_target mb_target rnd_target
        [] (Z_to_bv 64 3) inp
        (source_wexit_cap inp sp_source rnd_source hva hve hr_lo hr_hi hge2 (by omega))
        (target_wexit_cap inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap sp_target rnd_target
          hva hve ha_lo ha_hi hge2 (by
            change ¬ (((inp.in_argv.getD 1 []).length : Nat) : Int) ≤ 65536 at hcap
            change 65536 < (((inp.in_argv.getD 1 []).length : Nat) : Int)
            omega))
        (fun _ h => nomatch h)
  · -- argc < 2 : no output, exit 2
    exact cat_omni_strong_equiv_te
      source_segs 0x111c8 source_phdrs sp_source brk_source mb_source rnd_source
      target_segs 0x100115c target_phdrs sp_target brk_target mb_target rnd_target
      [] (Z_to_bv 64 2) inp
      (source_wexit_lt2 inp sp_source rnd_source hva hve hr_lo hr_hi (by omega))
      (target_wexit_lt2 inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap sp_target rnd_target
        hva hve ha_lo ha_hi (by omega))
      (fun _ h => nomatch h)

theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

/-- The ascriptions the generated Rocq `Checker.v` makes (`Module Checked <:
Equivalence.SPEC`), as `rwx_flag_ns/Proof.lean` states them. -/
theorem specification : SPEC Source.image Target.image := ⟨strong_universal⟩
theorem omni_specification : OMNI_SPEC Source.image Target.image := ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.oob_read_bug_ns.Proof
