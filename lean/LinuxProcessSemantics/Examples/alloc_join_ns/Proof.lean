import LinuxProcessSemantics.Common.ShapeAlg
import LinuxProcessSemantics.Common.AllocSim2
import LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_source
import LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_target

/-! rocq-baseline: b89fd3aefa642f07b01c02ead422e3cebfce5549 -/

/-! # alloc-join: equivalence proof, top-level glue

PROOF-SIDE, not trusted spec. Translates `theories/Examples/alloc_join_ns/Proof.v`:
observable trace equivalence between the source image (Source, brk allocator)
and the target image (Target, mmap allocator), for all valid stack pointers and
every valid process input (one `ProcInput` record: argv, envp, file system, stdin).

With `tot = |join1(argv[1..])| + 1`, the shared observable behavior is:

* argc < 2: no output, exit 2 (deterministic).
* argc >= 2, tot > 65536: no output, exit 3 (deterministic).
* argc >= 2, tot <= 65536: the outcome set
  `{ ([], 4) } ∪ { ([join1(argv[1..]) ++ '\n'], 0) }`.
  The source reaches it through the two brk resolutions, the target through
  the two mmap resolution families; allocation emits no events, so the sets
  coincide.

The glue goes through `Common.ShapeAlg`: each branch names one shape (a
prefix-closed trace set), exhibits a `realizes` derivation for each binary at
that shape, and closes with the master shape theorem. The per-binary witnesses
are unchanged; `wall_realizes`, `outcomes_realizes`, and `tmw_realizes` carry
them into `realizes`.

In the allocation branch, the source's brk-branching `AllocSim.to_outcomes`
set and the target's `MmapSim.tmw` derivation land on the same shape:
`t_alt2 (t_writes [] (t_exit 4 fs0)) (t_writes [jout argv] (t_exit 0 fs0))`.
The rewrite `t_outcomes_two_alt2` identifies them, without an allocator-pair
specific glue lemma. Exit codes are `Z_to_bv 64 c` words; the total-size cap
split is in `Int` over `bv_unsigned (tot inp)`.
-/

namespace LinuxProcessSemantics.Examples.alloc_join_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.Common.ShapeAlg.realizes
open LinuxProcessSemantics.Examples.alloc_join_ns.SourceMemImage
open LinuxProcessSemantics.Examples.alloc_join_ns.TargetMemImage
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_code
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_defs
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_source
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_target

theorem omni_strong_universal :
    omni_strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) := by
  intro es et inp Hens Hent Hvalid
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  -- The input declares Sv48 (`valid_input` pins it), so the entry predicate
  -- is the literal Sv48 one (`valid_entry_sv48`).
  have Hsv48 := valid_input_va_size inp Hvalid
  obtain ⟨⟨Hr_lo, Hr_hi, _⟩, ⟨Hbr_lo, Hbr_hi, Hbr_mod⟩, _⟩ :=
    (valid_entry_sv48 _ _ _ Hsv48).1 Hens
  obtain ⟨⟨Ha_lo, Ha_hi, _⟩, _⟩ := (valid_entry_sv48 _ _ _ Hsv48).1 Hent
  obtain ⟨Hva, Hve, _⟩ := Hvalid
  by_cases Hge2 : 2 ≤ inp.in_argv.length
  · by_cases Hle : bv_unsigned (tot inp) ≤ 65536
    · -- The shared two-element outcome set.
      apply shape_omni_strong_equiv
        source_segs SourceMemImage_init_pc source_phdrs sp_source brk_source mb_source rnd_source
        target_segs TargetMemImage_init_pc target_phdrs sp_target brk_target mb_target rnd_target
        (t_alt2 (t_writes [] (t_exit (Z_to_bv 64 4) inp.in_fs))
          (t_writes [jout inp.in_argv] (t_exit (Z_to_bv 64 0) inp.in_fs))) inp
      · unfold init_config
        refine rz_conseq _ _ _ (outcomes_realizes source_segs _ _ _ ?_ rfl rfl)
          (t_outcomes_two_alt2 inp.in_fs [] (Z_to_bv 64 4)
            [jout inp.in_argv] (Z_to_bv 64 0))
        rw [source_init_pc_val]
        exact source_outcomes inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
          brk_source mb_source Hbr_lo Hbr_hi Hge2 Hbr_mod Hle
      · unfold init_config
        refine tmw_realizes target_segs _ _ [] (Z_to_bv 64 4)
          [jout inp.in_argv] (Z_to_bv 64 0) rfl rfl rfl ?_
          (by intro b Hb; cases Hb) (jout_modeled inp Hva Hge2 Hle)
        rw [target_init_pc_val]
        exact target_tmw inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
          brk_target mb_target Hge2 Hle
    · -- The total-size cap: no output, exit 3.
      have Hgt : 65536 < bv_unsigned (tot inp) := by omega
      apply shape_omni_strong_equiv
        source_segs SourceMemImage_init_pc source_phdrs sp_source brk_source mb_source rnd_source
        target_segs TargetMemImage_init_pc target_phdrs sp_target brk_target mb_target rnd_target
        (t_writes [] (t_exit (Z_to_bv 64 3) inp.in_fs)) inp
      · unfold init_config
        refine wall_realizes source_segs _ _ [] (Z_to_bv 64 3) rfl rfl rfl ?_
          (by intro b Hb; cases Hb)
        rw [source_init_pc_val]
        exact source_wexit_cap inp Hva Hve sp_source rnd_source Hr_lo Hr_hi Hge2 Hgt
      · unfold init_config
        refine wall_realizes target_segs _ _ [] (Z_to_bv 64 3) rfl rfl rfl ?_
          (by intro b Hb; cases Hb)
        rw [target_init_pc_val]
        exact target_wexit_cap inp Hva Hve sp_target rnd_target Ha_lo Ha_hi Hge2 Hgt
  · -- argc < 2: no output, exit 2.
    have Hlt2 : inp.in_argv.length < 2 := by omega
    apply shape_omni_strong_equiv
      source_segs SourceMemImage_init_pc source_phdrs sp_source brk_source mb_source rnd_source
      target_segs TargetMemImage_init_pc target_phdrs sp_target brk_target mb_target rnd_target
      (t_writes [] (t_exit (Z_to_bv 64 2) inp.in_fs)) inp
    · unfold init_config
      refine wall_realizes source_segs _ _ [] (Z_to_bv 64 2) rfl rfl rfl ?_
        (by intro b Hb; cases Hb)
      rw [source_init_pc_val]
      exact source_wexit_lt2 inp Hva Hve sp_source rnd_source Hr_lo Hr_hi Hlt2
    · unfold init_config
      refine wall_realizes target_segs _ _ [] (Z_to_bv 64 2) rfl rfl rfl ?_
        (by intro b Hb; cases Hb)
      rw [target_init_pc_val]
      exact target_wexit_lt2 inp Hva Hve sp_target rnd_target Ha_lo Ha_hi Hlt2

/-- The legacy statement, through the compat `iff`; this is the theorem the
checker pins to `Equivalence.SPEC`. -/
theorem strong_universal :
    strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) :=
  (strong_universal_iff _ _).2 omni_strong_universal

end LinuxProcessSemantics.Examples.alloc_join_ns.Proof
