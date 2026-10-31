import LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_source
import LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_target
import LinuxProcessSemantics.Common.ShapeAlg
import LinuxProcessSemantics.Common.AllocSim2
import LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
/-! rocq-baseline: 3bd94f932fe0933df59ec88e6cc87819fee0d9d1 -/

/-! # Equivalence proof for brk-rev: top-level glue

PROOF-SIDE FILE (not part of the trusted specification). Discharges
`strong_universal`: observable trace equivalence between the source image
(`Source.image`) and the target image (`Target.image`) for valid stack
pointers and valid process inputs (one `ProcInput` record: argv, envp,
file system, stdin).

With `s = argv[1]`, `n = s.length`, the shared observable behavior is:

* argc < 2: no output, exit 2 (deterministic).
* argc >= 2, n > 65536: no output, exit 3 (deterministic).
* argc >= 2, n <= 65536: the outcome set
  `{ ([], 4) } ∪ { ([s.reverse ++ '\n'], 0) }`.
  The brk resolutions yield either silent failure with exit 4 or success
  writing the reversed string plus newline and exiting 0.

The glue goes through `Common.ShapeAlg`: each branch names one shape
(a prefix-closed trace set), exhibits a `realizes` derivation for the source
and target at that same shape, and closes with `shape_omni_strong_equiv`.
The per-binary witnesses are unchanged; the library bridges `wall_realizes`
and `outcomes_realizes` carry them into `realizes`.

Both binaries allocate with brk, so the interesting branch consists of two
`AllocSim.to_outcomes` derivations over the same outcome set
`brkU (rev_buf argv[1])`. The theorem `t_outcomes_two_alt2` identifies that
set's trace denotation with
`t_alt2 (t_writes [] (t_exit 4 fs0))
        (t_writes [rev_buf argv[1]] (t_exit 0 fs0))`.
This is the same shape an mmap-allocating target would need to realize;
no allocator-pair-specific glue lemma is involved. Exit codes are
`Z_to_bv 64 c` words, and the string-length cap split is in `Int` over
`((argv.getD 1 []).length : Int)`.

Which dispatcher arms the theorem rests on: the recorded runs issue brk
(214), write (64), and exit (93). The `brk_rev_ns` entry's `arms` in
`testing/syscall-check/traces/examples.json` is exactly
`["brk", "exit", "write"]`. Re-snapshotting a binary makes that recording
stale: `testing/syscall-check/trace_corpus.py` checks the snapshot digest
against the capture before verifying the recorded arm set.
-/

namespace LinuxProcessSemantics.Examples.brk_rev_ns.Proof

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
open LinuxProcessSemantics.Examples.brk_rev_ns.SourceMemImage
open LinuxProcessSemantics.Examples.brk_rev_ns.TargetMemImage
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_code
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_defs
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_source
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_target

theorem omni_strong_universal :
    omni_strong_universal_T
      Source.image Target.image := by
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
  obtain ⟨⟨Ha_lo, Ha_hi, _⟩, ⟨Hba_lo, Hba_hi, Hba_mod⟩, _⟩ :=
    (valid_entry_sv48 _ _ _ Hsv48).1 Hent
  obtain ⟨Hva, Hve, _⟩ := Hvalid
  by_cases Hge2 : 2 ≤ inp.in_argv.length
  · by_cases Hle : ((inp.in_argv.getD 1 []).length : Int) ≤ 65536
    · -- The shared two-element outcome set.
      apply shape_omni_strong_equiv
        source_segs SourceMemImage_init_pc source_phdrs sp_source brk_source mb_source rnd_source
        target_segs TargetMemImage_init_pc target_phdrs sp_target brk_target mb_target rnd_target
        (t_alt2 (t_writes [] (t_exit (Z_to_bv 64 4) inp.in_fs))
          (t_writes [rev_buf (inp.in_argv.getD 1 [])] (t_exit (Z_to_bv 64 0) inp.in_fs))) inp
      · unfold init_config
        refine rz_conseq _ _ _ (outcomes_realizes source_segs _ _ _ ?_ rfl rfl)
          (t_outcomes_two_alt2 inp.in_fs [] (Z_to_bv 64 4)
            [rev_buf (inp.in_argv.getD 1 [])] (Z_to_bv 64 0))
        rw [source_init_pc_val]
        exact source_outcomes inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
          brk_source mb_source Hbr_lo Hbr_hi Hge2 Hbr_mod Hle
      · unfold init_config
        refine rz_conseq _ _ _ (outcomes_realizes target_segs _ _ _ ?_ rfl rfl)
          (t_outcomes_two_alt2 inp.in_fs [] (Z_to_bv 64 4)
            [rev_buf (inp.in_argv.getD 1 [])] (Z_to_bv 64 0))
        rw [target_init_pc_val]
        exact target_outcomes inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
          brk_target mb_target Hba_lo Hba_hi Hge2 Hba_mod Hle
    · -- The string-length cap: no output, exit 3.
      have Hgt : 65536 < ((inp.in_argv.getD 1 []).length : Int) := by omega
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
      Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).mpr omni_strong_universal

end LinuxProcessSemantics.Examples.brk_rev_ns.Proof
