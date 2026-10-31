import LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_source
import LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_target
/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Equivalence proof for tail1-ns — top-level glue.

PROOF-SIDE FILE (not part of the trusted specification). Discharges
`strong_universal`: observable trace equivalence between the source image
(`Source`) and the target image (`Target`) for all valid stack pointers and
every valid process input (one `ProcInput` record: argv, envp, file system,
stdin).

Both binaries implement tail-1: read all of stdin to EOF in 1024-byte chunks,
tracking the current unterminated line `cur` and the last completed line
`done`; at EOF write the last line (cur if nonempty, else done, else nothing)
in one write and exit 0. A line exceeding 4096 bytes aborts with exit 3.
Arguments are ignored (no argc split). In-model stdin reads never fail and
stdout writes always complete, so both binaries' read/write error paths
(exit 1 / exit 4) are dead, and the shared observable trace set is
`drain_from (Z_to_bv 64 1024) f out ec ([], [])`.

The per-binary derivations are `src_LH_to_rd` / `src_init_to_rd`
(`tail1_ns_source`) and `tgt_LH_to_rd` / `tgt_init_to_rd`
(`tail1_ns_target`), glued with `DrainSim.drain_omni_strong_equiv`.

Bytes are `byte = bv 8`, machine values `word = bv 64`; the exit code `ec`
is a word with the integer bound `ec_lt256`.
-/

namespace LinuxProcessSemantics.Examples.tail1_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.DrainSim
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.tail1_ns.SourceMemImage
open LinuxProcessSemantics.Examples.tail1_ns.TargetMemImage
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_code
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_defs
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_source
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_target

theorem omni_strong_universal :
    omni_strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) := by
  intro ⟨sp_source, brk_source, mb_source, rnd_source⟩
    ⟨sp_target, brk_target, mb_target, rnd_target⟩ inp Hens Hent Hvalid
  -- Valid inputs declare Sv48, so the entry predicates give its stack window.
  have Hsv48 := valid_input_va_size inp Hvalid
  have Hspr := ((valid_entry_sv48 _ _ _ Hsv48).1 Hens).1
  have Hspa := ((valid_entry_sv48 _ _ _ Hsv48).1 Hent).1
  have Hva := valid_input_argv inp Hvalid
  have Hve := valid_input_envp inp Hvalid
  obtain ⟨Hr_lo, Hr_hi, _⟩ := Hspr
  obtain ⟨Ha_lo, Ha_hi, _⟩ := Hspa
  apply drain_omni_strong_equiv A (Z_to_bv 64 1024) f out ec a0
    source_segs (src_LH inp.in_argv inp.in_envp sp_source rnd_source inp.in_uid inp.in_hwcap)
    SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
    target_segs (tgt_LH inp.in_argv inp.in_envp sp_target rnd_target inp.in_uid inp.in_hwcap)
    TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target inp
  · exact ec_lt256
  · decide
  · intro a ms H
    apply src_LH_to_rd <;> assumption
  · intro a ms H
    apply tgt_LH_to_rd <;> assumption
  · rw [source_init_pc_val]
    apply src_init_to_rd <;> assumption
  · rw [target_init_pc_val]
    apply tgt_init_to_rd <;> assumption

/-- The legacy statement, through the compatibility `iff`; this is the
theorem Rocq's `Checker.v` pins to `Equivalence.SPEC`. -/
theorem strong_universal :
    strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) :=
  (strong_universal_iff _ _).2 omni_strong_universal

/-- The ascriptions the generated Rocq `Checker.v` makes (`Module Checked <:
Equivalence.SPEC`), as `rwx_flag_ns/Proof.lean` states them: `SPEC` and
`OMNI_SPEC` are `Prop`-valued structures, so these are theorems. -/
theorem specification :
    SPEC (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) :=
  ⟨strong_universal⟩
theorem omni_specification :
    OMNI_SPEC (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) :=
  ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.tail1_ns.Proof
