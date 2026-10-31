import LinuxProcessSemantics.Common.ShapeAlg
import LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_source
import LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_target

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # modprint-ns: equivalence proof, top-level glue

PROOF-SIDE, not trusted spec. Mirrors `theories/Examples/modprint_ns/Proof.v`
at the baseline above: `omni_strong_universal` and `strong_universal` keep
their names and statements, and the second is derived from the first through
the same `strong_universal_iff`.

Both binaries write `udec (argc mod 7) ++ "\n"` to fd 1 and exit 0, with no
input-dependent control flow, so there is no case split. A channel write
delivers a nonempty prefix of its own choosing and neither binary retries, so
the behavior is the delivered-prefix family `t_writes_pick`; the proof is one
application of `cat_omni_strong_equiv_alg` to the two `to_wexit` derivations,
which end at the same `(mod_bufs argc, 0)`.
-/

namespace LinuxProcessSemantics.Examples.modprint_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.Examples.modprint_ns.SourceMemImage
open LinuxProcessSemantics.Examples.modprint_ns.TargetMemImage
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_code
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_source
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_target

theorem omni_strong_universal :
    omni_strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) := by
  intro es et inp Hens Hent Hvalid
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  -- the input declares Sv48 (`Run.valid_input` pins it), so the entry
  -- predicate is the literal Sv48 one (`Run.valid_entry_sv48`)
  have Hsv48 := valid_input_va_size inp Hvalid
  obtain ⟨⟨Hr_lo, Hr_hi, _⟩, _⟩ := (valid_entry_sv48 _ _ _ Hsv48).1 Hens
  obtain ⟨⟨Ha_lo, Ha_hi, _⟩, _⟩ := (valid_entry_sv48 _ _ _ Hsv48).1 Hent
  obtain ⟨Hva, Hve, _⟩ := Hvalid
  apply cat_omni_strong_equiv_alg
    source_segs SourceMemImage_init_pc source_phdrs sp_source brk_source mb_source rnd_source
    target_segs TargetMemImage_init_pc target_phdrs sp_target brk_target mb_target rnd_target
    (mod_bufs (inp.in_argv.length : Int)) (Z_to_bv 64 0) inp
  · rw [source_init_pc_val]
    exact source_wexit inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap Hva Hve
      sp_source rnd_source Hr_lo Hr_hi
  · rw [target_init_pc_val]
    exact target_wexit inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap Hva Hve
      sp_target rnd_target Ha_lo Ha_hi
  · -- The single buffer is the two bytes `[digit; '\n']`, well under the
    -- model's read/write transfer bound.
    intro b Hb
    simp only [mod_bufs, List.mem_singleton] at Hb
    subst Hb
    unfold buf_modeled
    rw [mod_buf_bytes _ (by omega)]
    simp only [List.length_cons, List.length_nil]
    unfold rw_bytes_max
    omega

/-- The legacy statement, through the compat `iff`; this is the theorem the
checker pins to `Equivalence.SPEC`. -/
theorem strong_universal :
    strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) :=
  (strong_universal_iff _ _).2 omni_strong_universal

end LinuxProcessSemantics.Examples.modprint_ns.Proof
