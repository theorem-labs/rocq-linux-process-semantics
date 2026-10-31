import LinuxProcessSemantics.Examples.rwx_flag_ns.Proof

/-! Concrete accepting and rejecting traces for the real binary pair.
These use the universal execution proofs at independently validated entries;
the expected exit values are written explicitly, not read from the program.
-/

namespace LinuxProcessSemantics.Examples.rwx_flag_ns.Checks

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.Domain
open LinuxProcessSemantics.Examples.rwx_flag_ns.Proof

/-- Quantify the entire draw separately for each image: neither its random
word nor its page-slack function needs to agree between the binaries. -/
theorem independent_draws_preserve_equivalence (ds dt : EntryDraw)
    (inp : ProcInput) (hi : valid_input inp) :
    strong_equiv Source.image Target.image
      { source_entry with en_draw := ds } { target_entry with en_draw := dt } inp :=
  strong_universal _ _ inp (source_entry_with_draw_valid ds inp hi)
    (target_entry_with_draw_valid dt inp hi) hi

theorem independent_draws_and_both_hardware_masks (ds dt : EntryDraw) :
    strong_equiv Source.image Target.image
      { source_entry with en_draw := ds } { target_entry with en_draw := dt } input_witness ∧
    strong_equiv Source.image Target.image
      { source_entry with en_draw := ds } { target_entry with en_draw := dt } vector_input_witness :=
  ⟨independent_draws_preserve_equivalence ds dt _ input_witness_valid,
    independent_draws_preserve_equivalence ds dt _ vector_input_witness_valid⟩

/-- The concrete instance cannot accidentally use equal entry draws. -/
theorem equality_of_entry_draws_is_not_assumed : source_entry.en_draw ≠ target_entry.en_draw := by
  intro h
  exact entry_witnesses_have_distinct_random_draws (congrArg EntryDraw.ed_random h)

theorem source_traces (en : ExecEntry) (inp : ProcInput) (hi : valid_input inp)
    (he : valid_entry Source.image en inp) (tr : List event) :
    (run Source.image source_alloc_limit en inp).bh_traces tr ↔
      is_prefix tr [ExitEv 5 inp.in_fs] := by
  have hmask : bv_and (5 : word) (Z_to_bv 64 255) = (5 : word) := by decide +kernel
  simpa only [hmask] using
    exit_obs_iff_te Source.image source_alloc_limit en 5 inp (source_terminates en inp hi he) tr

theorem target_traces (en : ExecEntry) (inp : ProcInput) (tr : List event) :
    (run Target.image target_alloc_limit en inp).bh_traces tr ↔
      is_prefix tr [ExitEv 5 inp.in_fs] := by
  have hmask : bv_and (5 : word) (Z_to_bv 64 255) = (5 : word) := by decide +kernel
  simpa only [hmask] using
    exit_obs_iff_te Target.image target_alloc_limit en 5 inp (target_terminates en inp) tr

theorem source_exit_five_accepted :
    (run Source.image source_alloc_limit source_entry input_witness).bh_traces
      [ExitEv 5 input_witness.in_fs] :=
  (source_traces _ _ input_witness_valid (source_entry_valid _ input_witness_valid) _).2 (is_prefix_refl _)

theorem target_exit_five_accepted :
    (run Target.image target_alloc_limit target_entry input_witness).bh_traces
      [ExitEv 5 input_witness.in_fs] :=
  (target_traces _ _ _).2 (is_prefix_refl _)

theorem source_exit_six_rejected :
    ¬ (run Source.image source_alloc_limit source_entry input_witness).bh_traces
      [ExitEv 6 input_witness.in_fs] := by
  rw [source_traces _ _ input_witness_valid (source_entry_valid _ input_witness_valid)]
  intro h
  have hcode : (6 : word) = (5 : word) := (event.ExitEv.inj h.1).1
  exact (by decide +kernel : (6 : word) ≠ (5 : word)) hcode

theorem target_exit_six_rejected :
    ¬ (run Target.image target_alloc_limit target_entry input_witness).bh_traces
      [ExitEv 6 input_witness.in_fs] := by
  rw [target_traces]
  intro h
  have hcode : (6 : word) = (5 : word) := (event.ExitEv.inj h.1).1
  exact (by decide +kernel : (6 : word) ≠ (5 : word)) hcode

theorem vector_mask_source_exit_five_accepted :
    (run Source.image source_alloc_limit source_entry vector_input_witness).bh_traces
      [ExitEv 5 vector_input_witness.in_fs] :=
  (source_traces _ _ vector_input_witness_valid (source_entry_valid _ vector_input_witness_valid) _).2 (is_prefix_refl _)

theorem vector_mask_source_exit_six_rejected :
    ¬ (run Source.image source_alloc_limit source_entry vector_input_witness).bh_traces
      [ExitEv 6 vector_input_witness.in_fs] := by
  intro h
  have hp := (source_traces _ _ vector_input_witness_valid (source_entry_valid _ vector_input_witness_valid) _).1 h
  have hcode := (event.ExitEv.inj hp.1).1
  exact (by decide +kernel : (6 : word) ≠ (5 : word)) hcode

theorem source_errors_rejected (en : ExecEntry) (inp : ProcInput) (hi : valid_input inp)
    (he : valid_entry Source.image en inp) :
    ¬ (run Source.image source_alloc_limit en inp).bh_errors :=
  exit_no_error_te _ _ _ _ _ (source_terminates en inp hi he)

theorem target_errors_rejected (en : ExecEntry) (inp : ProcInput) :
    ¬ (run Target.image target_alloc_limit en inp).bh_errors :=
  exit_no_error_te _ _ _ _ _ (target_terminates en inp)

end LinuxProcessSemantics.Examples.rwx_flag_ns.Checks
