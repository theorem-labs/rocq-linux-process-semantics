import LinuxProcessSemantics.Examples.rwx_flag_ns.SourceExec
import LinuxProcessSemantics.Examples.rwx_flag_ns.TargetExec
import LinuxProcessSemantics.Examples.rwx_flag_ns.Domain

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! The existing example's universal contracts, with an independent
termination guarantee for each binary. The guarantees require actual total
execution to the sole exit event; they cannot use the equivalence relation's
all-source-executions-error escape. The images are the generated translations
of the reference snapshots, not instruction lists manufactured for the proof.

Mirrors `theories/Examples/rwx_flag_ns/Proof.v` at the baseline above:
`omni_strong_universal` and `strong_universal` keep their names and their
statements, and the second is derived from the first through the same
`strong_universal_iff`. Rocq glues two `to_wexit` derivations with
`cat_omni_strong_equiv_te`; this port glues the two termination theorems
with `exit_omni_strong_equiv_of_runs`, because it states termination
outright (`lean/README.md`, "Pilot contract").

Which dispatcher arms the theorem rests on: both binaries' derivations are
`to_exit` derivations (`Common/ExitSim.lean`), whose every step requires
no pending service call and whose end requires the pending one to be an
exit number, and the proof meets the syscall table only through
`Common/ExitSim.lean`'s `syscall_spec_exit`, which looks up the two exit
numbers, 93 and 94, both dispatched to `exit_spec`. An arm ported at
another number cannot enter this proof; a change to either exit line's
shape can, and that lemma is where it shows. The runs themselves issue
`exit` (93): both derivations end with `some 93` pending. The run-side
witness of the same arm set is the recording of both binaries under the
pinned kernel that ticket E0 committed as
`testing/syscall-check/traces/examples.json`, whose `--verify` reports a
re-snapshotted binary as a stale recording, and
`tools/test_lean_port_graph.py` holds this example's plan dependencies to
the arms recorded there. This stops being true if either binary is
re-snapshotted to issue another syscall: the recording goes stale first,
and the derivation above stops closing.
-/

namespace LinuxProcessSemantics.Examples.rwx_flag_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.SourceExec
open LinuxProcessSemantics.Examples.rwx_flag_ns.TargetExec

/-- The input's validity is a hypothesis because the entry window follows
the input's address-space declaration (`Run.valid_entry`): a valid input
declares Sv48, and under Sv48 the entry predicate is the literal window
`source_exit` reasons about (`Run.valid_entry_sv48`). -/
theorem source_terminates (en : ExecEntry) (inp : ProcInput) (hi : valid_input inp)
    (he : valid_entry Source.image en inp) :
    omni_run Source.image source_alloc_limit en inp (exit_post 5 inp.in_fs) := by
  cases en with
  | mkEntry sp brk0 mb draw =>
    have he' := (valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)).1 he
    exact exit_omni_run_te Source.loaded_segments Source.init_pc Source.phdrs
      sp brk0 mb draw source_alloc_limit 5 inp
      (source_exit sp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap draw he'.1.1 he'.1.2.1)

theorem source_abort_terminates (en : ExecEntry) (inp : ProcInput)
    (hi : valid_input_abort inp) (he : valid_entry Source.image en inp) :
    omni_run Source.image source_alloc_limit en inp (exit_post 5 inp.in_fs) := by
  cases en with
  | mkEntry sp brk0 mb draw =>
    have he' := (valid_entry_sv48 _ _ _ (valid_input_abort_va_size inp hi)).1 he
    exact exit_omni_run_te Source.loaded_segments Source.init_pc Source.phdrs
      sp brk0 mb draw source_alloc_limit 5 inp
      (source_exit sp inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap draw he'.1.1 he'.1.2.1)

theorem target_terminates (en : ExecEntry) (inp : ProcInput) :
    omni_run Target.image target_alloc_limit en inp (exit_post 5 inp.in_fs) := by
  cases en with
  | mkEntry sp brk0 mb draw =>
    exact exit_omni_run_te Target.loaded_segments Target.init_pc Target.phdrs
      sp brk0 mb draw target_alloc_limit 5 inp
      (target_exit sp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap draw)

theorem omni_strong_universal : omni_strong_universal_T Source.image Target.image := by
  intro es et inp hs _ hi
  exact exit_omni_strong_equiv_of_runs _ _ _ _ 5 inp
    (source_terminates es inp hi hs) (target_terminates et inp)

theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

theorem strong_universal_error_free : strong_universal_error_free_T Source.image Target.image := by
  intro es et inp hs _ hi
  have hsrun := source_terminates es inp hi hs
  have htrun := target_terminates et inp
  exact ⟨exit_no_error_te _ _ _ _ _ hsrun, exit_no_error_te _ _ _ _ _ htrun,
    fun tr => (exit_obs_iff_te _ _ _ _ _ hsrun tr).trans (exit_obs_iff_te _ _ _ _ _ htrun tr).symm⟩

theorem strong_universal_abort : strong_universal_T_abort Source.image Target.image := by
  intro es et inp hs _ hi
  exact exit_strong_equiv_of_runs _ _ _ _ 5 inp
    (source_abort_terminates es inp hi hs) (target_terminates et inp)

/-- The ascriptions the generated Rocq `Checker.v` makes (`Module Checked <:
Equivalence.SPEC`): `SPEC` and `OMNI_SPEC` are `Prop`-valued structures, so
these are theorems, not definitions. Lean 4.34 warns on a `def` of a
proposition, and review treats a warning as red. -/
theorem specification : SPEC Source.image Target.image := ⟨strong_universal⟩
theorem omni_specification : OMNI_SPEC Source.image Target.image := ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.rwx_flag_ns.Proof
