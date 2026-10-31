import LinuxProcessSemantics.LinuxProcessSem.Checks.All
import LinuxProcessSemantics.LinuxProcessSem.Checks.Policy

/-! The public theorem pins and the environment trust audit.

`Checks.All` is written by `lean/lakefile.lean` from the library's module
glob, so a new module is audited by the build itself and no shared import
list has to be edited for it to be walked. `tools/check_lean_policy.py`
freshly elaborates this module after the build and checks that its imports
cover every source and generated project module, which is what catches a
walk that missed one.
`#pin_theorem` checks complete types, not just the existence of names. The
environment audit checks every declaration, including definitions and unused
axioms, and rejects unchecked runtime substitutions on project declarations.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Axioms

open LinuxProcessSemantics.LinuxProcessSem.Checks.Policy

#pin_theorem LinuxProcessSemantics.Examples.rwx_flag_ns.Proof.strong_universal :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_T
    LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage.Source.image
    LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage.Target.image

#pin_theorem LinuxProcessSemantics.Examples.rwx_flag_ns.Proof.omni_strong_universal :
  LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_universal_T
    LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage.Source.image
    LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage.Target.image

#pin_theorem LinuxProcessSemantics.Examples.rwx_flag_ns.Proof.source_terminates :
  ∀ (en : LinuxProcessSemantics.LinuxProcessSem.Run.ExecEntry)
    (inp : LinuxProcessSemantics.LinuxProcessSem.State.ProcInput),
    LinuxProcessSemantics.LinuxProcessSem.Run.valid_input inp →
    LinuxProcessSemantics.LinuxProcessSem.Run.valid_entry
      LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage.Source.image en inp →
    LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run
      LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage.Source.image
      LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit en inp
      (LinuxProcessSemantics.Common.ExitSim.exit_post 5 inp.in_fs)

#pin_theorem LinuxProcessSemantics.Examples.rwx_flag_ns.Proof.target_terminates :
  ∀ (en : LinuxProcessSemantics.LinuxProcessSem.Run.ExecEntry)
    (inp : LinuxProcessSemantics.LinuxProcessSem.State.ProcInput),
    LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run
      LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage.Target.image
      LinuxProcessSemantics.LinuxProcessSem.State.target_alloc_limit en inp
      (LinuxProcessSemantics.Common.ExitSim.exit_post 5 inp.in_fs)

#pin_theorem LinuxProcessSemantics.Examples.rwx_flag_ns.rwx_flag_ns_code.SourceWf :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.IMAGE_WF
    LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage.Source.image

#pin_theorem LinuxProcessSemantics.Examples.rwx_flag_ns.rwx_flag_ns_code.TargetWf :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.IMAGE_WF
    LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage.Target.image

#pin_theorem LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.exit_dispatch_artifact :
  ∀ (i : LinuxProcessSemantics.LinuxProcessSem.State.SyscallInput)
    (m : LinuxProcessSemantics.LinuxProcessSem.State.Model)
    (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome
      LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect),
    LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.exit_number i.in_sysno →
    (LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec i m o ↔
      ∃ c, LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.artifact_clause = some c ∧
        LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.denote c i m o)

#pin_theorem LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.denote_normal_form :
  ∀ (c : LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.Clause)
    (i : LinuxProcessSemantics.LinuxProcessSem.State.SyscallInput)
    (m : LinuxProcessSemantics.LinuxProcessSem.State.Model)
    (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome
      LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect),
    LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.denote c i m o ↔
      o = LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.evaluate c i m

#pin_theorem LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit.status_mod256 :
  ∀ code : LinuxProcessSemantics.Riscv.Prelude.word,
    LinuxProcessSemantics.Riscv.Prelude.bv_unsigned
      (LinuxProcessSemantics.Riscv.Prelude.bv_and code
        (LinuxProcessSemantics.Riscv.Prelude.Z_to_bv 64 255)) =
      LinuxProcessSemantics.Riscv.Prelude.bv_unsigned code % 256

-- Keep the original regression witnesses live as the pilot adds new roots.
#check LinuxProcessSemantics.LinuxProcessSem.Checks.Examples.exit0_image_must_exit_zero
#check LinuxProcessSemantics.LinuxProcessSem.Checks.Examples.exit1_image_must_exit_one
#check LinuxProcessSemantics.LinuxProcessSem.Checks.Examples.exit1_image_refutes_must_exit_zero
#check LinuxProcessSemantics.LinuxProcessSem.Checks.Examples.undecodable_image_refutes_must_exit
#check LinuxProcessSemantics.EquivalenceDefinition.MustExit.must_exit_with_realizes
#check LinuxProcessSemantics.EquivalenceDefinition.MustExit.must_exit_with_exclusive

#print axioms LinuxProcessSemantics.Examples.rwx_flag_ns.Proof.strong_universal
#print axioms LinuxProcessSemantics.Examples.rwx_flag_ns.Proof.source_terminates
#print axioms LinuxProcessSemantics.Examples.rwx_flag_ns.Proof.target_terminates

run_cmd auditEnvironment

end LinuxProcessSemantics.LinuxProcessSem.Checks.Axioms
