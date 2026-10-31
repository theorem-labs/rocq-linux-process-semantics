import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit

/-! # Sys.Registry.Kernel.Exit — the arms `Sys/Kernel/Exit.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Exit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def exit_arm : SpecArm := SpecArm.mkSpecArm 93 (fun i => Sys.Kernel.Exit.exit_spec (in_arg i 0) i)
def exit_group_arm : SpecArm := SpecArm.mkSpecArm 94 (fun i => Sys.Kernel.Exit.exit_spec (in_arg i 0) i)
def wait4_arm : SpecArm := SpecArm.mkSpecArm 260 (fun i => Sys.Kernel.Exit.wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Exit
