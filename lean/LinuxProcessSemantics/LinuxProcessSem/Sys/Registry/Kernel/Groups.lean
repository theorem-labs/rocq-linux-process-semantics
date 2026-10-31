import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups

/-! # Sys.Registry.Kernel.Groups — the arms `Sys/Kernel/Groups.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Groups

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def getgroups_arm : SpecArm := SpecArm.mkSpecArm 158 (fun i => Sys.Kernel.Groups.getgroups_spec (in_arg i 0) i)
def setgroups_arm : SpecArm := SpecArm.mkSpecArm 159 (fun i => Sys.Kernel.Groups.setgroups_spec i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Groups
