import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork

/-! # Sys.Registry.Kernel.Fork — the arms `Sys/Kernel/Fork.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Fork

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def set_tid_address_arm : SpecArm := SpecArm.mkSpecArm 96 (fun i => Sys.Kernel.Fork.set_tid_address_spec i)
def clone_arm : SpecArm := SpecArm.mkSpecArm 220 (fun i => Sys.Kernel.Fork.clone_spec (in_arg i 0) i)
def clone3_arm : SpecArm := SpecArm.mkSpecArm 435 (fun i => Sys.Kernel.Fork.clone3_spec (in_arg i 0) (in_arg i 1) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Fork
