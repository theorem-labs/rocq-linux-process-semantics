import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect

/-! # Sys.Registry.Mm.Mprotect — the arms `Sys/Mm/Mprotect.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mprotect

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def mprotect_arm : SpecArm := SpecArm.mkSpecArm 226 (fun i => Sys.Mm.Mprotect.mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mprotect
