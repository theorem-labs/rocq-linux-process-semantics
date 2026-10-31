import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise

/-! # Sys.Registry.Mm.Madvise — the arms `Sys/Mm/Madvise.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Madvise

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def madvise_arm : SpecArm := SpecArm.mkSpecArm 233 (fun i => Sys.Mm.Madvise.madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Madvise
