import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath

/-! # Sys.Registry.Fs.DPath — the arms `Sys/Fs/DPath.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.DPath

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def getcwd_arm : SpecArm := SpecArm.mkSpecArm 17 (fun i => Sys.Fs.DPath.getcwd_spec (in_arg i 1) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.DPath
