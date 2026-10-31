import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe

/-! # Sys.Registry.Fs.Pipe — the arm `Sys/Fs/Pipe.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Pipe

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def pipe2_arm : SpecArm := SpecArm.mkSpecArm 59 (fun i => Sys.Fs.Pipe.pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Pipe
