import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl

/-! # Sys.Registry.Fs.Fcntl — the arms `Sys/Fs/Fcntl.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Fcntl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def fcntl_arm : SpecArm := SpecArm.mkSpecArm 25 (fun i => Sys.Fs.Fcntl.fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Fcntl
