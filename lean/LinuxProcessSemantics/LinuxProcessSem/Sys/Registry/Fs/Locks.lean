import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks

/-! # Sys.Registry.Fs.Locks — the arms `Sys/Fs/Locks.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Locks

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def flock_arm : SpecArm := SpecArm.mkSpecArm 32 (fun i => Sys.Fs.Locks.flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Locks
