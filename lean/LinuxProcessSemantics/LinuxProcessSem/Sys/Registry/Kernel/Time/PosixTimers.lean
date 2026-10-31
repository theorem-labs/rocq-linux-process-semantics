import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers

/-! # Sys.Registry.Kernel.Time.PosixTimers — the arms `Sys/Kernel/Time/PosixTimers.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Time.PosixTimers

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def clock_gettime_arm : SpecArm := SpecArm.mkSpecArm 113 (fun i => Sys.Kernel.Time.PosixTimers.clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Time.PosixTimers
