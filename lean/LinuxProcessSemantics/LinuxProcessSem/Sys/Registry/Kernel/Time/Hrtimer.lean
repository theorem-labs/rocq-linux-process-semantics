import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer

/-! # Sys.Registry.Kernel.Time.Hrtimer — the arms `Sys/Kernel/Time/Hrtimer.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Time.Hrtimer

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def nanosleep_arm : SpecArm := SpecArm.mkSpecArm 101 (fun i => Sys.Kernel.Time.Hrtimer.nanosleep_spec (in_arg i 0) (in_arg i 1) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Time.Hrtimer
