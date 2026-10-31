import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sched.Syscalls

/-! # Sys.Registry.Kernel.Sched.Syscalls — the arms `Sys/Kernel/Sched/Syscalls.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Sched.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def sched_setscheduler_arm : SpecArm := SpecArm.mkSpecArm 119 (fun i => Sys.Kernel.Sched.Syscalls.sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
def sched_getaffinity_arm : SpecArm := SpecArm.mkSpecArm 123 (fun i => Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec (in_arg i 1) i)
def sched_yield_arm : SpecArm := SpecArm.mkSpecArm 124 (fun i => Sys.Kernel.Sched.Syscalls.sched_yield_spec i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Sched.Syscalls
