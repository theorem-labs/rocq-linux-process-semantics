import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd

/-! # Sys.Registry.Fs.Timerfd — the arms `Sys/Fs/Timerfd.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Timerfd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def timerfd_create_arm : SpecArm := SpecArm.mkSpecArm 85 (fun i => Sys.Fs.Timerfd.timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Timerfd
