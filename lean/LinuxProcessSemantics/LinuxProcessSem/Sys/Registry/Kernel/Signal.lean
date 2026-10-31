import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal

/-! # Sys.Registry.Kernel.Signal — the arms `Sys/Kernel/Signal.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Signal

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def tkill_arm : SpecArm := SpecArm.mkSpecArm 130 (fun i => Sys.Kernel.Signal.tkill_spec (pid32 (in_arg i 0)) (Sys.Kernel.Signal.sig32 (in_arg i 1)) i)
def tgkill_arm : SpecArm := SpecArm.mkSpecArm 131 (fun i => Sys.Kernel.Signal.tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) i)
def sigaltstack_arm : SpecArm := SpecArm.mkSpecArm 132 (fun i => Sys.Kernel.Signal.sigaltstack_spec (in_arg i 0) (in_arg i 1) i)
def rt_sigaction_arm : SpecArm := SpecArm.mkSpecArm 134 (fun i => Sys.Kernel.Signal.rt_sigaction_spec (Sys.Kernel.Signal.sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
def rt_sigprocmask_arm : SpecArm := SpecArm.mkSpecArm 135 (fun i => Sys.Kernel.Signal.rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Signal
