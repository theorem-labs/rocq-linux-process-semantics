import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll

/-! # Sys.Registry.Fs.EventPoll — the arms `Sys/Fs/EventPoll.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.EventPoll

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def epoll_create1_arm : SpecArm := SpecArm.mkSpecArm 20 (fun i => Sys.Fs.EventPoll.epoll_create1_spec (flag32 (in_arg i 0)) i)
def epoll_ctl_arm : SpecArm := SpecArm.mkSpecArm 21 (fun i => Sys.Fs.EventPoll.epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i)
def epoll_pwait_arm : SpecArm := SpecArm.mkSpecArm 22 (fun i => Sys.Fs.EventPoll.epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.EventPoll
