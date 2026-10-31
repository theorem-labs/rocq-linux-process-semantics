import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl

/-! # Sys.Registry.Fs.Ioctl — the arm `Sys/Fs/Ioctl.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

The arm is Rocq's (`theories/LinuxProcessSem/Sys/SyscallTable.v`, the
`ioctl` line): both arguments pass through the 32-bit truncations
`Syscall.fd32` and `Syscall.cmd32`, because `SYSCALL_DEFINE3(ioctl,
unsigned int, fd, unsigned int, cmd, unsigned long, arg)` (fs/ioctl.c:583,
Linux v6.18.46) declares them `unsigned int`; the third argument is not
read on any path the spec models.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Ioctl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def ioctl_arm : SpecArm := SpecArm.mkSpecArm 29 (fun i => Sys.Fs.Ioctl.ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Ioctl
