import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls

/-! # Sys.Registry.Kernel.Futex.Syscalls — the arm `Sys/Kernel/Futex/Syscalls.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies the `def` body below verbatim.  The four registers
`futex_spec` reads are Rocq's (`theories/LinuxProcessSem/Sys/SyscallTable.v`,
arm 98): `uaddr`, `op`, `val` and `utime`, the op word whole and `val`
narrowed inside the spec. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Futex.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def futex_arm : SpecArm := SpecArm.mkSpecArm 98 (fun i => Sys.Kernel.Futex.Syscalls.futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Futex.Syscalls
