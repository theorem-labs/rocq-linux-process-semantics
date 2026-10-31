import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir

/-! # Sys.Registry.Fs.Readdir — the arms `Sys/Fs/Readdir.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Readdir

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def getdents64_arm : SpecArm := SpecArm.mkSpecArm 61 (fun i => Sys.Fs.Readdir.getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Readdir
