import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File

/-! # Sys.Registry.Fs.File — the arms `Sys/Fs/File.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.File

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def dup_arm : SpecArm := SpecArm.mkSpecArm 23 (fun i => Sys.Fs.File.dup_spec (fd32 (in_arg i 0)) i)
def dup3_arm : SpecArm := SpecArm.mkSpecArm 24 (fun i => Sys.Fs.File.dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.File
