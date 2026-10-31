import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Stat

/-! # Sys.Registry.Fs.Stat — the arms `Sys/Fs/Stat.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Stat

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def readlinkat_arm : SpecArm := SpecArm.mkSpecArm 78 (fun i => Sys.Fs.Stat.readlinkat_spec (fd32 (in_arg i 0)) i)
def newfstatat_arm : SpecArm := SpecArm.mkSpecArm 79 (fun i => Sys.Fs.Stat.newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i)
def fstat_arm : SpecArm := SpecArm.mkSpecArm 80 (fun i => Sys.Fs.Stat.fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Stat
