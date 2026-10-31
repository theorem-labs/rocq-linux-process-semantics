import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap

/-! # Sys.Registry.Mm.Mmap — the arms `Sys/Mm/Mmap.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mmap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def brk_arm : SpecArm := SpecArm.mkSpecArm 214 (fun i => Sys.Mm.Mmap.brk_spec (in_arg i 0) i)

def munmap_arm : SpecArm := SpecArm.mkSpecArm 215 (fun i => Sys.Mm.Mmap.munmap_spec (in_arg i 0) (in_arg i 1) i)

def mmap_arm : SpecArm := SpecArm.mkSpecArm 222 (fun i => Sys.Mm.Mmap.mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mmap
