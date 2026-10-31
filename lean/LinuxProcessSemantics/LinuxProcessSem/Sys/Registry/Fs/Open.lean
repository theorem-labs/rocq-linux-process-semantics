import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open

/-! # Sys.Registry.Fs.Open — the arms `Sys/Fs/Open.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.  Rocq's table line for
openat (56) hands the arm `fd32 (in_arg i 0)`, the pathname pointer and
the flags word whole (`theories/LinuxProcessSem/Sys/SyscallTable.v`).
The twin is shared with S-Fs-Open-close-ftruncate, whose two arms (46, 57)
are added here as lines of their own.
Those two lines take their shapes from Rocq's table lines as well —
`close_spec (fd32 (in_arg i 0)) i` and
`ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i` (`SyscallTable.v`) —
so the fd is narrowed and ftruncate's length is the whole register on
both sides.
The faccessat (48) and faccessat2 (439) lines take their argument
shapes from the same two Rocq table lines (`SyscallTable.v`), so a
truncation the Rocq arm sees is the one the Lean arm sees.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Open

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def openat_arm : SpecArm := SpecArm.mkSpecArm 56 (fun i => Sys.Fs.Open.openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def faccessat_arm : SpecArm := SpecArm.mkSpecArm 48 (fun i => Sys.Fs.Open.faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def faccessat2_arm : SpecArm := SpecArm.mkSpecArm 439 (fun i => Sys.Fs.Open.faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)

def close_arm : SpecArm := SpecArm.mkSpecArm 57 (fun i => Sys.Fs.Open.close_spec (fd32 (in_arg i 0)) i)
def ftruncate_arm : SpecArm := SpecArm.mkSpecArm 46 (fun i => Sys.Fs.Open.ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Open
