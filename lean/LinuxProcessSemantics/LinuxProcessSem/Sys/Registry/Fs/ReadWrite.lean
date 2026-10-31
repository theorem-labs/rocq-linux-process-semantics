import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite

/-! # Sys.Registry.Fs.ReadWrite — the arms `Sys/Fs/ReadWrite.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.  The seven syscalls of the Rocq file
register here as their tickets land, one line each, in syscall-number
order: `read` (63) is ticket S-Fs-ReadWrite-read's and its line lands
above `write`'s from its own PR.
`lseek` (62), `pread64` (67) and `pwrite64` (68) are ticket
S-Fs-ReadWrite-pread-pwrite-lseek's, around those two.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.ReadWrite

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def lseek_arm : SpecArm := SpecArm.mkSpecArm 62 (fun i => Sys.Fs.ReadWrite.lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i)

def read_arm : SpecArm := SpecArm.mkSpecArm 63 (fun i => Sys.Fs.ReadWrite.read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)

def write_arm : SpecArm := SpecArm.mkSpecArm 64 (fun i => Sys.Fs.ReadWrite.write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def readv_arm : SpecArm := SpecArm.mkSpecArm 65 (fun i => Sys.Fs.ReadWrite.readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def writev_arm : SpecArm := SpecArm.mkSpecArm 66 (fun i => Sys.Fs.ReadWrite.writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)

def pread64_arm : SpecArm := SpecArm.mkSpecArm 67 (fun i => Sys.Fs.ReadWrite.pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)

def pwrite64_arm : SpecArm := SpecArm.mkSpecArm 68 (fun i => Sys.Fs.ReadWrite.pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.ReadWrite
