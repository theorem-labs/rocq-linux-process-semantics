import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Sync

/-! # Sys.Registry.Fs.Sync — the arms `Sys/Fs/Sync.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Sync

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def fsync_arm : SpecArm := SpecArm.mkSpecArm 82 (fun i => Sys.Fs.Sync.fsync_spec (fd32 (in_arg i 0)) i)
def fdatasync_arm : SpecArm := SpecArm.mkSpecArm 83 (fun i => Sys.Fs.Sync.fsync_spec (fd32 (in_arg i 0)) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Sync
