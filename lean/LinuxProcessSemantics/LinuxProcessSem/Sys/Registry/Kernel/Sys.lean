import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys

/-! # Sys.Registry.Kernel.Sys — the arms `Sys/Kernel/Sys.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Sys

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def setgid_arm : SpecArm := SpecArm.mkSpecArm 144 (fun i => Sys.Kernel.Sys.setid_spec Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) i)
def setuid_arm : SpecArm := SpecArm.mkSpecArm 146 (fun i => Sys.Kernel.Sys.setid_spec Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) i)
def setresuid_arm : SpecArm := SpecArm.mkSpecArm 147 (fun i => Sys.Kernel.Sys.setresid_spec Sys.Kernel.Sys.cred_uids Sys.Kernel.Sys.set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)
def setresgid_arm : SpecArm := SpecArm.mkSpecArm 149 (fun i => Sys.Kernel.Sys.setresid_spec Sys.Kernel.Sys.cred_gids Sys.Kernel.Sys.set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)
def setsid_arm : SpecArm := SpecArm.mkSpecArm 157 (fun i => Sys.Kernel.Sys.setsid_spec i)
def uname_arm : SpecArm := SpecArm.mkSpecArm 160 (fun i => Sys.Kernel.Sys.uname_spec (in_arg i 0) i)
def prctl_arm : SpecArm := SpecArm.mkSpecArm 167 (fun i => Sys.Kernel.Sys.prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i)
def getpid_arm : SpecArm := SpecArm.mkSpecArm 172 (fun i => Sys.Kernel.Sys.getpid_spec i)
def getuid_arm : SpecArm := SpecArm.mkSpecArm 174 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_uid i)
def geteuid_arm : SpecArm := SpecArm.mkSpecArm 175 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_euid i)
def getgid_arm : SpecArm := SpecArm.mkSpecArm 176 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_gid i)
def getegid_arm : SpecArm := SpecArm.mkSpecArm 177 (fun i => Sys.Kernel.Sys.getid_spec Creds.cr_egid i)
def gettid_arm : SpecArm := SpecArm.mkSpecArm 178 (fun i => Sys.Kernel.Sys.gettid_spec i)
def prlimit64_arm : SpecArm := SpecArm.mkSpecArm 261 (fun i => Sys.Kernel.Sys.prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Sys
