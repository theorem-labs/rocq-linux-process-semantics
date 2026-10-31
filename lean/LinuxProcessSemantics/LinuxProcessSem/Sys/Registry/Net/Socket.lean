import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket

/-! # Sys.Registry.Net.Socket — the arms `Sys/Net/Socket.lean` puts in the table

A registry file, read by `tools/gen_lean_registry.py`, whose docstring
states the shape a line here may take; the table and its pins are
rendered from it on every build.

TRUST BOUNDARY: this file is part of the trusted specification; the
generated table copies each `def` body below verbatim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Net.Socket

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

def socket_arm : SpecArm := SpecArm.mkSpecArm 198 (fun i => Sys.Net.Socket.socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
def socketpair_arm : SpecArm := SpecArm.mkSpecArm 199 (fun i => Sys.Net.Socket.socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
def bind_arm : SpecArm := SpecArm.mkSpecArm 200 (fun i => Sys.Net.Socket.bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def listen_arm : SpecArm := SpecArm.mkSpecArm 201 (fun i => Sys.Net.Socket.listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i)
def accept_arm : SpecArm := SpecArm.mkSpecArm 202 (fun i => Sys.Net.Socket.accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i)
def connect_arm : SpecArm := SpecArm.mkSpecArm 203 (fun i => Sys.Net.Socket.connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def getsockname_arm : SpecArm := SpecArm.mkSpecArm 204 (fun i => Sys.Net.Socket.getsockname_spec (fd32 (in_arg i 0)) i)
def getpeername_arm : SpecArm := SpecArm.mkSpecArm 205 (fun i => Sys.Net.Socket.getpeername_spec (fd32 (in_arg i 0)) i)
def sendto_arm : SpecArm := SpecArm.mkSpecArm 206 (fun i => Sys.Net.Socket.sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)
def recvfrom_arm : SpecArm := SpecArm.mkSpecArm 207 (fun i => Sys.Net.Socket.recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def setsockopt_arm : SpecArm := SpecArm.mkSpecArm 208 (fun i => Sys.Net.Socket.setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i)
def getsockopt_arm : SpecArm := SpecArm.mkSpecArm 209 (fun i => Sys.Net.Socket.getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i)
def shutdown_arm : SpecArm := SpecArm.mkSpecArm 210 (fun i => Sys.Net.Socket.shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i)
def sendmsg_arm : SpecArm := SpecArm.mkSpecArm 211 (fun i => Sys.Net.Socket.sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
def recvmsg_arm : SpecArm := SpecArm.mkSpecArm 212 (fun i => Sys.Net.Socket.recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i)
def accept4_arm : SpecArm := SpecArm.mkSpecArm 242 (fun i => Sys.Net.Socket.accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Net.Socket
