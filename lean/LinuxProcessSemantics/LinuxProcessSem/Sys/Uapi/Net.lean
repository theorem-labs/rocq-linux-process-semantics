import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uapi.Net — the socket ABI constants

One part of `theories/LinuxProcessSem/Sys/Uapi.v` (see `Sys/Uapi.lean`
for the split).  WHAT GOES HERE: address families, socket types and the
flag bits beside them, protocol numbers, the three address lengths the
socket calls test, option levels, `shutdown`'s directions, and the one
`MSG_` bit a spec reads.

TRUST BOUNDARY: this file is part of the trusted specification.

riscv64 has no asm/socket.h and no asm/errno.h of its own —
arch/riscv/include/uapi/asm/Kbuild generates only unistd_32.h and
unistd_64.h — so every constant here is the asm-generic or
architecture-independent one.  Rocq read them at v6.12; the line numbers
below are Linux v6.18.46's, commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5,
where every value is the same. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! ## Address families (include/linux/socket.h) -/

/-- `#define AF_UNSPEC 0` (include/linux/socket.h:190, Linux v6.18.46,
commit 1f99e9ab748f). -/
def AF_UNSPEC : Int := 0

/-- `#define AF_INET 2` (include/linux/socket.h:193, Linux v6.18.46,
commit 1f99e9ab748f). -/
def AF_INET : Int := 2

/-- `#define NPROTO AF_MAX` (include/uapi/linux/net.h:25) over
`#define AF_MAX 46` (include/linux/socket.h:244), both Linux v6.18.46,
commit 1f99e9ab748f — one past the last named family, not the last
family. -/
def NPROTO : Int := 46

/-! ## Socket types (include/linux/net.h) -/

/-- `SOCK_STREAM = 1` in `enum sock_type` (include/linux/net.h:64, Linux
v6.18.46, commit 1f99e9ab748f). -/
def SOCK_STREAM : Int := 1

/-- `SOCK_DGRAM = 2` (include/linux/net.h:65, Linux v6.18.46, commit
1f99e9ab748f). -/
def SOCK_DGRAM : Int := 2

/-- `SOCK_RAW = 3` (include/linux/net.h:66, Linux v6.18.46, commit
1f99e9ab748f). -/
def SOCK_RAW : Int := 3

/-- `SOCK_SEQPACKET = 5` (include/linux/net.h:68, Linux v6.18.46, commit
1f99e9ab748f). -/
def SOCK_SEQPACKET : Int := 5

/-- `SOCK_DCCP = 6` (include/linux/net.h:69, Linux v6.18.46, commit
1f99e9ab748f). -/
def SOCK_DCCP : Int := 6

/-- `SOCK_PACKET = 10` (include/linux/net.h:70, Linux v6.18.46, commit
1f99e9ab748f). -/
def SOCK_PACKET : Int := 10

/-- `#define SOCK_MAX (SOCK_PACKET + 1)` (include/linux/net.h:74, Linux
v6.18.46, commit 1f99e9ab748f). -/
def SOCK_MAX : Int := 11

/-- `#define SOCK_TYPE_MASK 0xf` (include/linux/net.h:77, Linux v6.18.46,
commit 1f99e9ab748f): the low four bits of `type` are the socket type and
the rest are flags. -/
def SOCK_TYPE_MASK : Int := 15

/-- `SOCK_CLOEXEC` is `O_CLOEXEC` on EVERY architecture — `#define
SOCK_CLOEXEC O_CLOEXEC` (include/linux/net.h:80, Linux v6.18.46, commit
1f99e9ab748f) sits outside every `#ifndef` — so it is arch-dependent only
through `O_CLOEXEC` itself, which riscv64 takes from
include/uapi/asm-generic/fcntl.h, having no asm/fcntl.h of its own.  What
IS arch-overridden nearby: the `enum sock_type` under `#ifndef
ARCH_HAS_SOCKET_TYPES` (net.h:47), which only mips defines
(arch/mips/include/asm/socket.h:39, v6.18.46), and `SOCK_NONBLOCK`, which
alpha and parisc set to 0x40000000 (arch/alpha/include/asm/socket.h:10,
arch/parisc/include/asm/socket.h:10, v6.18.46) through net.h:81's
`#ifndef SOCK_NONBLOCK`.  sparc overrides neither. -/
def SOCK_CLOEXEC : Int := 524288

/-- `#define SOCK_NONBLOCK O_NONBLOCK` (include/linux/net.h:82, Linux
v6.18.46, commit 1f99e9ab748f), the fallback under net.h:81's `#ifndef
SOCK_NONBLOCK`, which riscv64 takes because nothing in its headers
defines the name first (alpha and parisc do, in their asm/socket.h, as
`SOCK_CLOEXEC`'s docstring says); `O_NONBLOCK` is 00004000
(include/uapi/asm-generic/fcntl.h:38, Linux v6.18.46).  Rocq's `Sys/Uapi.v` comment on
this pair says net.h defines them only `#ifndef ARCH_HAS_SOCKET_TYPES`
and that mips and sparc override them, neither of which the headers do —
a `comments:` defect there. -/
def SOCK_NONBLOCK : Int := 2048

/-! ## Protocols (include/uapi/linux/in.h)

`IPPROTO_MAX` is the TRAILING ENUMERATOR of the `IPPROTO_*` enum, not a
round number: the last named member is `IPPROTO_MPTCP = 262` (line 88)
and `IPPROTO_MAX` follows it (line 90).  It was 256 only up to v5.5; `IPPROTO_MPTCP` arrived in v5.6.  Getting this wrong makes
protocols 256-262 answer -EINVAL where Linux answers -EPROTONOSUPPORT. -/

/-- `IPPROTO_IP = 0` (include/uapi/linux/in.h:30, Linux v6.18.46, commit
1f99e9ab748f). -/
def IPPROTO_IP : Int := 0

/-- `IPPROTO_TCP = 6` (include/uapi/linux/in.h:38, Linux v6.18.46, commit
1f99e9ab748f). -/
def IPPROTO_TCP : Int := 6

/-- `IPPROTO_SCTP = 132` (include/uapi/linux/in.h:74, Linux v6.18.46,
commit 1f99e9ab748f). -/
def IPPROTO_SCTP : Int := 132

/-- `IPPROTO_MPTCP = 262` (include/uapi/linux/in.h:88, Linux v6.18.46,
commit 1f99e9ab748f). -/
def IPPROTO_MPTCP : Int := 262

/-- `IPPROTO_MAX`, the enumerator after `IPPROTO_MPTCP`
(include/uapi/linux/in.h:90, Linux v6.18.46, commit 1f99e9ab748f). -/
def IPPROTO_MAX : Int := 263

/-! ## The three address lengths the socket calls test, in the order the
kernel applies them.  The middle one is connect's alone: bind reaches
`inet_bind_sk` directly and never tests it, and a 4-byte address passes
it and is then refused by the third. -/

/-- `sizeof(struct __kernel_sockaddr_storage)`: `#define _K_SS_MAXSIZE 128`
(include/uapi/linux/socket.h:8, Linux v6.18.46, commit 1f99e9ab748f) —
the largest address `move_addr_to_kernel` (net/socket.c) will copy. -/
def SOCKADDR_STORAGE_SIZE : Int := 128

/-- `sizeof(sa_family_t)`, an `unsigned short` (`__kernel_sa_family_t`,
include/uapi/linux/socket.h) — `__inet_stream_connect`'s
`addr_len < sizeof(uaddr->sa_family)` (net/ipv4/af_inet.c), which
precedes its state switch. -/
def SA_FAMILY_SIZE : Int := 2

/-- `sizeof(struct sockaddr_in)`: padded to `__SOCK_SIZE__`, which is
`#define __SOCK_SIZE__ 16` (include/uapi/linux/in.h:259-268, Linux
v6.18.46, commit 1f99e9ab748f) — the smallest `inet_bind_sk` accepts and
the one `tcp_v4_connect` applies AFTER the state switch. -/
def SOCKADDR_IN_SIZE : Int := 16

/-! ## Option levels and shutdown

`SOL_SOCKET` is the odd one out: not an `IPPROTO_*` value but a constant
of its own.  The other two levels an AF_INET/SOCK_STREAM socket has a
handler for are `IPPROTO_IP` and `IPPROTO_TCP` above — SOL_IP and SOL_TCP
are the SAME NUMBERS (0 and 6) under other names (include/uapi/linux/in.h),
so they are not defined again; `Net.Socket.sock_level_known` names them
as the levels.

`SHUT_RD`/`SHUT_WR`/`SHUT_RDWR` are the members of the unnumbered
`enum sock_shutdown_cmd` (include/linux/net.h:92-96, Linux v6.18.46),
declared in that order with no initialisers, hence 0/1/2.  They are NOT
the `RCV_SHUTDOWN`/`SEND_SHUTDOWN` bits of include/net/sock.h (1/2/3,
with `SHUTDOWN_MASK = 3`) — `inet_shutdown` (net/ipv4/af_inet.c) converts
between the two with a `how++`, and mistaking one set for the other is
exactly how a model gets `shutdown`'s validation backwards. -/

/-- `#define SOL_SOCKET 1` (include/uapi/asm-generic/socket.h:9, Linux
v6.18.46, commit 1f99e9ab748f), which riscv64 uses unchanged. -/
def SOL_SOCKET : Int := 1

/-- `SHUT_RD`, first member of `enum sock_shutdown_cmd`
(include/linux/net.h:93, Linux v6.18.46, commit 1f99e9ab748f). -/
def SHUT_RD : Int := 0

/-- `SHUT_WR` (include/linux/net.h:94, Linux v6.18.46, commit
1f99e9ab748f). -/
def SHUT_WR : Int := 1

/-- `SHUT_RDWR` (include/linux/net.h:95, Linux v6.18.46, commit
1f99e9ab748f). -/
def SHUT_RDWR : Int := 2

/-- `MSG_CMSG_COMPAT`.  Its VALUE depends on the kernel's configuration:
`#define MSG_CMSG_COMPAT 0x80000000` under CONFIG_COMPAT and
`#define MSG_CMSG_COMPAT 0` without it (include/linux/socket.h:337-341,
Linux v6.18.46, commit 1f99e9ab748f), and the two give different answers
for the same call — see `Net.Socket.recvmsg_spec`.  This is the
CONFIG_COMPAT value. -/
def MSG_CMSG_COMPAT : Int := 2147483648

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
