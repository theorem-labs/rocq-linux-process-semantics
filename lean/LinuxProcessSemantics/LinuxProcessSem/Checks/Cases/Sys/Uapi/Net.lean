import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # Checks.Cases.Sys.Uapi.Net — the `Sys.Uapi.Net` constants, read off
against Linux

Pins over `Sys/Uapi/Net.lean`, the socket constants. Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about a header or a function of
Linux v6.18.46, commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, with the
citation beside it.

Each pin states a value the kernel really has and, beside it, refutes the
concrete mistake the constant exists to prevent — a value from another
architecture's header, an off-by-one at a bound, a decimal read of an
octal, a mask taken for its neighbour.  They are stated about the cited
headers and sources, never about the Rocq definitions of the same names.
No Rocq file sits at this file's mirror path: the Rocq tree keeps its
Uapi constants unpinned (this stops being true the day a Rocq case
file pins them), so this file is the Lean port's own evidence rather
than a twin. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Net

open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `AF_MAX` is one PAST the last named family: `#define AF_MCTP 45` and
`#define AF_MAX 46` (include/linux/socket.h:240 and :244, Linux v6.18.46,
commit 1f99e9ab748f).  A bound at the last name would refuse family 45
where `__sock_create` (net/socket.c) consults the registered table. -/
theorem families : AF_UNSPEC = 0 ∧ AF_INET = 2 ∧ NPROTO = 45 + 1 ∧ NPROTO ≠ 45 := by decide

/-- `enum sock_type` (include/linux/net.h:64-70, Linux v6.18.46) and its two
derived macros (lines 74 and 77).  `SOCK_MAX` is `SOCK_PACKET + 1`, not
`SOCK_PACKET`; and both flag bits are OUTSIDE `SOCK_TYPE_MASK`, so the
`type &= SOCK_TYPE_MASK` that `__sys_socket` reaches through
`__sys_socket_create` (net/socket.c:1699, Linux v6.18.46, commit
1f99e9ab748f, after the `BUILD_BUG_ON`s at :1694-1695 assert exactly this
disjointness) never sees them. -/
theorem socket_types :
    SOCK_STREAM = 1 ∧ SOCK_DGRAM = 2 ∧ SOCK_RAW = 3 ∧ SOCK_SEQPACKET = 5 ∧ SOCK_DCCP = 6
    ∧ SOCK_PACKET = 10 ∧ SOCK_MAX = SOCK_PACKET + 1 ∧ SOCK_TYPE_MASK = 0xf
    ∧ SOCK_MAX ≠ SOCK_PACKET
    ∧ (SOCK_CLOEXEC.toNat &&& SOCK_TYPE_MASK.toNat : Nat) = 0
    ∧ (SOCK_NONBLOCK.toNat &&& SOCK_TYPE_MASK.toNat : Nat) = 0 := by decide

/-- `IPPROTO_MAX` is the enumerator after `IPPROTO_MPTCP = 262`
(include/uapi/linux/in.h:88-90), 263 — not the 256 it was through v5.5.
With 256, protocols 256-262 would answer -EINVAL where Linux answers
-EPROTONOSUPPORT. -/
theorem protocols :
    IPPROTO_IP = 0 ∧ IPPROTO_TCP = 6 ∧ IPPROTO_SCTP = 132 ∧ IPPROTO_MPTCP = 262
    ∧ IPPROTO_MAX = IPPROTO_MPTCP + 1 ∧ IPPROTO_MAX ≠ 256 := by decide

/-- The three address lengths: `_K_SS_MAXSIZE` 128 (include/uapi/linux/socket.h:8,
Linux v6.18.46), `sizeof(unsigned short)` 2 for `sa_family_t`, and
`__SOCK_SIZE__` 16 for `struct sockaddr_in` (include/uapi/linux/in.h:259,
Linux v6.18.46).  `sa_family_t` is not an
`int`, and `sockaddr_in` is not the 28-byte `sockaddr_in6`: connect's
`addr_len < sizeof(uaddr->sa_family)` test admits a 2-byte address, and
`inet_bind_sk` refuses one shorter than 16. -/
theorem address_lengths :
    SOCKADDR_STORAGE_SIZE = 128 ∧ SA_FAMILY_SIZE = 2 ∧ SOCKADDR_IN_SIZE = 16
    ∧ SA_FAMILY_SIZE ≠ 4 ∧ SOCKADDR_IN_SIZE ≠ 28 := by decide

/-- `SOL_SOCKET` is 1 (include/uapi/asm-generic/socket.h:9, Linux v6.18.46) and
is a level of its own, not `SOL_IP` (0) or `SOL_TCP` (6). -/
theorem option_levels :
    SOL_SOCKET = 1 ∧ SOL_SOCKET ≠ IPPROTO_IP ∧ SOL_SOCKET ≠ IPPROTO_TCP := by decide

/-- `shutdown`'s `how` is the unnumbered `enum sock_shutdown_cmd`
(include/linux/net.h:92-96, Linux v6.18.46), 0/1/2 — NOT the `RCV_SHUTDOWN`
/ `SEND_SHUTDOWN` / `SHUTDOWN_MASK` bits of include/net/sock.h:1491-1493
(Linux v6.18.46), 1/2/3, which `inet_shutdown` (net/ipv4/af_inet.c, Linux
v6.18.46) reaches by `how++`.
Taking the bits for the commands makes `shutdown(fd, 0)` an -EINVAL and
`shutdown(fd, 3)` valid, both backwards. -/
theorem shutdown_words :
    SHUT_RD = 0 ∧ SHUT_WR = 1 ∧ SHUT_RDWR = 2
    ∧ SHUT_RD + 1 = 1 ∧ SHUT_WR + 1 = 2 ∧ SHUT_RDWR + 1 = 3
    ∧ SHUT_RD ≠ 1 ∧ SHUT_WR ≠ 2 ∧ SHUT_RDWR ≠ 3 := by decide

/-- `MSG_CMSG_COMPAT` is bit 31 under CONFIG_COMPAT (include/linux/socket.h:338,
Linux v6.18.46) and 0 without it (line 340); this constant is the compat kernel's, and a
spec reading it must say so. -/
theorem MSG_CMSG_COMPAT_is_the_compat_value :
    MSG_CMSG_COMPAT = 2 ^ 31 ∧ MSG_CMSG_COMPAT ≠ 0 := by decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Net
