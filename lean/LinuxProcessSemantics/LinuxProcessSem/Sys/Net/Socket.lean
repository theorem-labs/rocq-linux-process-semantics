import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
drift-ticket: socket_spec R-Net-Socket-rebase -- T142 declines protocols 256-262; T149 restores pre-protocol ENFILE alternatives; T172 declines unknown type-flag bits; T172 step 2 declines AF_NETLINK's type range outside protocols 9 and 15; T172 step 2 also declines families 44 and 45 in the type range
drift-ticket: socketpair_spec R-Net-Socket-rebase -- T172 declines unknown type-flag bits in both trees
drift-ticket: load_write_free S-Net-Socket-io -- T172 declines writable LOAD bytes whose read permission is unavailable
drift-ticket: sendmsg_load_free S-Net-Socket-io -- T172 checks pre-host locks for writable LOAD bytes
drift-ticket: seg_lockable S-Net-Socket-io -- #1636 declines the send shapes qemu-user answers differently; baseline moves after #1636 lands
drift-ticket: iov_inval_at_head S-Net-Socket-io -- #1636 declines the send shapes qemu-user answers differently; baseline moves after #1636 lands
drift-ticket: iovs_lockable S-Net-Socket-io -- #1636 declines the send shapes qemu-user answers differently; baseline moves after #1636 lands
drift-ticket: sendmsg_prehost_quiet S-Net-Socket-io -- #1636 declines the send shapes qemu-user answers differently; baseline moves after #1636 lands
drift-ticket: iov_fault_at_head S-Net-Socket-io -- #1636 declines the send shapes qemu-user answers differently; baseline moves after #1636 lands
drift-ticket: sendto_spec S-Net-Socket-io -- #1636 declines the send shapes qemu-user answers differently; baseline moves after #1636 lands
drift-ticket: sendmsg_spec S-Net-Socket-io -- #1636 declines the send shapes qemu-user answers differently; baseline moves after #1636 lands
drift-ticket: accept_notsock_errnos S-Net-Socket-socket-accept -- T149 retains EMFILE below the embedded fd-table floor; baseline moves after T149 lands
drift-ticket: accept_notlisten_errnos S-Net-Socket-socket-accept -- T149 names errors preceding non-listening EINVAL; baseline moves after T149 lands
drift-ticket: accept4_spec R-Net-Socket-rebase -- T149 restores allocation alternatives and declines implementation-dependent ordering; baseline moves after T149 lands
drift-ticket: IPPROTO_MAX_PRE_V5_6 S-Net-Socket-socket-accept -- added in both trees by T142; the baseline moves once T142 lands -/

/-! # LinuxProcessSem.Sys.Net.Socket — socket (198), socketpair (199), bind (200),
listen (201), accept (202), connect (203), getsockname (204), getpeername (205),
sendto (206), recvfrom (207), setsockopt (208), getsockopt (209), shutdown (210),
sendmsg (211), recvmsg (212), accept4 (242)

Mirrors `theories/LinuxProcessSem/Sys/Net/Socket.v`, which answers to Linux
`net/socket.c, v6.18.46`: it holds what the kernel defines there, and nothing else.
The Rocq file was ported by four tickets — the socket LIFECYCLE arms
(S-Net-Socket-lifecycle), the two OPTION calls (S-Net-Socket-options),
CREATION and ACCEPTANCE (S-Net-Socket-socket-accept, held back until the
descriptor allocator existed; below), and the SEND and RECEIVE arms
(S-Net-Socket-io) — and this twin now holds every definition of it.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Net/Socket.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq still pins most of these arms to "v6.12" line numbers (its
descriptor-gate comment names `sockfd_lookup_light` only as the spelling
before v6.13); every line here was read at v6.18.46, where each `__sys_*`
entry point opens with `CLASS(fd, f)(fd)` and `fd_empty`, with the same
two answers.

THE BASELINE is a71fd38a, the squash of the 2026-09-11 work on main (its
tree is fc3d97ec's, the 09-11 head), which every twin names since the day
branch was rebased onto main.  It includes #712, which gave `FdEntry` its
`FdUrandom` constructor and added the matching -ENOTSOCK arm to Rocq's
`sock_fd`, so the Lean `FdEntry` has the constructor and the arm below has
to exist for the match to be total.  The lifecycle arms were written
against c2de0991's Socket.v, which differs from the baseline's only in two
citation comments (`inet_hash` at net/ipv4/inet_hashtables.c:796-797,
Linux v6.18.46, in place of `__inet_hash`, and `__sys_recvfrom`'s
descriptor gate in place of `sockfd_lookup_light`); no definition differs.
The option arms — `sock_level_known`, `int32_neg`, `setsockopt_spec`,
`getsockopt_optlen_read` and `getsockopt_spec` — and the send and receive
arms were written against the baseline itself.

FDFILERW AND FDFILEA DECLINE HERE, beyond Rocq, in `sendmsg_spec` alone.
`sendmsg_spec` answers `unmodeled` on a read-write or an append-mode file,
where Rocq's arm answers -ENOTSOCK as for `FdFile`.  The base change that
added the two constructors ported Rocq's arm into every pure helper that
names either and declined both in every spec arm that does, so that each arm
is ported later against pins of its own; `Checks/Cases/Net/Socket.lean`'s
`a17_rdwr_sendmsg_declines` and `a17_append_sendmsg_declines` hold the
declines.  `sock_fd` and `sockfd_lookup_errno` are pure helpers and answer
both kinds -ENOTSOCK, as Rocq's do.  No run an example can reach is
narrowed: none can hold either kind yet (`State/Fd.lean`'s constructor notes
say why, and when that stops being true).

Spellings that differ from Rocq without changing a value:

- bit tests on a flag word are done on the `word` (`bv_and`, `bv_not`,
  `bv_or`) where Rocq does them on `bv_unsigned` in `Z` (`Z.land`,
  `Z.ldiff`, `Z.lor`); the constants are below `2^64`, so the two agree;
- Rocq's `Z.eqb`, `Z.leb` and `Z.ltb` Bool tests are Lean's decidable `=`,
  `≤` and `<` on `Int`;
- Rocq's `NetStream` is an inductive with constructors `NCons`, `NFin`,
  `NRst` and `NTimedOut`, and `bind_spec` matches on them; the Lean
  `NetStream` is a cell function (`State.lean`), so a script's head is
  read as `rx.cell_at 0`, exactly as `State.NetStream.uncons` and
  `State.net_ended` do; `send_state` reads it so, and `bind_spec`'s
  connected arm does not split on it at all (the declines below);
- Rocq keeps unused names in scope with `let _ := x in` — `addrlenp` in
  `accept4_spec`, `namelen` and `ctl` in
  `sendmsg_spec`; Lean has no such idiom, so the twin keeps a parameter
  under `set_option linter.unusedVariables false in`
  (`send_on_socket`'s unread ones included) and does not decode a header
  field it never reads, and `recvfrom_spec` does not bind the input Rocq
  binds and never reads;
- Rocq's `sendmsg_spec` reads the six header fields with `read_u64` after
  the whole-header read, which needs a seventh, unreachable arm to make
  the match total; the twin decodes them from the 56 bytes that read
  returned, the same bytes in the same order.

WHERE THIS TWIN ANSWERS DIFFERENTLY FROM ROCQ, each argued where it
happens:

- `bind_spec`'s connected arm declines every head where Rocq answers
  -EINVAL for a byte or a FIN (its docstring, "THE STATE MATCH");
- `send_on_socket` declines both connected states, where Rocq delivers on
  a byte or a FIN and answers the pending error once on a reset or a
  timeout: the head of the script does not decide either (the send
  section's header), so only `SendDead`'s -EPIPE is kept;
- `sendmsg_spec` reads its header through `State.copy_bytes_map`, which
  asks `access_okb` first as `copy_from_user` does, where Rocq's
  `read_bytes_map` walks without a range test: the shape
  bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md records,
  whose enumeration has not ruled Rocq's `sendmsg_spec` in or out.  Both
  are argued on `sendmsg_spec`.

WHY `socket_spec` AND `accept4_spec` LANDED AFTER THE LIFECYCLE ARMS: both
allocate the new descriptor through `Fs.File.lowest_fd`, which ticket
S-Fs-File landed (#788) after the lifecycle arms had been written and
reviewed against a base without it, so the two arms were held back as the
ticket's follow-up rather than added to a reviewed diff; their helpers (`socket_errnos`,
`accept_errnos`, `conn_channel`, `conn_ix_exhausted`) were ported with the
lifecycle arms so that each of the two would land as one definition and
one table line.  Until #788 neither spec could have been written without
inventing a second descriptor allocator; the Rocq file has one, and so,
now, does this one. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File

/-! ## The errno sets the environment may draw from -/

/-- The errnos `socket` (198) can fail with for reasons the model does not
decide: the descriptor table filling up — `alloc_fd` answers -EMFILE past
the soft `RLIMIT_NOFILE` (fs/file.c:570, at :591, Linux v6.18.46,
commit 1f99e9ab748f) and `alloc_fdtable` answers -ENOMEM when the table
cannot grow (fs/file.c:162, at :242) — and the system file table
filling up, `__sock_create`'s -ENFILE when `sock_alloc` fails
(net/socket.c:1570-1575, v6.18.46, at :1573).  Drawn from with `errno_from` under an
`alt` so the failure stays LIVE.  The soft limit is carried by
`State.m_nofile` and still not consulted here, the gap
bugs/fd-allocation-ignores-rlimit-nofile.md records.  Argument on Rocq's
`Net.Socket.socket_errnos`; drawn from by `socket_spec` below. -/
def socket_errnos : List Int := [ENOMEM, EMFILE, ENFILE]

/-- The same three for `accept`/`accept4`: `get_unused_fd_flags` in
`__sys_accept4_file` (net/socket.c:2025-2027, Linux v6.18.46, commit
1f99e9ab748f) for -EMFILE and -ENOMEM, `sock_alloc` in `do_accept`
(net/socket.c:1966-1968) for -ENFILE.  Argument on Rocq's
`Net.Socket.accept_errnos`; drawn from by `accept4_spec` below. -/
def accept_errnos : List Int := [ENOMEM, EMFILE, ENFILE]

/-- Linux v6.18.46 net/socket.c `__sys_accept4_file` reserves the fd
before `do_accept` calls `sock_from_file`. Below `NR_OPEN_DEFAULT`,
fs/file.c `alloc_fd` needs no `expand_files` allocation, so that path's
ENOMEM is excluded. EMFILE remains possible because this arm does not
consult RLIMIT_NOFILE (v6.18.46, commit 1f99e9ab748f).
Linux v5.10 and v4.17 net/socket.c `__sys_accept4` check the socket before
fd allocation; QEMU 11.1.1 linux-user/syscall.c `do_accept4` with a NULL
address forwards to the host without allocating an address buffer. -/
def accept_notsock_errnos : List Int := [EMFILE]

/-- Linux net/socket.c `__sys_accept4` at v4.17 and `__sys_accept4_file`
at v5.10, v5.15, v6.1, v6.12 and v6.18.46 allocate before
net/ipv4/inet_connection_sock.c `inet_csk_accept` checks listening state.
`sock_alloc` and `sock_alloc_file` add ENFILE and ENOMEM. In particular
`sock_alloc_file` reaches fs/file_table.c `alloc_file_pseudo` /
`alloc_empty_file`, whose allocation can return ENOMEM even below
`NR_OPEN_DEFAULT` (v6.18.46). -/
def accept_notlisten_errnos : List Int := [EMFILE, ENOMEM, ENFILE]


/-- `bind` and `listen` both reach `inet_csk_get_port`
(net/ipv4/inet_connection_sock.c:500, Linux v6.18.46, commit
1f99e9ab748f), whose every failure — an exhausted
net.ipv4.ip_local_port_range, or a bind-bucket allocation failure — is
reported as -EADDRINUSE: the function initialises `ret = -EADDRINUSE`
(:506) and never overwrites it.  The model has no port table, so which of
the two happens is not something it can decide; the branch is kept live so
it can happen.  Argument on Rocq's `Net.Socket.bind_errnos`. -/
def bind_errnos : List Int := [EADDRINUSE]

/-- The autobind `listen` performs on an unbound socket is the same
`inet_csk_get_port` call (`inet_csk_listen_start`,
net/ipv4/inet_connection_sock.c:1345, at :1366, Linux v6.18.46,
commit 1f99e9ab748f), so the same single errno.  Argument on Rocq's
`Net.Socket.listen_errnos`. -/
def listen_errnos : List Int := [EADDRINUSE]

/-! ## The trace channel of an accepted connection -/

/-- THE TRACE CHANNEL OF THE `n`-TH CONNECTION HANDED OVER, which is
`3 + n`: past stdin, stdout and stderr, and never colliding with them or
with another connection.  NOT THE FD — the kernel reissues a closed
descriptor (`alloc_fd`, fs/file.c:570, Linux v6.18.46, commit
1f99e9ab748f, scans from the lowest free number), so after `close(1)` the
next accept would return fd 1 and a socket read would be reported on
stdout's channel.  NOT A COUNTER OF ALLOCATIONS EITHER: it counts
connections TAKEN FROM THE INPUT, so it is a function of the environment
and of how many connections the program has accepted.  Argument on Rocq's
`Net.Socket.conn_channel`. -/
def conn_channel (ix : word) : word := ix + Z_to_bv 64 3

/-- THE COUNTER IS EXHAUSTED once three values remain, because
`conn_channel` adds three and a `word` wraps: the last index that does not
wrap is `2^64 - 4`, reported on `2^64 - 1`; at `2^64 - 3` the next channel
would be 0, stdin's.  Nothing reaches this in a run anyone will execute —
it takes `2^64` successful accepts — but `State.with_accepted` increments
unconditionally and the run relation admits chains of any finite length,
so without the guard the channel separation is FALSE at a reachable
configuration rather than merely unreached
(bugs/socket-conn-channel-wraps-at-2-64.md).  Argument on Rocq's
`Net.Socket.conn_ix_exhausted`.  Rocq: `two_pow_64 - 3 <=? bv_unsigned ix`. -/
def conn_ix_exhausted (ix : word) : Bool :=
  two_pow_64 - 3 ≤ bv_unsigned ix

/-! ## `struct sockaddr_in`, decoded from the bytes the guest supplied

The layout is `struct sockaddr_in` of include/uapi/linux/in.h (Linux
v6.18.46, commit 1f99e9ab748f): `sin_family` at offset 0, `sin_port` at
2, `sin_addr` at 4, padded to 16 by `sin_zero`.  Three readers, each
answering -1 on a list too short to hold its field, so a short address can
never look like a well-formed one. -/

/-- `sin_family`: a `sa_family_t`, i.e. an `unsigned short` in HOST byte
order, at offset 0.  riscv64 is little-endian.  Rocq:
`Net.Socket.sa_family_of`. -/
def sa_family_of (bs : List byte) : Int :=
  match bs with
  | b0 :: b1 :: _ => bv_unsigned b0 + 256 * bv_unsigned b1
  | _ => -1

/-- `sin_port`: a `__be16` at offset 2 — NETWORK byte order, so the
high-order byte comes first.  Rocq: `Net.Socket.sin_port_of`. -/
def sin_port_of (bs : List byte) : Int :=
  match bs with
  | _ :: _ :: b2 :: b3 :: _ => 256 * bv_unsigned b2 + bv_unsigned b3
  | _ => -1

/-- `sin_addr.s_addr`: a `__be32` at offset 4 — network byte order.  Rocq:
`Net.Socket.sin_addr_of`. -/
def sin_addr_of (bs : List byte) : Int :=
  match bs with
  | _ :: _ :: _ :: _ :: b4 :: b5 :: b6 :: b7 :: _ =>
      16777216 * bv_unsigned b4 + 65536 * bv_unsigned b5
        + 256 * bv_unsigned b6 + bv_unsigned b7
  | _ => -1

/-- `#define INADDR_ANY ((unsigned long int) 0x00000000)`
(include/uapi/linux/in.h:307, Linux v6.18.46, commit 1f99e9ab748f): the
only bind address the model accepts. -/
def INADDR_ANY : Int := 0

/-- `IPPROTO_SMC = 256` (include/uapi/linux/in.h:86, Linux v6.18.46, commit
1f99e9ab748f): the protocol `smc_inet_protosw` registers under
`SOCK_STREAM` (net/smc/smc_inet.c:54-56, at :130, v6.18.46). -/
def IPPROTO_SMC : Int := 256

/-- `IPPROTO_MAX` as Linux v4.17 through v5.5 define it: 256, the enumerator
after `IPPROTO_RAW = 255` (include/uapi/linux/in.h:77-79 at v4.17, and the
same lines at v5.5).  v5.6 inserts `IPPROTO_MPTCP = 262` ahead of it
(include/uapi/linux/in.h:81-83, v5.6), which is where `IPPROTO_MAX`'s 263
comes from.  `inet_create`'s `protocol >= IPPROTO_MAX` -EINVAL reads the
same at all three (net/ipv4/af_inet.c:257-258 at v4.17, :258-259 at v5.5
and v5.6).  After socket allocation, `inet_create` returns -EINVAL
for a protocol in `[IPPROTO_MAX_PRE_V5_6, IPPROTO_MAX)` on the older
supported kernels and reaches the `inetsw` walk on the newer ones. -/
def IPPROTO_MAX_PRE_V5_6 : Int := 256

/-! ## socket (198) -/

/-- `#define AF_NETLINK 16` (include/linux/socket.h:207, Linux v6.18.46,
commit 1f99e9ab748f).  Rocq's `socket_spec` writes it as the literal 16, so
that no Rocq definition is new since this twin's baseline. -/
def AF_NETLINK : Int := 16

/-- `#define AF_MAX 44` (include/linux/socket.h:211, Linux v4.17), the lowest family bound of a
supported kernel: v4.18 adds AF_XDP (44) and v5.15 AF_MCTP (45).  Rocq's `socket_spec` writes it as the
literal 44, so that no Rocq definition is new since this twin's baseline. -/
def AF_MAX_V4_17 : Int := 44

/-- `#define NETLINK_AUDIT 9` (include/uapi/linux/netlink.h:18, Linux v6.18.46,
commit 1f99e9ab748f); a literal in Rocq, as `AF_NETLINK` is. -/
def NETLINK_AUDIT : Int := 9

/-- `#define NETLINK_KOBJECT_UEVENT 15` (include/uapi/linux/netlink.h:24,
Linux v6.18.46, commit 1f99e9ab748f); a literal in Rocq, as `AF_NETLINK` is. -/
def NETLINK_KOBJECT_UEVENT : Int := 15

/-- `socket domain type protocol`.

`SYSCALL_DEFINE3(socket)` (net/socket.c:1760, Linux v6.18.46, commit
1f99e9ab748f) is `__sys_socket` (:1743), which calls
`__sys_socket_create` (:1686), which calls `sock_create` (:1662) and so
`__sock_create` (:1535), which for `PF_INET` reaches
`inet_create` (net/ipv4/af_inet.c:254, v6.18.46).

Fd allocation comes LAST, unlike `openat`'s: `__sys_socket` finishes with
`sock_map_fd(sock, flags & (O_CLOEXEC | O_NONBLOCK))` (net/socket.c:1757, v6.18.46),
and `sock_map_fd` (:504) is where `get_unused_fd_flags` (:507, fs/file.c:620, v6.18.46)
runs.  The success-path alternatives remain: -EMFILE and -ENOMEM from `alloc_fd`
(fs/file.c:570, v6.18.46, at :591-593 and via `expand_files` :595-598) and -ENFILE
when `sock_alloc` (net/socket.c:632, v6.18.46) fails in `__sock_create`
(:1570-1575).  The new descriptor is
`Fs.File.lowest_fd`, the model's reading of `alloc_fd`'s lowest-free scan,
and the table gains the fd as `FdSocket SkFresh`: `inet_create` leaves
`sock->state = SS_UNCONNECTED` (net/ipv4/af_inet.c:268, v6.18.46) with no port bound.

Linux net/socket.c `__sock_create` at v4.17 and v6.18.46 calls
`sock_alloc` after family/type validation and before net/ipv4/af_inet.c
`inet_create`.  Its ENFILE joins the protocol-validation alternatives.
QEMU 11.1.1 linux-user/syscall.c `do_socket` has no AF_INET protocol
rejection before the host socket call.  Issue #1472 (T152) tracks the
LSM run configuration.

WHAT IS DECLINED, and why:
- An unknown type-flag bit: Linux v6.18.46 net/socket.c
  `__sys_socket_create` (:1697-1698) refuses it with -EINVAL before
  `sock_create`. QEMU 11.1.1 linux-user/syscall.c
  `target_to_host_sock_type` (:3183-3215) keeps the type nibble and the
  translated SOCK_CLOEXEC/SOCK_NONBLOCK bits, dropping the other bits;
  `do_socket` (:3233, host call :3257) calls the host with that word.
  On most of this class qemu-user's answer is the stripped word's answer.
  This does not imply disagreement on each input: socket(AF_INET, 0x10b, 0)
  gets -EINVAL from both after QEMU strips to type 11. The whole class is
  declined, including that agreement case (pinned by
  `t172_socket_agreeing_einval_declined`). The test stays FIRST because
  Linux tests the bit first: placing it after the family range would let
  -EAFNOSUPPORT through for socket(9999, SOCK_STREAM|0x100, 0), where Linux
  answers -EINVAL. The new decline costs coverage in the equivalence
  theorem's modeled conjunct; the examples do not construct these arguments.
- AF_NETLINK with type >= SOCK_MAX, except protocols 9 and 15: Linux v6.18.46
  net/socket.c `__sock_create` (:1547-1548) returns -EINVAL; QEMU 11.1.1
  linux-user/syscall.c `do_socket` (:3243-3249) returns -EPROTONOSUPPORT first
  (protocol 0 only without CONFIG_RTNETLINK). NETLINK_AUDIT (9) and
  NETLINK_KOBJECT_UEVENT (15) reach the host. This costs the equivalence theorem's
  modeled conjunct on these arguments; the examples do not construct them.
- Families 44 and 45 with type >= SOCK_MAX: AF_MAX is 44 in v4.17
  (include/linux/socket.h:211), 45 from v4.18 through v5.14 after AF_XDP
  (include/linux/socket.h:212 at v4.18, :227 at v5.14), and 46 from v5.15
  after AF_MCTP (include/linux/socket.h:226-230 at v5.15).
  The family check precedes the type check in net/socket.c `__sock_create`:
  v4.17:1224-1227 answers -EAFNOSUPPORT where v6.18.46:1545-1548 answers -EINVAL.
  This costs the equivalence theorem's modeled conjunct on these arguments;
  the examples do not construct them.
- `SOCK_NONBLOCK` in the flags sets `O_NONBLOCK` on the new file
  (`sock_map_fd`'s flags, net/socket.c:1757, v6.18.46 and :513), and the model has
  no notion of a non-blocking fd.  `SOCK_CLOEXEC` is accepted and ignored,
  as `openat_spec` does for `O_CLOEXEC`: it touches only the descriptor's
  close-on-exec bit, and there is no `execve` here.
- Every family but `AF_INET`: whether an in-range family is
  registered is a property of the kernel build, so neither success nor
  -EAFNOSUPPORT can be asserted.
- `SOCK_DGRAM`, `SOCK_RAW` and `SOCK_PACKET` under `AF_INET`.  The first
  two would SUCCEED (`inetsw_array`'s UDP and RAW entries, :1161-1183) and
  hand back a socket whose protocol this model does not have; the third is
  silently rewritten to `PF_PACKET` by `__sock_create` (net/socket.c:1555-1559, v6.18.46)
  before `inet_create` ever runs.  The protocol range is `inet_create`'s, and a
  rewritten call never reaches it — `packet_create`
  (net/packet/af_packet.c:3361, v6.18.46) casts the protocol to a `__be16` (:3366) and refuses only on
  `CAP_NET_RAW` (:3369-3370) — so judging `SOCK_PACKET` by `IPPROTO_MAX`
  would answer -EINVAL where Linux answers -EPERM or succeeds.
  `SOCK_DGRAM` and `SOCK_RAW` are not rewritten and so stay below it.
- `IPPROTO_SCTP` (include/uapi/linux/in.h:74, v6.18.46) and `IPPROTO_MPTCP` (:88)
  under `SOCK_STREAM`, and the types `SOCK_SEQPACKET` and `SOCK_DCCP`:
  SCTP registers `sctp_stream_protosw` and `sctp_seqpacket_protosw`
  (net/sctp/protocol.c:1162-1169, v6.18.46, at :1285-1286) and MPTCP
  `mptcp_protosw` (net/mptcp/protocol.c:4198-4201, v6.18.46, at :4271) when built,
  through `inet_register_protosw` (net/ipv4/af_inet.c:1188, which appends
  past the permanent entries, :1201-1218), so whether the walk answers
  success or -EPROTONOSUPPORT / -ESOCKTNOSUPPORT is again the build's.
  At v6.18.46 the tree has no `net/dccp` directory and no
  `inet_register_protosw` caller names `SOCK_DCCP`, so on this kernel
  type 6 falls through to -ESOCKTNOSUPPORT; the decline is Rocq's, made
  on account of the older supported kernels that shipped DCCP as a build
  option, and this twin keeps its shape — the cost is priority 3 on this
  kernel, never priority 1.
- `IPPROTO_SMC` (256,
  include/uapi/linux/in.h:86, v6.18.46) is `smc_inet_protosw`'s protocol
  under `SOCK_STREAM` (net/smc/smc_inet.c:54-56, registered at :130,
  v6.18.46), and `CONFIG_SMC` is a tristate (net/smc/Kconfig:2): built in,
  the walk finds the entry; built as a module, `inet_create`'s
  `request_module("net-pf-2-proto-256-type-1")` retry (net/ipv4/af_inet.c:292-302,
  v6.18.46) loads it through `MODULE_ALIAS_NET_PF_PROTO_TYPE(PF_INET, 256, 1)`
  (net/smc/af_smc.c:3683, v6.18.46) and the second walk finds it.  So a
  v6.18.46 with SMC answers `socket(AF_INET, SOCK_STREAM, 256)` with a
  descriptor where one without it answers -EPROTONOSUPPORT — the build's
  answer, exactly as 132 and 262 are.  256 and 262 fall in the next item's
  range, whose decline covers them.
- Protocols 256 through 262 under every type that reaches `inet_create`:
  after socket allocation, `inet_create` returns -EINVAL on v4.17
  through v5.5, where `IPPROTO_MAX` was 256 (`IPPROTO_MAX_PRE_V5_6`),
  and reaches the walk from v5.6 on.
- `update_socket_protocol` (net/socket.c:1736-1739, v6.18.46) is a `__weak` hook a
  BPF struct_ops program may override to rewrite the protocol; the modeled
  environment carries none, so the protocol is the argument's.

Argument on Rocq's `Net.Socket.socket_spec`.  Rocq does the flag tests on
`bv_unsigned (abi_low32 type)` in `Z`; this twin does them on the low
32 bits as a `word`, the file header's first spelling note. -/
def socket_spec (domain type protocol : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let tu := abi_low32 type
  let flagbits := bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK))
  if ¬ (bv_unsigned (bv_and flagbits
          (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0)
  then unmodeled
  else if ¬ (bv_unsigned (bv_and flagbits (Z_to_bv 64 SOCK_NONBLOCK)) = 0) then unmodeled
  else
    let ty : Int := bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK))
    let fam : Int := sint32 domain
    let pro : Int := sint32 protocol
    if fam < 0 ∨ NPROTO ≤ fam then err_ret EAFNOSUPPORT
    else if SOCK_MAX ≤ ty then
      if AF_MAX_V4_17 ≤ fam ∨ (fam = AF_NETLINK ∧ ¬ (pro = NETLINK_AUDIT ∨ pro = NETLINK_KOBJECT_UEVENT))
      then unmodeled else err_ret EINVAL
    else if ¬ (fam = AF_INET) then unmodeled
    else if ty = SOCK_PACKET then unmodeled              -- rewritten to PF_PACKET, before the protocol range
    else if pro < 0 ∨ IPPROTO_MAX ≤ pro then alt (err_ret EINVAL) (err_ret ENFILE)
    else if IPPROTO_MAX_PRE_V5_6 ≤ pro then unmodeled
    else if ty = SOCK_STREAM then
      if pro = IPPROTO_SCTP then unmodeled  -- registered when built
      else if ¬ (pro = IPPROTO_IP ∨ pro = IPPROTO_TCP) then alt (err_ret EPROTONOSUPPORT) (err_ret ENFILE)
      else alt (e <- errno_from socket_errnos ;; err_ret e)
               (fd <- lowest_fd (m_fds m) ;;
                set_fds (fd_insert (m_fds m) fd (.FdSocket .SkFresh)) ;;
                ret_only fd)
    else if ty = SOCK_DGRAM ∨ ty = SOCK_RAW then unmodeled          -- would succeed, unmodeled protocol
    else if ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP then unmodeled     -- SCTP and DCCP, when built
    else alt (err_ret ESOCKTNOSUPPORT) (err_ret ENFILE)

/-! ## bind (200) -/

/-- `bind fd addr addrlen`.

`__sys_bind` (net/socket.c:1889, Linux v6.18.46, commit 1f99e9ab748f)
fires its checks in this order, and the order is the spec's:

1. THE FD IS RESOLVED FIRST: `fd_empty` is -EBADF (:1896-1897), then
   `sock_from_file` is -ENOTSOCK for an open fd that is not a socket
   (:1898-1900; the test itself is the single comparison
   `file->f_op == &socket_file_ops`, net/socket.c:530-536, v6.18.46).  Nothing about
   the address is looked at before that verdict, which is the difference
   from `connect_spec` below.
2. `move_addr_to_kernel` (net/socket.c:248-257): `ulen < 0 || ulen >
   sizeof(struct sockaddr_storage)` (128) is -EINVAL (:250-251);
   `ulen == 0` copies NOTHING and returns 0 (:252-253), leaving the
   kernel's buffer untouched; otherwise a failed `copy_from_user` is
   -EFAULT (:254-255).  So -EFAULT PRECEDES the 16-byte minimum, and the
   copy-in ledger records the copy from here down and not above: the two
   range arms return before it, and the -EFAULT arm is the copy FAILING,
   which transfers nothing.
3. `inet_bind_sk` (net/ipv4/af_inet.c:444, v6.18.46): `addr_len <
   sizeof(struct sockaddr_in)` (16) is -EINVAL (:453-454).  A zero
   `addrlen` lands here in Linux; the spec answers it one step earlier
   with the same errno and, as the kernel, no copy.
4. `__inet_bind` (net/ipv4/af_inet.c:473, v6.18.46): a `sin_family` other than
   AF_INET is -EAFNOSUPPORT (:484-491) — NOT -EINVAL — except that
   AF_UNSPEC with INADDR_ANY is accepted as AF_INET ("Compatibility
   games", :485-490).  Then -EADDRNOTAVAIL (:504-507), then -EACCES for a
   privileged port (:510-514), then -EINVAL for a socket that is not
   TCP_CLOSE or already has a port (`sk->sk_state != TCP_CLOSE ||
   inet->inet_num`, :527-529), then `get_port` (:538-541), whose every
   failure is `bind_errnos`.

WHAT IS DECLINED.  Only INADDR_ANY on port 0 is accepted: a specific
address needs the local address table behind -EADDRNOTAVAIL, a specific
port the port table behind -EADDRINUSE and the sysctl behind -EACCES
(`inet_port_requires_bind_service`, include/net/ip.h, v6.18.46, reads
net.ipv4.ip_unprivileged_port_start), none of which a one-process model
has.  EVEN PORT 0 CAN FAIL: with `snum == 0` and no
`IP_BIND_ADDRESS_NO_PORT`, `__inet_bind` still calls `get_port` (:538),
which is why the errno branch on the fresh arm is live.

THE STATE MATCH.  A fresh socket binds; a bound or listening one is
-EINVAL (:528: a bound socket has a port, a listener is TCP_LISTEN).  Every
CONNECTED socket is declined, whatever its script's head; the reset case
comes first because the others reduce to it.  A connection
the peer has RESET is declined rather than answered -EINVAL, because it is
UNBOUND AGAIN on Linux: `tcp_done` (net/ipv4/tcp.c:5020, v6.18.46) runs `tcp_set_state(sk,
TCP_CLOSE)` (:5033), whose TCP_CLOSE arm calls `inet_put_port` whenever
`icsk_bind_hash && !(sk_userlocks & SOCK_BINDPORT_LOCK)` (net/ipv4/tcp.c:
2993-3001); `sk_clone_lock` (net/core/sock.c:2464, v6.18.46) clears that bit on
EVERY accepted child (:2515), so the guard never saves it; and
`__inet_put_port` (net/ipv4/inet_hashtables.c:212) stores
`inet_num = 0` (:227).  Both conjuncts of :528 are then false and Linux
AUTOBINDS and returns 0 — and the reset arrives when the SEGMENT does, not
when the program reads it: `tcp_validate_incoming` resets on an in-order
RST the moment it arrives (net/ipv4/tcp_input.c:6183-6193, v6.18.46),
`tcp_reset` (:4678) purges the WRITE queue only, through
`tcp_done_with_error` (:4663), and
`tcp_recvmsg_locked` hands the queued bytes out before it reports the error
(net/ipv4/tcp.c:2703, ahead of :2744).  So a script whose head is a BYTE may
already sit on an unbound socket exactly as one whose head is the reset
does; the model sees the head cell and not the tail, and a timeout takes
the same path (`tcp_write_err`, net/ipv4/tcp_timer.c:78, v6.18.46, into
`tcp_done`).
A FIN-headed script is declined too.  A FIN moves no port, so a CLOSE_WAIT
connection still has one and :528 would answer -EINVAL — but a reset can
sit BEHIND the FIN exactly as behind a byte: a peer whose FIN came from a
full `close` answers a RST to anything the program writes afterwards (its
`tcp_rcv_state_process` FIN_WAIT_2 arm resets on data once RCV_SHUTDOWN is
set; a peer that only `shutdown(SHUT_WR)` keeps reading), or sends one
when it closes with unread data, and `tcp_rcv_state_process` runs
`tcp_validate_incoming` in CLOSE_WAIT as well (net/ipv4/tcp_input.c:7019,
v6.18.46), so `tcp_reset` (:4678; err EPIPE in that state) has run
`tcp_done` and put the port back before the program's next call.  Reading
cannot tell the two sockets apart: `tcp_fin` set SOCK_DONE (:4727), and
`tcp_recvmsg_locked` tests SOCK_DONE (net/ipv4/tcp.c:2741, v6.18.46) before
`sk_err` (:2744), so the read answers 0 either way — while
`bind(INADDR_ANY:0)` answers -EINVAL on the CLOSE_WAIT socket and 0 (or
-EADDRINUSE) on the one the reset already unbound.  The model holds the FIN
cell and nothing after it, so it cannot express the difference; a certain
-EINVAL would assert an answer Linux does not always give, and a successful
bind would leave a socket that is bound and still reads as end-of-stream,
which `State.SockState` cannot express either.  Rocq's `bind_spec` answers -EINVAL for
`NCons _ _` and for the FIN, on the argument that a live or half-closed
connection has a port, which does not survive a reset queued behind the
cell it reads — the same fact its own `NRst` arm concedes.  Rocq owes the
matching change; `Checks/Cases/Net/Socket.lean`'s
`bind_byte_then_reset_declines` and `bind_half_closed_connection_declines`
carry the kernel reading.

A NARROWING, reaching one of the two length checks and not both:
`__sys_bind` runs `move_addr_to_kernel` (:1902) and only then
`__sys_bind_socket` (:1906), whose first statement is
`security_socket_bind` (:1872) — so step 2's range test PRECEDES the LSM
while step 3's 16-byte minimum FOLLOWS it.  An LSM can answer -EACCES
where this spec answers step 3's -EINVAL. Issue #1472 (T152) owns
the declared LSM run configuration. -/
def bind_spec (fd addrp addrlen : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF                  -- fd not open: real -EBADF, before the address
  | some (.FdSocket sk) =>
      (let al := sint32 addrlen
       if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then err_ret EINVAL
       else if al = 0 then err_ret EINVAL   -- nothing copied, nothing faults; inet_bind_sk refuses it
       else
       match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
       | none => err_ret EFAULT             -- copy_from_user failed: real -EFAULT, nothing transferred
       | some bs =>
           record_copyins [(addrp, al.toNat)]
             (if al < SOCKADDR_IN_SIZE then err_ret EINVAL
              else
                let fam := sa_family_of bs
                let port := sin_port_of bs
                let a := sin_addr_of bs
                if ¬ (fam = AF_INET ∨ (fam = AF_UNSPEC ∧ a = INADDR_ANY))
                then err_ret EAFNOSUPPORT    -- NOT -EINVAL; see above
                else if ¬ (a = INADDR_ANY) then unmodeled
                else if ¬ (port = 0) then unmodeled
                else
                  match sk with
                  | .SkFresh =>
                      alt (e <- errno_from bind_errnos ;; err_ret e)
                          (set_fds (fd_insert (m_fds m) fd (.FdSocket .SkBound)) ;;
                           ret_only (Z_to_bv 64 0))
                  | .SkBound | .SkListening => err_ret EINVAL
                  | .SkReset _ _ => unmodeled  -- unbound again by tcp_done: see above
                  | .SkConnected _ _ _ => unmodeled))
                      -- a reset or timeout the kernel has ALREADY processed may sit
                      -- behind the head cell, byte or FIN, or be the head: see above
  | some _ => err_ret ENOTSOCK
      -- AN OPEN FD THAT IS NOT A SOCKET, whatever kind it is: `sock_from_file`
      -- is one comparison against `socket_file_ops` (net/socket.c:530-536, v6.18.46),
      -- so -ENOTSOCK is a property of the kernel's dispatch rather than of
      -- any enumeration of file kinds, and this arm stays correct as
      -- `FdEntry` grows.  Argument on Rocq's `Net.Socket.bind_spec`.

/-! ## listen (201) -/

set_option linter.unusedVariables false in
/-- `listen fd backlog`.

`__sys_listen` (net/socket.c:1933, Linux v6.18.46, commit
1f99e9ab748f) resolves the fd first — `fd_empty` is -EBADF (:1938-1939),
`sock_from_file` is -ENOTSOCK (:1940-1942) — and only then
`__sys_listen_socket` (net/socket.c:1919) clamps the backlog:
`if ((unsigned int)backlog > somaxconn) backlog = somaxconn;`
(:1923-1925).  THE BACKLOG IS NEVER REJECTED, only clamped; the cast is
what makes a negative backlog a huge unsigned clamped down rather than
refused.  Nothing in this model observes the backlog, so the argument is
unused here.

`inet_listen` (net/ipv4/af_inet.c:232, v6.18.46) refuses a socket that is not
`SS_UNCONNECTED` or not `SOCK_STREAM` with -EINVAL (:239-240), then
`__inet_listen_sk` (:193-227) accepts exactly the states in `TCPF_CLOSE |
TCPF_LISTEN` (:198-199) — so RE-LISTENING IS LEGAL: a second listen writes
the new backlog (:201) and skips `inet_csk_listen_start` (:220-222),
returning 0.  LISTEN WITHOUT BIND SUCCEEDS: `inet_csk_listen_start`
(net/ipv4/inet_connection_sock.c:1345, v6.18.46) calls `get_port(sk,
inet->inet_num)` with `inet_num == 0` (:1366) and autobinds an ephemeral
port; that autobind is the only thing that can fail on the modeled surface
(`listen_errnos`), so the errno branch is live on the FRESH arm alone — a
socket that is already bound has a port, and `get_port` cannot fail for
it.  (`inet_csk_listen_start`'s other two exits, `inet_ulp_can_listen` at
:1351 and the reuseport hash at :1371, need a `setsockopt` this model
answers `unmodeled`, so no modeled run reaches them; the argument is on
Rocq's `Net.Socket.listen_spec`.)

A CONNECTED SOCKET IS -EINVAL from :239 (`sock->state` is
`SS_CONNECTED`), and so is a RESET one, but not for the reason a reader
expects: `__inet_listen_sk`'s state mask (:198) would ACCEPT the TCP_CLOSE
that `tcp_done` (net/ipv4/tcp.c:5020, v6.18.46) left the socket in; what refuses
it is `inet_listen`'s earlier `sock->state != SS_UNCONNECTED` (:239),
because `tcp_done` moves `sk->sk_state` and never `sock->state`, which
only `inet_release` and `tcp_disconnect` move back.  The argument in full
is on Rocq's `Net.Socket.listen_spec`. -/
def listen_spec (fd backlog : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdSocket sk) =>
      (match sk with
       | .SkConnected _ _ _ => err_ret EINVAL      -- not SS_UNCONNECTED: real -EINVAL
       | .SkReset _ _ => err_ret EINVAL            -- still SS_CONNECTED: see above
       | .SkListening => ret_only (Z_to_bv 64 0)   -- re-listen: backlog only
       | .SkBound =>
           set_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) ;;
           ret_only (Z_to_bv 64 0)                 -- already has a port: get_port cannot fail
       | .SkFresh =>
           alt (e <- errno_from listen_errnos ;; err_ret e)   -- the autobind's -EADDRINUSE
               (set_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) ;;
                ret_only (Z_to_bv 64 0)))
  | some _ => err_ret ENOTSOCK

/-! ## connect (203) -/

/-- `connect fd addr addrlen`.

THE ORDER IS NOT BIND'S, and the difference is observable.  `__sys_connect`
(net/socket.c:2109, Linux v6.18.46, commit 1f99e9ab748f) resolves the
descriptor only far enough for -EBADF (`fd_empty`, :2115-2116), copies the
address (`move_addr_to_kernel`, :2118-2120), and reaches -ENOTSOCK only
inside `__sys_connect_file` (net/socket.c:2086, v6.18.46, at :2092-2096).  So
`connect(non_socket_fd, unreadable, 16)` is -EFAULT while the same `bind`
is -ENOTSOCK, and the copy-in ledger sits at exactly that seam: attached
BEFORE the -ENOTSOCK arm, because that is where the kernel performed it.
A zero length copies nothing (`move_addr_to_kernel`, :252-253) — the read
at length 0 is `some []` whatever the pointer, which is exactly "cannot
fault" — and records an empty ledger rather than a zero-length range.

Past the copy, `__inet_stream_connect` (net/ipv4/af_inet.c:626, v6.18.46):

3. `addr_len < sizeof(uaddr->sa_family)` (2) is -EINVAL (:643-644);
4. an AF_UNSPEC family is a DISCONNECT, not a connect, handled BEFORE the
   switch on `sock->state` (:646-651);
5. the switch (:654): `SS_CONNECTED` is -EISCONN (:658-660);
   `SS_UNCONNECTED` pre-loads -EISCONN and keeps it when `sk->sk_state !=
   TCP_CLOSE` (:668-671), then runs `tcp_v4_connect`
   (net/ipv4/tcp_ipv4.c:222, v6.18.46), whose first two tests are `addr_len <
   sizeof(struct sockaddr_in)` (16) -EINVAL (:236-237) and `sin_family !=
   AF_INET` -EAFNOSUPPORT (:239-240).

-EISCONN FOR A LISTENING SOCKET is the answer most worth getting right:
`listen` leaves `sock->state` at `SS_UNCONNECTED` (`inet_listen` refuses
anything else, net/ipv4/af_inet.c:239, v6.18.46) and moves only `sk->sk_state`, so
the `SS_UNCONNECTED` arm returns the -EISCONN it pre-loaded (:669-671).  An
ACCEPTED socket is -EISCONN from :658-660, since `__inet_accept` ends with
`newsock->state = SS_CONNECTED` (:769); a RESET one too, because `tcp_done`
(net/ipv4/tcp.c:5020, v6.18.46) moves `sk->sk_state` and not `sock->state`,
which is why this spec does not split on the script as `bind_spec` does.
A BOUND socket groups with the fresh one: `__inet_bind` never calls
`tcp_set_state`, so it is still TCP_CLOSE and reaches `tcp_v4_connect`.

THE CONNECTION ATTEMPT ITSELF IS DECLINED: once the address has passed on
a fresh or bound socket, `sk->sk_prot->connect` runs (:679) and the
outcome is the environment's — success, -ECONNREFUSED, -ETIMEDOUT,
-ENETUNREACH, … — and a successful connect would hand back a peer and a
byte stream whose only source here is the accept queue.  Not a `choose`
over that list, because it would have to include success.

AF_UNSPEC IS ANSWERED ONLY ON A FRESH SOCKET.  For TCP the `disconnect`
(:648) is `tcp_disconnect` (net/ipv4/tcp.c:3346, v6.18.46), which has one return
statement and it is `return 0` (:3489).  On a fresh socket every branch
inside it is dead — `old_state` is TCP_CLOSE, so no `inet_csk_listen_stop`
(:3359-3360), no RST (`tcp_need_reset`, :3306-3311, :3363-3365) — and it
leaves nothing this model can see: it advances `tp->write_seq` (:3396-3399),
which only a connect would read, and the connect is declined.  The other
four states are declined for a change `State.SockState` cannot express: a
bound socket's port bookkeeping (`inet_bhash2_reset_saddr`, :3388), a
listener's accept queue (:3360), a live connection's RST (:3363-3365), and
a reset connection's queue and port release.

NARROWINGS, all "fewer behaviours, never more": the LSM connect hook,
security_socket_connect, runs in `__sys_connect_file` (net/socket.c:2098-2101,
v6.18.46) between -ENOTSOCK and `ops->connect`, so an LSM can answer -EACCES where this spec answers anything past the copy; a
cgroup BPF program at `pre_connect` (net/ipv4/af_inet.c:673-677) can
preempt step 5's -EAFNOSUPPORT but not -EISCONN or the 16-byte -EINVAL,
which `tcp_v4_pre_connect` replicates (net/ipv4/tcp_ipv4.c:206-219, v6.18.46, at
:213-214); and the audit hook at the end of `move_addr_to_kernel` (net/socket.c:256,
v6.18.46) can answer -ENOMEM at any nonzero length.  The argument in full, with what would falsify each
unreachability claim, is on Rocq's `Net.Socket.connect_spec`. -/
def connect_spec (fd addrp addrlen : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF                   -- fd_empty, before the address is touched
  | some e =>
      let al := sint32 addrlen
      if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then err_ret EINVAL
      else
      match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
      | none => err_ret EFAULT              -- copy_from_user failed, BEFORE -ENOTSOCK
      | some bs =>
          record_copyins (if al = 0 then [] else [(addrp, bs.length)])
            (match e with
             | .FdSocket sk =>
                 (if al < SA_FAMILY_SIZE then err_ret EINVAL   -- __inet_stream_connect's first test
                  else if sa_family_of bs = AF_UNSPEC then
                    (match sk with
                     | .SkFresh => ret_only (Z_to_bv 64 0)     -- tcp_disconnect with nothing to disconnect
                     | .SkBound | .SkListening | .SkConnected _ _ _ | .SkReset _ _ => unmodeled)
                  else
                    (match sk with
                     | .SkListening | .SkConnected _ _ _ | .SkReset _ _ => err_ret EISCONN
                     | .SkFresh | .SkBound =>
                         if al < SOCKADDR_IN_SIZE then err_ret EINVAL
                         else if ¬ (sa_family_of bs = AF_INET) then err_ret EAFNOSUPPORT
                         else unmodeled))                      -- the attempt itself: the environment's
             | _ => err_ret ENOTSOCK)       -- sock_from_file, AFTER the copy

/-! ## accept (202) and accept4 (242) -/

set_option linter.unusedVariables false in
/-- `accept4 fd addr addrlen flags`, which `accept` reaches with
`flags = 0` — `SYSCALL_DEFINE3(accept)` (net/socket.c:2068, Linux v6.18.46,
commit 1f99e9ab748f) is literally `return __sys_accept4(fd, upeer_sockaddr,
upeer_addrlen, 0);` (:2071), so there is one spec and not two, and the
table's 202 arm passes a zero flags word.

At Linux v6.18.46, net/socket.c `__sys_accept4_file` reserves the fd
before `do_accept` converts the file to a socket.  At v5.10 the conversion
and `sock_alloc` precede reservation.  At v4.17, `__sys_accept4` performs
the flag check and lookup before `sock_alloc` and reservation.
The named errno lists account for these allocation failures.

THE ERRNO BRANCH IS LIVE, and that is not decoration.  Without it a source
that handles an accept failure and a target with that handling deleted
would have identical trace sets, while differing on real Linux.  It is
also what makes `accept` RECEPTIVE at fd exhaustion: `alloc_fd`'s scan is
bounded, and when it runs out `lowest_fd`'s freeness conjunct empties the
success branch, leaving this one.  An errno is an ordinary `Ok`, so an
errno-versus-success `alt` is not the shape that a `choose` between `Ok`
and `Unmodeled` would be.  For the same reason the exhausted-counter arm
is `choose (fun _ => False)` and not `unmodeled`: the `alt` sibling answers
a concrete errno at the same `(input, model)`, and the checker's totality
(`check_syscall_err_iff`) needs the success branch to be EMPTY there, not
declined — `conn_ix_exhausted`'s docstring says why the arm exists at all.

WHAT THE SUCCESS BRANCH DOES: the head connection of the environment's
queue is handed over on the lowest free fd as
`SkConnected (nq_peer net) (conn_channel ix) (nq_script net)`, and
`State.with_accepted` installs the table, pops the queue and advances the
channel counter.  The kernel side is `inet_csk_accept`'s
`reqsk_queue_remove` (:679) followed by `fd_install` (fs/file.c) in
`__sys_accept4_file` (net/socket.c:2035, v6.18.46).

WHAT IS DECLINED:
- `SOCK_NONBLOCK` in the flags — it marks the NEW file `O_NONBLOCK`:
  `__sys_accept4_file` passes `flags` to `do_accept` (:2029-2030), which
  hands them to `sock_alloc_file` (:1980), whose `alloc_file_pseudo` opens
  the file `O_RDWR | (flags & O_NONBLOCK)` (:483-485); the model has no
  such notion.  Note it does not affect whether this call blocks:
  `proto_accept_arg arg = { }` (:2015) carries no flag from the argument,
  and `do_accept` sets `arg->flags |= sock->file->f_flags` (:1988) from
  the LISTENING socket's own file before `ops->accept` reads
  `arg->flags & O_NONBLOCK`.  `SOCK_CLOEXEC` is accepted and ignored.
- A non-NULL address argument: the `move_addr_to_user` write
  (:1999-2000).  With a NULL address `do_accept` never
  touches `upeer_addrlen` (:1993 guards both) — not read, not written, not
  validated — so `addrlenp` is genuinely unused here (the header's
  spellings list says how the name is kept).
- -ECONNABORTED (:1996), which is unreachable for AF_INET/TCP: it comes
  only from `inet_getname` failing on `inet_dport == 0`, and `do_accept`
  passes `peer = 2` (:1994) specifically so the `TCPF_CLOSE` test is
  skipped.  A peer that resets between the handshake and the accept does
  NOT abort the connection — the child stays queued and is handed over,
  and the reset surfaces as -ECONNRESET on the first read.  That is
  exactly a connection whose script begins with a reset.

Linux net/socket.c `__sys_accept4` checks flags before lookup at v4.17;
v5.10 and v6.18.46 resolve the descriptor first.  QEMU 11.1.1
linux-user/syscall.c `do_accept4` checks flags and, for non-NULL addr,
reads and validates addrlen before the host call.  The corresponding
closed-fd and non-socket address shapes are declined.  Allocation
alternatives are justified beside the errno lists.  Issue #1472 (T152)
tracks the LSM run configuration. -/
def accept4_spec (fd addrp addrlenp flags : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none =>
      if ¬ (bv_unsigned (bv_and (abi_low32 flags)
              (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0)
      then unmodeled
      else if ¬ (w_is0 addrp) then unmodeled
      else err_ret EBADF
  | some e =>
      let fl := abi_low32 flags
      if ¬ (bv_unsigned (bv_and fl
              (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0)
      then err_ret EINVAL
      else if ¬ (bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0) then unmodeled
      else
      (match e with
       | .FdSocket sk =>
           if ¬ (w_is0 addrp) then unmodeled               -- the peer address
           else
           (match sk with
            | .SkListening =>
                alt (er <- errno_from accept_errnos ;; err_ret er)
                    (if conn_ix_exhausted (m_conn_ix m) then choose (fun (_ : SyscallEffect) => False)
                     else nfd <- lowest_fd (m_fds m) ;;
                          modify (with_accepted
                                   (fd_insert (m_fds m) nfd
                                     (.FdSocket (.SkConnected (nq_peer (m_net m))
                                                              (conn_channel (m_conn_ix m))
                                                              (nq_script (m_net m)))))) ;;
                          ret_only nfd)
            | _ => alt (err_ret EINVAL)
                        (er <- errno_from accept_notlisten_errnos ;; err_ret er))
       | _ => if ¬ (w_is0 addrp) then unmodeled
              /- Linux v6.18.46 (commit 1f99e9ab748f), fs/file.c `alloc_fd`
              reaches `expand_files`' ENOMEM only when the selected fd reaches
              the current max_fds. include/linux/fdtable.h `NR_OPEN_DEFAULT`
              is a capacity floor, not the current capacity: fs/file.c
              (Linux v6.18.46) `alloc_fdtable` grows toward a power-of-two size,
              clamped to sysctl_nr_open rounded down to BITS_PER_LONG,
              `close_fd` does not shrink it, and `dup_fd` sizes
              a fork child's table from its parent's highest open fd. The
              entry table may have grown before exec. State does not track
              this history, so at or above NR_OPEN_DEFAULT the floor does not
              decide whether expansion can fail. A capacity lower bound in
              State would lift this decline where it proves expansion unnecessary.
              Below the floor expansion is
              unnecessary. No example calls accept or accept4, so this bound
              does not change an example's equivalence theorem. -/
              else if NR_OPEN_DEFAULT ≤ bv_unsigned (alloc_fd (m_fds m)) then unmodeled
              else alt (err_ret ENOTSOCK)
                       (er <- errno_from accept_notsock_errnos ;; err_ret er))

/-! ## The descriptor half shared by getsockname, getpeername, setsockopt,
getsockopt and shutdown -/

/-- The socket an fd names, or the errno the five calls answer before they
look at any other argument.  `__sys_getsockname`, `__sys_getpeername`,
`__sys_setsockopt`, `__sys_getsockopt` and `__sys_shutdown` (net/socket.c,
Linux v6.18.46, commit 1f99e9ab748f) each open with `CLASS(fd, f)(fd)`,
answer -EBADF on `fd_empty` and -ENOTSOCK once `sock_from_file` has
returned NULL (net/socket.c:2144-2148, :2181-2185, :2380-2384, :2445-2449,
:2481-2485 for the five this file dispatches), and nothing else about the
call is examined before that verdict.  `sock_from_file` (net/socket.c:530-536, v6.18.46) is the single
comparison `file->f_op == &socket_file_ops` (:532), so every non-socket
kind answers -ENOTSOCK alike: a pipe end's `f_op` is `pipeanon_fops`
(`create_pipe_files`, fs/pipe.c:926, at :946 and :957), /dev/null's is
`null_fops` (drivers/char/mem.c:644, v6.18.46) and /dev/urandom's is `urandom_fops`
(drivers/char/random.c:1572).  The arms are spelled out rather than
wildcarded ON PURPOSE, so that a socket-like constructor added to `FdEntry`
breaks this definition and forces an answer rather than inheriting
-ENOTSOCK.  Argument on Rocq's `Net.Socket.sock_fd`.

A NOTE ON THE LSM AND THE CGROUP BPF HOOKS, once, for all five.  Each call
runs a `security_socket_*` hook past this verdict — `do_sock_setsockopt`
and `do_sock_getsockopt` open with theirs (net/socket.c:2338-2340 and
:2405-2407, v6.18.46) — and every hook can deny (the hooks default to 0:
`security_socket_setsockopt` and `security_socket_getsockopt`,
security/security.c, and include/linux/lsm_hook_defs.h:345-346, v6.18.46);
the two option calls then run `BPF_CGROUP_RUN_PROG_SETSOCKOPT` and
`BPF_CGROUP_RUN_PROG_GETSOCKOPT` (include/linux/bpf-cgroup.h:376-403,
v6.18.46), which return 0 or `retval` unchanged unless a program is
attached, and may rewrite the arguments or answer themselves when one is.
This model, like Rocq's (the LSM note on `Net.Socket.sock_fd`), describes a
kernel whose active LSMs do not deny and whose cgroups carry no sockopt
program — the environment the guest of testing/vm/README.md boots; an
enforcing SELinux or AppArmor policy, or an attached program, is outside
the modeled environment, not a case answered wrongly. -/
def sock_fd (m : Model) (fd : word) : SockState ⊕ Int :=
  match fd_lookup (m_fds m) fd with
  | none => .inr EBADF                    -- fd not open: real -EBADF, before any argument is examined
  | some (.FdChannel _) => .inr ENOTSOCK  -- an external channel is not a socket
  | some (.FdFile _ _) => .inr ENOTSOCK
  | some (.FdFileW _ _) => .inr ENOTSOCK
  | some (.FdFileA _ _) => .inr ENOTSOCK
  | some (.FdFileRW _ _) => .inr ENOTSOCK
  | some .FdDir => .inr ENOTSOCK
  | some (.FdPipe _ _) => .inr ENOTSOCK   -- pipeanon_fops is not socket_file_ops
  | some (.FdDevNull _ _) => .inr ENOTSOCK  -- nor is null_fops
  | some .FdUrandom => .inr ENOTSOCK      -- nor urandom_fops
  | some (.FdSocket sk) => .inl sk

/-- A level with a handler on an AF_INET/SOCK_STREAM socket, and so the
level test both option calls share.  SOL_SOCKET (1,
include/uapi/asm-generic/socket.h:9, Linux v6.18.46, commit 1f99e9ab748f) is
answered in place by `do_sock_setsockopt` (net/socket.c:2356-2357, v6.18.46)
— unless the socket has SOCK_CUSTOM_SOCKOPT set, which
`sock_use_custom_sol_socket` (net/socket.c:2323-2326, v6.18.46) tests and
which only mptcp, af_unix, udp and vsock ever set (the set_bit of
SOCK_CUSTOM_SOCKOPT at net/mptcp/protocol.c:2975 and :4066,
net/unix/af_unix.c:1162 and :1890, net/vmw_vsock/af_vsock.c:1806 and
:2610, and include/net/udp.h:295, v6.18.46), none of them a socket this
model can hold — and by `do_sock_getsockopt` (net/socket.c:2413-2414,
v6.18.46), which has no such condition; every other level walks the
protocol chain, where `tcp_setsockopt` (net/ipv4/tcp.c:4162-4166,
v6.18.46) keeps SOL_TCP and hands the rest to `ip_setsockopt`
(net/ipv4/ip_sockglue.c:1414-1415, v6.18.46), which keeps SOL_IP; the get
side's `tcp_getsockopt` (net/ipv4/tcp.c:4841-4845, v6.18.46) and
`do_ip_getsockopt` (net/ipv4/ip_sockglue.c:1515-1516, v6.18.46) are the same
two tests.  SOL_IP is 0 and SOL_TCP is 6 (include/linux/socket.h:348-350,
v6.18.46), the values the Uapi spells IPPROTO_IP and IPPROTO_TCP, as Rocq
does.  Anything else is refused BY THE LEVEL, and the two option calls
refuse it with DIFFERENT ERRNOS — `setsockopt_spec` and `getsockopt_spec`
below.  Rocq: `Net.Socket.sock_level_known`. -/
def sock_level_known (level : word) : Bool :=
  let l := bv_unsigned level
  l = SOL_SOCKET ∨ l = IPPROTO_IP ∨ l = IPPROTO_TCP

/-- `how` is one of the three `enum sock_shutdown_cmd` members
(include/linux/net.h:92-96, Linux v6.18.46, commit 1f99e9ab748f): the
values `inet_shutdown` accepts once it has done `how++`, tested against
`SHUTDOWN_MASK` (net/ipv4/af_inet.c:896-900).  Rocq:
`Net.Socket.shut_how_ok`. -/
def shut_how_ok (how : word) : Bool :=
  let h := bv_unsigned how
  h = SHUT_RD ∨ h = SHUT_WR ∨ h = SHUT_RDWR

/-- Negative when its LOW 32 BITS are read as the `int` the argument is:
`do_sock_setsockopt` (net/socket.c:2328-2336, Linux v6.18.46, commit
1f99e9ab748f) takes `int optlen` (:2329) and tests `optlen < 0` (:2335).
`sint32` does that truncation itself, so this is total on a `word`: the
model's tests on these arguments are the kernel's own, and the kernel's are
on the truncated `int`.  Rocq: `Net.Socket.int32_neg`. -/
def int32_neg (w : word) : Bool := sint32 w < 0

/-! ## getsockname (204), getpeername (205) -/

/-- `getsockname fd addr addrlen` — DECLINED ON A SOCKET, and the reason is
not "hard".  `inet_getname` with `peer = 0` (net/ipv4/af_inet.c:797, at
:818-826, Linux v6.18.46, commit 1f99e9ab748f) HAS NO ERROR RETURN AT ALL:
it fills a `sockaddr_in` from `inet_sport` and `inet_rcv_saddr` and returns
a length (:829).  So on a socket the only answer is a SUCCESS THAT WRITES
AN ADDRESS through `move_addr_to_user` (net/socket.c:276, v6.18.46, called at
:2159).  AND THE VALUE IS NOT THE MODEL'S TO KNOW past a
fresh socket: `bind` and `listen` autobind an EPHEMERAL PORT that
`inet_csk_find_open_port` (net/ipv4/inet_connection_sock.c:315, v6.18.46) draws at
random (get_random_u32_below, :348), and an accepted socket
inherits the listener's; answering would mean a `choose` over a value the
program can print.  The non-socket half is `sock_fd`'s and exact.
Argument on Rocq's `Net.Socket.getsockname_spec`. -/
def getsockname_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl _ => unmodeled            -- an address write, and a port the model cannot know

/-- `getpeername fd addr addrlen` — THE ONE CALL OF THE FIVE THAT SEPARATES
THE SOCKET STATES.  `inet_getname` with `peer = 1` (net/ipv4/af_inet.c:
797-830, Linux v6.18.46, commit 1f99e9ab748f) refuses first,

    if (!inet->inet_dport ||
        (((1 << sk->sk_state) & (TCPF_CLOSE | TCPF_SYN_SENT)) && peer == 1))
            return -ENOTCONN;

(:808-813), and only past that copies the address out.  Two disjuncts,
each catching a different set of this model's states: `inet_dport == 0` on
every socket that was never connected — fresh, bound, listening — a plain
errno with no memory effect, and EXACT; and `sk_state` in `TCPF_CLOSE` on
a RESET connection, which is the whole reason `State.SockState` carries
`SkReset` as a constructor of its own: a peer RST ran `tcp_done`
(net/ipv4/tcp.c:5020, v6.18.46), which does `tcp_set_state(sk, TCP_CLOSE)`
(:5033) and does NOT clear `inet_dport`; the dport survives and the STATE
test fires.  A consumed FIN, by contrast, leaves TCP_CLOSE_WAIT, in
NEITHER disjunct, so a connected socket whose script is at end-of-stream
SUCCEEDS on Linux — and is declined here for `getsockname_spec`'s reason
alone: the answer is a success that writes an address.  The address itself
is available and honest (`State.nq_peer` took it from the run's input), so
that decline is a missing export, not a missing value.  Argument on Rocq's
`Net.Socket.getpeername_spec`. -/
def getpeername_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl sk =>
      (match sk with
       | .SkFresh => err_ret ENOTCONN       -- inet_dport == 0
       | .SkBound => err_ret ENOTCONN
       | .SkListening => err_ret ENOTCONN
       | .SkReset _ _ => err_ret ENOTCONN   -- tcp_done left TCP_CLOSE; dport still set
       | .SkConnected _ _ _ => unmodeled)   -- succeeds, writing the peer: no address export

/-! ## setsockopt (208), getsockopt (209) -/

/-- `setsockopt fd level optname optval optlen`.  Two real answers and a
decline, in the kernel's order — and the level's errno is NOT the one
`getsockopt` gives.

THE FD FIRST.  `__sys_setsockopt` (net/socket.c:2372-2387, Linux v6.18.46,
commit 1f99e9ab748f) opens with `CLASS(fd, f)(fd)` (:2378), answers -EBADF
on `fd_empty` (:2380-2381) and -ENOTSOCK once `sock_from_file` has returned
NULL (:2382-2384), and only then calls `do_sock_setsockopt` (:2386) with
`optlen` by value.  That half is `sock_fd`'s.

-EINVAL FOR A NEGATIVE `optlen`, SECOND.  The first statement of
`do_sock_setsockopt` (net/socket.c:2328-2366, v6.18.46) is `if (optlen < 0)
return -EINVAL;` (:2335-2336), ahead of the LSM hook (:2338-2340), the
cgroup BPF hook (:2342-2351) and every level dispatch (:2355-2362).
`optlen` is an `int` (:2329), so the test is on the low 32 bits read as
signed, which is `int32_neg`.  Up to v6.6 this check sat in
`__sys_setsockopt` AHEAD of the descriptor lookup, where the same call on a
closed fd was -EINVAL and not -EBADF; this spec states the v6.7-and-later
order, which is why the test is inside the socket arm rather than beside
`sock_fd` (Rocq's `Net.Socket.setsockopt_spec` carries the window).  What
the premise costs — a v4.17..v6.6 kernel answers -EINVAL on a closed fd, a
trace this spec refuses as impossible — is recorded in
bugs/setsockopt-getsockopt-orders-rest-on-v6.7-and-v6.11.md.

-ENOPROTOOPT FOR AN UNKNOWN LEVEL, THIRD, AND NOT -EOPNOTSUPP.  Past the
length, SOL_SOCKET is answered in place (:2356-2357) and every other level
goes to `ops->setsockopt` (:2361-2362).  Ahead of both, past the length
test, sits the cgroup BPF hook (:2342-2351), and with a program attached it may rewrite `level`,
`optname` and `optlen` or answer 0 itself; `BPF_CGROUP_RUN_PROG_SETSOCKOPT`
(include/linux/bpf-cgroup.h:376-387, v6.18.46) starts from `int __ret = 0`
and runs a filter only under `cgroup_bpf_enabled`, so with none attached
the dispatch below sees the arguments as passed — the modeled
environment `sock_fd`'s note on the LSM and the cgroup BPF hooks states,
and Rocq's premise too.  On an AF_INET/SOCK_STREAM socket
that member of `inet_stream_ops` (net/ipv4/af_inet.c:1063, v6.18.46) is
`sock_common_setsockopt` (net/core/sock.c:3910-3917, v6.18.46), which
forwards to the protocol's member (:3916), `tcp_setsockopt` in `tcp_prot`
(net/ipv4/tcp_ipv4.c:3515, v6.18.46); `tcp_setsockopt`
(net/ipv4/tcp.c:4157-4167, v6.18.46) keeps SOL_TCP and hands any other level (:4162-4165)
to the address family's member, `ip_setsockopt` in `ipv4_specific`
(net/ipv4/tcp_ipv4.c:2501, v6.18.46), whose FIRST statement —
`ip_setsockopt` (net/ipv4/ip_sockglue.c:1409-1427, v6.18.46) — is `if (level
!= SOL_IP) return -ENOPROTOOPT;` (:1414-1415).  The check is there and not
in `do_ip_setsockopt` (net/ipv4/ip_sockglue.c:892-900, v6.18.46), which has
no level test at all and switches on the optname (:900) — and the get
side's mirror image of this walk answers -EOPNOTSUPP instead
(`getsockopt_spec`).  THE ASYMMETRY IS REAL and is exactly the shape a
model invents symmetry over, so it is MEASURED rather than asserted:
testing/syscall-check/tests/socket_calls.c's `levels` run puts both calls
at SOL_UDP, a level with no handler on a TCP socket, and its `level-tcp`,
`level-socket` and `level-ip` runs are the boundary that keeps that from
being an answer to everything.  No user memory is read on the way: `optval`
is untouched and `optlen` is by value.

EVERYTHING PAST THE LEVEL IS DECLINED — the option table itself.  Three
shapes it would have to get right, none of them guessable: an unknown
optname is -ENOPROTOOPT and not -EINVAL at every layer (the `default:` arm
of `sk_setsockopt` (net/core/sock.c:1668-1669, v6.18.46)); two options
ACCEPT AND DISCARD, storing nothing and returning 0 — SO_BSDCOMPAT, a bare
`break` in `sk_setsockopt` (net/core/sock.c:1417-1418, v6.18.46) past only
the generic `optlen < sizeof(int)` test and copy of `val` (:1204-1208), and
TCP_THIN_DUPACK, which `do_tcp_setsockopt` (net/ipv4/tcp.c:3963-3966,
v6.18.46) validates in {0,1} and stores nowhere; and several options really do change later behaviour,
so accepting them silently is not free.  Argument in full on Rocq's
`Net.Socket.setsockopt_spec`. -/
def setsockopt_spec (fd level optlen : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl _ =>
      if int32_neg optlen then err_ret EINVAL         -- do_sock_setsockopt's first statement (v6.7+)
      else if ¬ (sock_level_known level) then err_ret ENOPROTOOPT   -- ip_setsockopt
      else unmodeled                                  -- the option table

/-- The four bytes `do_sock_getsockopt` (net/socket.c:2409-2410, Linux
v6.18.46, commit 1f99e9ab748f) reads at `optlen` before it dispatches on the
level — `sizeof(int)` — or NOTHING when that range is not wholly readable:
`copy_from_sockptr` (include/linux/sockptr.h:59-62, v6.18.46) is a
copy_from_user on a user pointer, and a copy that faults moved none of it
that this model can see (`getsockopt_spec`, "ONE RESIDUE").  `read_bytes_map`
walks the four addresses with wrapping addition and no `access_ok`, where
`_inline_copy_from_user` (include/linux/uaccess.h:159-169, v6.18.46) —
riscv defines no `masked_user_access_begin`, so it takes the `access_ok`
branch, `__access_ok` in include/asm-generic/access_ok.h:31-41, v6.18.46 —
refuses a range that wraps or reaches past `TASK_SIZE_MAX` before it copies
a byte; the two agree because every range `access_ok` refuses contains an
address at or above `TASK_SIZE`, where no user mapping lies, so the walk
answers `none` there as well.  One definition for the spec and for any
checker or witness ported later, so they cannot drift apart.  Rocq:
`Net.Socket.getsockopt_optlen_read`. -/
def getsockopt_optlen_read (i : SyscallInput) (optlenp : word) : List (word × Nat) :=
  match read_bytes_map i.in_mem optlenp (Z_to_bv 64 4) with
  | some _ => [(optlenp, 4)]
  | none => []

/-- `getsockopt fd level optname optval optlen` — the same walk, the OTHER
errno, and a copy-in ledger.

THE FD FIRST.  `__sys_getsockopt` (net/socket.c:2439-2453, Linux v6.18.46,
commit 1f99e9ab748f) answers -EBADF on `fd_empty` (:2445-2446) and
-ENOTSOCK on a NULL `sock_from_file` (:2447-2449) before it calls
`do_sock_getsockopt` (:2451-2452), so neither errno reaches the read below
and neither carries a ledger.

FOUR BYTES AT `optlen` ARE READ BEFORE THE DISPATCH, and this spec RECORDS
them.  `do_sock_getsockopt` (net/socket.c:2398-2432, v6.18.46) runs
`security_socket_getsockopt` and returns on its error (:2405-2407), and
then — before it has looked at `level` at all — `if (!compat)
copy_from_sockptr(&max_optlen, optlen, sizeof(int));` (:2409-2410).
`__sys_getsockopt` passes `in_compat_syscall()` for `compat` (:2451), false
for a native riscv64 task, so on this port the read is UNCONDITIONAL; at
v6.18.46 the guarded shape is gone — include/linux/bpf-cgroup.h no longer
defines a BPF_CGROUP_GETSOCKOPT_MAX_OPTLEN, and the bare copy is what the
tree has (its removal in 33f339a1ba54 and the stable branches that took the
backport are Rocq's `Net.Socket.getsockopt_spec`, "THE VERSION WINDOW").  A
kernel without that commit — v6.6.50, v6.10.9, every 6.1.y — reads
`*optlen` here only while a cgroup getsockopt program is attached, so its
trace carries no copy-in where this spec records one; that premise and its
cost are recorded in
bugs/setsockopt-getsockopt-orders-rest-on-v6.7-and-v6.11.md.
The copy's RESULT is discarded — no assignment, no test; `max_optlen` keeps
its `= 0` initialiser (:2401) when the copy faults and is only handed to
`BPF_CGROUP_RUN_PROG_GETSOCKOPT` (include/linux/bpf-cgroup.h:389-403,
v6.18.46), which hands `retval` back unchanged unless a cgroup BPF program
is attached (:392-394) — so it changes no errno.  What it changes is
`eff_copyins`: the bytes really left user memory, so the ledger names them
(`getsockopt_optlen_read`).

-EOPNOTSUPP FOR AN UNKNOWN LEVEL, AND NOT -ENOPROTOOPT.  SOL_SOCKET is
answered in place by `sk_getsockopt` (:2413-2414); every other level goes
to `ops->getsockopt` (:2422-2423), which on this socket is the member of
`inet_stream_ops` (net/ipv4/af_inet.c:1064, v6.18.46) —
`sock_common_getsockopt` (net/core/sock.c:3888-3895, v6.18.46) — then the
protocol's, `tcp_getsockopt` (net/ipv4/tcp.c:4836-4847, v6.18.46), which
keeps SOL_TCP and hands the rest (:4841-4844) to the address family's,
`ip_getsockopt` (net/ipv4/ip_sockglue.c:1760-1784, v6.18.46), which calls
straight into `do_ip_getsockopt` (net/ipv4/ip_sockglue.c:1507-1516,
v6.18.46), whose FIRST statement is `if (level != SOL_IP) return
-EOPNOTSUPP;` (:1515-1516).  So an unknown level is -EOPNOTSUPP here and
-ENOPROTOOPT on the set side, out of two functions in the same file.

IT ALSO BEATS A BAD `optlen` POINTER, which is the ordering a reader
expects backwards.  The length that DECIDES anything is read DOWNSTREAM of
the level test — inside `do_ip_getsockopt`, and inside `sk_getsockopt`
(net/core/sock.c:1743-1746, v6.18.46), where `copy_from_sockptr(&len,
optlen, sizeof(int))` is -EFAULT and `len < 0` is -EINVAL — so
`getsockopt(sockfd, 12345, ..., NULL)` is -EOPNOTSUPP and not -EFAULT, and
the pre-dispatch read above faults the COPY, never the call.

WHETHER TO RECORD AN UNREADABLE `optlen` IS A DECISION, not a default,
because the errno does not settle it: a faulting copy is discarded exactly
like a successful one, so -EOPNOTSUPP stands either way and both ledgers
were available.  It is recorded only when the whole four-byte range is
MAPPED.  An unconditional ledger would claim four bytes left user memory on
a call where copy_from_user took its fixup path and moved none, and
`eff_copyins` feeds `State.materialize_model_accesses`, which charges a
first touch against the backing limit — so it would charge a page the
kernel never faulted in and could refuse a run Linux allows.  ONE RESIDUE,
named rather than left silent: copy_from_user copies PARTIALLY, so a
four-byte `optlen` straddling a page boundary whose first page is mapped
really does touch that first page before faulting, while `read_bytes_map`
fails on the whole range and this spec then records nothing.  That
under-records by at most one page, in the same accept-more direction the
empty ledger had, and it is the identical bound `bind_spec` carries.

A KNOWN LEVEL IS DECLINED, for `setsockopt_spec`'s reasons plus one of its
own: on the get side an over-long `*optlen` is silently TRUNCATED rather
than refused, and `*optlen` is rewritten to the bytes actually copied — a
memory write, and the export the model does not have.  The ledger is
recorded on that arm too, and simply never compared: an `Unmodeled` carries
no effect for a ledger to be right or wrong about.  Argument in full on
Rocq's `Net.Socket.getsockopt_spec`. -/
def getsockopt_spec (fd level optlenp : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match sock_fd m fd with
  | .inr e => err_ret e
      -- __sys_getsockopt resolves the fd before it calls do_sock_getsockopt,
      -- so neither -EBADF nor -ENOTSOCK reaches the read and neither carries a ledger
  | .inl _ =>
      record_copyins (getsockopt_optlen_read i optlenp)
        (if ¬ (sock_level_known level) then err_ret EOPNOTSUPP  -- do_ip_getsockopt
         else unmodeled)                                       -- the option table

/-! ## shutdown (210) -/

/-- `shutdown fd how`.  Two real answers and a decline, and the DECLINE is
the most carefully argued arm in this file.

-EINVAL FOR A `how` OUTSIDE {0,1,2}, ON EVERY SOCKET STATE.  Nothing in
`__sys_shutdown` (net/socket.c:2476, Linux v6.18.46, commit
1f99e9ab748f) or `__sys_shutdown_sock` (net/socket.c:2465) tests `how`, which is why a NON-socket fd is
-ENOTSOCK however wild the argument.  The rejection is `inet_shutdown`'s
(net/ipv4/af_inet.c:888, v6.18.46) and it is the first thing that function does:
`how++` (:896), then `if ((how & ~SHUTDOWN_MASK) || !how) return -EINVAL;`
(:899-900), BEFORE `lock_sock` (:902) and before any write to
`sk_shutdown`, so this -EINVAL leaves the socket bit for bit unchanged —
which is what lets a model with no shutdown bits answer it.  (`how = -1`
passes the mask after the increment and is caught by `!how`; that is what
the kernel's `MAXINT->0` comment means.)

0 FOR SHUT_WR ON A LISTENING SOCKET, WITH NO STATE CHANGE.  The switch on
`sk_state` (:911) has a `case TCP_LISTEN:` whose whole body is `if (!(how &
RCV_SHUTDOWN)) break;` (:927-929).  For SHUT_WR the incremented `how` is 2,
`2 & RCV_SHUTDOWN` is 0 (include/net/sock.h:1491-1493, v6.18.46), and the `break`
leaves `err` at 0 WITHOUT reaching the `default:` arm — `sk_shutdown` is
not ORed, `sk_prot->shutdown` is not called.  Exact, and a genuine success.

EVERYTHING ELSE IS DECLINED, AND HERE IS THE TRAP THAT FORCES IT.  The
obvious answer for a fresh, bound or reset socket is -ENOTCONN, and the
errno is right — those are TCP_CLOSE.  But `case TCP_CLOSE: err =
-ENOTCONN; fallthrough;` (:912-916) into `default: WRITE_ONCE(sk->sk_shutdown,
sk->sk_shutdown | how);` (:917-918) RETURNS THE ERROR AND STILL APPLIES THE
SHUTDOWN, and the bit is observable on the very next read:
`tcp_recvmsg_locked` (net/ipv4/tcp.c:2634, v6.18.46) tests `sk_shutdown &
RCV_SHUTDOWN` (:2749) BEFORE its `sk_state == TCP_CLOSE` -ENOTCONN arm
(:2752-2756), so after `shutdown(fresh, SHUT_RD)` a real `read` returns 0
where without it the read is -ENOTCONN.  `State.SockState` carries no
shutdown bits, so a spec answering -ENOTCONN would buy a right errno with a
wrong successor state — precisely the class the equivalence cannot see.
The same argument covers SHUT_RD/SHUT_RDWR on a listener (they fall through
to `disconnect`, :930-934, purging the accept queue) and every `how` on a
connected socket (the `default:` arm sets the bits and `tcp_shutdown` may
send a FIN).  Spelled out rather than wildcarded, for `sock_fd`'s reason.
Argument on Rocq's `Net.Socket.shutdown_spec`. -/
def shutdown_spec (fd how : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | .inr e => err_ret e
  | .inl sk =>
      if ¬ (shut_how_ok how) then err_ret EINVAL   -- inet_shutdown, before lock_sock
      else
        (match sk with
         | .SkFresh => unmodeled                   -- TCP_CLOSE: -ENOTCONN, bits set
         | .SkBound => unmodeled                   -- still TCP_CLOSE; bind moves nothing
         | .SkListening =>
             if bv_unsigned how = SHUT_WR
             then ret_only (Z_to_bv 64 0)          -- case TCP_LISTEN: break, nothing written
             else unmodeled                        -- SHUT_RD/SHUT_RDWR: tcp_disconnect
         | .SkConnected _ _ _ => unmodeled         -- default: the bits, maybe a FIN
         | .SkReset _ _ => unmodeled)              -- tcp_done: TCP_CLOSE again

/-! ## The socket write path: sendto (206), sendmsg (211)

MSG_NOSIGNAL IS REQUIRED, AND IT IS CHECKED FIRST.  `sk_stream_error`
(net/core/stream.c:190-197, Linux v6.18.46, commit 1f99e9ab748f) turns an
-EPIPE into `sock_error(sk) ? : -EPIPE` and then raises SIGPIPE exactly
when the final answer is -EPIPE and MSG_NOSIGNAL is clear; a partial send
never gets there, since `tcp_sendmsg_locked`'s `do_error:` label
(net/ipv4/tcp.c:1079-1406, at :1387-1391, v6.18.46) returns the count
whenever `copied + copied_syn` is nonzero.  `__sys_sendto`
(net/socket.c:2210-2246, v6.18.46) sets `msg.msg_flags` from the syscall
argument (:2244) and `____sys_sendmsg` (net/socket.c:2574-2648) from the
`flags` its caller passes (:2614), so for these two calls the flag is
something the spec can READ, which is why the path is modelable at all;
write(2) and writev(2) cannot set it and stay declined on a socket
(`Fs.ReadWrite.write_spec`).  The gate runs before the fd and the buffer,
the opposite of the kernel's order.  Rocq gives three reasons for that
order, and in this twin only the last — it is the gate a reader must find
first — still holds: with both connected states declined (below), the
one socket answer left is `SendDead`'s -EPIPE, which is decided by
`(i, m)` alone, so a later gate declining exactly the flagless -EPIPE
would be writable here and would not lean on `m_net`.  The order is kept
for parity with Rocq's arm, and what that costs is named: a flagless send
is declined even where Linux answers -EBADF, -ENOTSOCK or -EFAULT without
a signal.  At some of those inputs the place is also what keeps the spec
sound, because qemu-user answers otherwise (QEMU 11.1.1).  For sendmsg,
and for sendto with a NULL `addr` and an `addrlen` nonnegative as a 32-bit
`int`, as the pins for these inputs take them: over an in-range
nonzero-length sendto buffer, or any sendmsg header, that it cannot lock,
on a closed or non-socket fd, it answers -EFAULT (`do_sendto`'s lock,
linux-user/syscall.c:3648-3652, QEMU 11.1.1; `do_sendrecvmsg`'s,
:3445-3450) where Linux answers -EBADF or -ENOTSOCK, and a zero-length
sendto at a kernel address, which it never locks (:3648), reaches the
host's answer on the fd where Linux answers -EFAULT.  A non-NULL `addr`
is locked for `addrlen` bytes before the host call
(`target_to_host_sockaddr`, linux-user/syscall.c:1687-1689, via :3665,
QEMU 11.1.1), so beside a readable buffer on a closed or non-socket fd a
nonzero-length one it cannot lock is -EFAULT there as well, where Linux
answers -EBADF or -ENOTSOCK before it reads `addr` (net/socket.c:2222-2227
and :2234-2240, v6.18.46).  At a negative `addrlen`, sendto is -EINVAL
there ahead of all of these (linux-user/syscall.c:3644-3646,
QEMU 11.1.1).  The decline admits every one of these.  The
`sendto_flagless_*` and `sendmsg_flagless_*` pins in
Checks/Cases/Net/Socket.lean name each of these inputs on the closed 9 and
on the channel 1 of `fresh_socket_model`, a decline and a refutation of
Linux's answer at each.

THE STANDING PRECONDITION, stated over two MODELED SETS so a reader can
settle it in one step: SIGPIPE is the only signal this path can raise
because SIGIO needs two settings this model can reach neither of.  The
argument is over the socket's fasync LIST, not over the route to it:
`kill_fasync(&wq->fasync_list, SIGIO, band)` is called in
`sock_wake_async` (net/socket.c:1494-1517, at :1510, v6.18.46), which
returns before it when the list is empty (:1496-1497), and the routes into
`sock_wake_async` are several — `sk_wake_async`
(include/net/sock.h:2536-2543, v6.18.46) and `sk_wake_async_rcu`
(include/net/sock.h:2545-2549) under `SOCK_FASYNC`, and TCP's write-space
hook, `sk_stream_write_space` (net/core/stream.c:34-51, at :47-48,
v6.18.46; installed at net/ipv4/tcp.c:484), which tests the list and not
the flag.  Only `sock_fasync` (net/socket.c:1471-1490) creates entries
on a socket's list, through `fasync_helper` with `on` nonzero (:1481); the
one other writer of a non-empty list, `smc_switch_to_fallback`
(net/smc/af_smc.c:931-961, at :948-950, v6.18.46), moves the entries
`sock_fasync` put on an SMC socket onto its TCP socket, and this model
reaches no SMC socket.  `socket_spec` makes a descriptor only for
`AF_INET`, a type of `SOCK_STREAM` and a protocol of `IPPROTO_IP` or
`IPPROTO_TCP`; every other input, `AF_SMC` and `IPPROTO_SMC` among them,
gets an errno or a decline, and neither makes a descriptor; the
route that turns a TCP socket it does create into one,
`setsockopt(SOL_TCP, TCP_ULP, "smc")` (`do_tcp_setsockopt`,
net/ipv4/tcp.c:3852-3869; `tcp_set_ulp`, net/ipv4/tcp_ulp.c:157-168;
`smc_ulp_init`, net/smc/af_smc.c:3428-3468, which hands the file over at
:3460-3465; all v6.18.46), is inside `setsockopt_spec`'s decline of every
option at a level it knows (`setsockopt_sol_tcp_declines`), so a TCP_ULP
arm would falsify this.  Two syscalls reach `sock_fasync` with `on`
nonzero — F_SETFL with FASYNC through `setfl`'s test at fs/fcntl.c:75
(v6.18.46), and FIOASYNC through `ioctl_fioasync` (fs/ioctl.c:363-383,
v6.18.46).  `__fput` (fs/file_table.c:479, at :500-502, v6.18.46) calls
it too, with `on` 0, when the last reference to a file with FASYNC set
goes — as a close, a dup2 or dup3 over the fd, a close_range, an exit or
a close-on-exec can make it — and that only takes entries off.
`Fs.Fcntl.setfl_acted_on` carries FASYNC, so `Fs.Fcntl.setfl_noop_on` is
false on any `arg` naming it and `Fs.Fcntl.fcntl_spec` declines
(`setfl_noop_declines_fasync` below is that step as a theorem); FIOASYNC
is not in `Fs.Ioctl.tty_only_request`.  And even a socket on the list
signals nobody without an owner: the owner is allocated lazily by
`file_f_owner_allocate` (fs/fcntl.c:95-113, v6.18.46), whose callers that
can act on a socket's file are `f_setown` (fs/fcntl.c:153), `f_setown_ex`
(fs/fcntl.c:216) and `f_owner_sig` (fs/fcntl.c:420), i.e. F_SETOWN, F_SETOWN_EX, F_SETSIG and
the FIOSETOWN/SIOCSPGRP ioctls `sock_ioctl` routes into the first of them
(net/socket.c:1282, at :1312-1317, v6.18.46).  Its other callers are
refused on a socket before they reach it — `generic_add_lease`
(fs/locks.c:1774, at :1786) behind `vfs_setlease`'s `S_ISREG` test
(:2021-2022), `fcntl_dirnotify` (fs/notify/dnotify/dnotify.c:259, at
:311) behind its `S_ISDIR` test (:288-291) — or belong to another file
type's `fasync` (`__tty_fasync`, drivers/tty/tty_io.c:2204, at :2214;
`tun_chr_fasync`, drivers/net/tun.c:3373, at :3379).
`kill_fasync_rcu` (fs/fcntl.c:1111, v6.18.46) skips an entry without an
owner (:1125).  `Fs.Fcntl.fcntl_spec` answers F_SETFD, the provably empty
F_SETFL and F_GETFL and declines every other command.  ADDING A COMMAND TO
EITHER SET — an F_SETOWN arm, an F_SETFL that lets FASYNC through, a
FIOASYNC arm — BREAKS THIS PARAGRAPH, and the test a new arm must be put to
is whether it reaches `sock_fasync` with `on` nonzero or
`file_f_owner_allocate`.  SIGURG needs only the second of those settings,
so the owner gate alone closes it: `sk_send_sigurg`
(net/core/sock.c:3614-3619, v6.18.46) signals the file's owner through
`send_sigurg` (fs/fcntl.c:936-974, v6.18.46) without reading the fasync
list, and `send_sigurg` returns 0 without signalling when the file has no
owner (:945-947) or the owner names no pid (:953-954).  Only when
`send_sigurg` returns nonzero does `sk_send_sigurg` call
`sk_wake_async(sk, SOCK_WAKE_URG, POLL_PRI)` (net/core/sock.c:3618),
which goes on only for a socket flagged `SOCK_FASYNC`
(include/net/sock.h:2536-2543, v6.18.46), into `sock_wake_async`, which
returns at an empty fasync list (net/socket.c:1496-1497, v6.18.46) and
otherwise takes its `SOCK_WAKE_URG` arm (:1512-1513), where
`kill_fasync_rcu` skips an entry without an owner
(fs/fcntl.c:1124-1126, v6.18.46) and, for SIGURG, one whose F_SETSIG
`signum` is 0 (:1127-1131), and otherwise calls `send_sigio`.  Its
`send_sigio_to_task` (fs/fcntl.c:842-896, v6.18.46) sends nothing when
`sigio_perm` refuses (:852-853); otherwise it sends the `signum` F_SETSIG
chose (:850, :889), and when that send fails it falls back to plain SIGIO
(:892-894).  A real-time `signum` fails that way when `sig_get_ucounts`
finds the pending count of the receiving task's user over
RLIMIT_SIGPENDING (kernel/signal.c:424, v6.18.46): `__send_signal_locked`
then answers -EAGAIN for a real-time signal whose `si_code` is not
`SI_USER` (kernel/signal.c:1117-1126, v6.18.46).  So once the file has an
owner this path can raise SIGIO as well, whose default action terminates;
the owner gate closes it with the rest.  A third, independent gate:
`Kernel.Signal.sigaction_accepted` accepts SIGINT and SIGTERM only, so no
handler for SIGIO or SIGPIPE can be installed.  Rocq's section header
carries the list-and-owner argument and how its earlier "fcntl is
unmodeled" form went stale; the `send_sigurg` route, the `sigio_perm`
gate and the F_SETSIG fallback above are this twin's, beyond Rocq's
header, which names only the list route for SIGURG (Socket.v:1448-1452),
and so is the correction of its "only callers" of `file_f_owner_allocate`
(Socket.v:1485-1487): the callers refused on a socket and the other file
types' `fasync` above are the ones that list leaves out.

THE CONNECTED STATES ARE DECLINED HERE, BEYOND ROCQ.  Rocq's
`send_state` reads the head cell of the connection's script and answers
from it — delivery on a byte or a FIN (CLOSE_WAIT), the pending error once
on an RST or a timeout — and every one of those answers is decided by
timing the head cell does not carry, so each is a MODELED answer Linux does
not always give:

- a byte or a FIN at the head does not rule out a reset the kernel has
  ALREADY processed behind it: `tcp_reset` (net/ipv4/tcp_input.c:4678-4704,
  v6.18.46) records EPIPE in CLOSE_WAIT and ECONNRESET in ESTABLISHED
  through `tcp_done_with_error` (:4663-4674), which leaves TCP_CLOSE, so a
  send answers that error through `sk_stream_wait_connect`
  (net/core/stream.c:60-87, at :67-69) where Rocq allows only a delivery;
  and a timeout or a FIN-then-reset behind a byte leaves an error whose
  post-state `State.SockState` cannot write down;
- an RST or a timeout at the head does not say the kernel has processed it
  yet: the segment may still be in flight when the send runs, and then
  `tcp_sendmsg_locked` copies bytes (:1197 on) where Rocq allows only the
  errno.

So `send_on_socket` declines `SendGoes` and `SendErr` alike, as
`bind_spec`'s connected arm declines every head for the same reason
(this file's header), and `send_bytes` — ported name for name, because
OBL-4 of `tools/check_lean_port_obligations.py` refuses an `unported:`
entry naming a definition inside a dispatched arm's Rocq closure — is
referenced by no arm; `send_state` still is, through `send_on_socket`.  `SendDead` is EXACT and kept: a fresh,
bound, listening or reset socket is outside `TCPF_ESTABLISHED |
TCPF_CLOSE_WAIT`, `tcp_sendmsg_locked` calls `sk_stream_wait_connect`
(:1159-1164), and that answers -EPIPE (:70-71) ahead of its -EAGAIN
(:72-73), whatever the timeout and so whatever `O_NONBLOCK` would add;
`SkReset` is a socket whose error a read or send has already consumed
(`sock_error`, include/net/sock.h:2486, v6.18.46), so no error is left for
the first test to report. -/

/-- The FASYNC half of the standing precondition above, as a theorem: no
`F_SETFL` this model answers can carry the bit that would put a socket on a
fasync list.  `Fs.Fcntl.setfl_acted_on` is a SUPERSET of the kernel's
`SETFL_MASK` (fs/fcntl.c:37, Linux v6.18.46), which leaves FASYNC to the
`->fasync` callback; dropping FASYNC from the superset stops this proof
rather than reopening the SIGIO route.  Twin of Rocq's
`Net.Socket.setfl_noop_declines_fasync`, where it is a `Remark`. -/
theorem setfl_noop_declines_fasync (e : FdEntry) (arg : word) :
    Sys.Fs.Fcntl.setfl_noop_on e arg = true →
      bv_unsigned (bv_and arg (Z_to_bv 64 FASYNC)) = 0 := by
  intro h
  have hsub : bv_and (Z_to_bv 64 Sys.Fs.Fcntl.setfl_acted_on) (Z_to_bv 64 FASYNC)
      = Z_to_bv 64 FASYNC := by decide
  cases e <;> simp only [Sys.Fs.Fcntl.setfl_noop_on, decide_eq_true_eq,
    Bool.false_eq_true] at h <;>
  · have hz : bv_and arg (Z_to_bv 64 Sys.Fs.Fcntl.setfl_acted_on) = 0 :=
      BitVec.eq_of_toNat_eq (by unfold bv_unsigned at h; show _ = 0; omega)
    rw [← hsub]
    unfold bv_and at hz ⊢
    rw [← BitVec.and_assoc, hz]
    decide

/-- MSG_NOSIGNAL (include/linux/socket.h:319, Linux v6.18.46, commit
1f99e9ab748f).  Rocq: `Net.Socket.MSG_NOSIGNAL`. -/
def MSG_NOSIGNAL : Int := 0x4000

/-- The `flags` argument is `unsigned int` in both `SYSCALL_DEFINE6(sendto)`
(net/socket.c:2248-2253, Linux v6.18.46) and `SYSCALL_DEFINE3(sendmsg)`
(:2720), so the kernel sees its low 32 bits only — `Syscall.abi_low32`, at
the boundary `Syscall.fd32` narrows at.  Rocq: `Net.Socket.sendflags32`. -/
def sendflags32 (fl : word) : word := abi_low32 fl

/-- THE FIRST GATE: the low 32 bits of the flag word are EXACTLY
MSG_NOSIGNAL.  Not "MSG_NOSIGNAL is among the bits": MSG_DONTWAIT
(include/linux/socket.h:311, Linux v6.18.46) turns a wait into -EAGAIN,
MSG_MORE corks, MSG_OOB sends urgent data, MSG_ZEROCOPY and MSG_FASTOPEN
reach `tcp_sendmsg_locked`'s first branches (net/ipv4/tcp.c:1079-1406, at
:1103 and :1141),
and TCP IGNORES a bit it does not know rather than refusing it, so a
permissive reading would be a confident wrong answer for every bit this
model does not interpret.  The same exactness keeps `__sys_sendmsg`'s
MSG_CMSG_COMPAT gate (net/socket.c:2700-2718, v6.18.46, at :2706-2707) out of
reach.  Rocq: `Net.Socket.send_flags_modeled`, a `Z.eqb` on `bv_unsigned`. -/
def send_flags_modeled (fl : word) : Bool :=
  bv_unsigned (sendflags32 fl) = MSG_NOSIGNAL

/-- The connection as the SEND path sees it: the send goes out, or answers
a pending peer error once, or answers -EPIPE because there is no connection
to send on.  Rocq: `Net.Socket.SendState`. -/
inductive SendState : Type
  | SendGoes (chan : word)
  | SendErr (e : Int) (peer : PeerAddr) (chan : word)
  | SendDead

/-- Rocq's classification, kept as Rocq writes it so that the twin can be
read against it: a reset or a timeout at the head of the script is one
pending error, a FIN (CLOSE_WAIT, inside `TCPF_ESTABLISHED |
TCPF_CLOSE_WAIT`) or a byte lets the send go out, and every state without a
connection is `SendDead` — the fresh one included, because `tcp_prot` sets
`.no_autobind = true` (net/ipv4/tcp_ipv4.c:3549, Linux v6.18.46), so
`inet_send_prepare` (net/ipv4/af_inet.c:833-843) never autobinds and its
-EAGAIN is dead.  Only `SendDead` reaches an answer: `send_on_socket`
declines the other two, and the section header says why.  The Lean script
is a cell function, so the head is `rx.cell_at 0` where Rocq matches
`NCons`/`NFin`/`NRst`/`NTimedOut`.  Rocq: `Net.Socket.send_state`. -/
def send_state (sk : SockState) : SendState :=
  match sk with
  | .SkConnected peer ch rx =>
      match rx.cell_at 0 with
      | .NRst => .SendErr ECONNRESET peer ch
      | .NTimedOut => .SendErr ETIMEDOUT peer ch
      | .NFin => .SendGoes ch               -- CLOSE_WAIT: a send may go out
      | .NByte _ => .SendGoes ch
  | .SkReset _ _ => .SendDead
  | .SkBound | .SkListening => .SendDead
  | .SkFresh => .SendDead                   -- no autobind for TCP

/-- Rocq's delivery body, which both calls share once their arguments are
"these bytes, on this socket": a zero-length request is 0, an unreadable
first byte is -EFAULT, and otherwise any nonempty prefix of the gatherable
bytes goes out, one `WriteEv` per byte on the connection's channel, with
`pre` (what was copied before the payload) and `acc n` (the ranges an
`n`-byte prefix came out of) in the ledger.  NO ARM CALLS IT: every state it
would serve is declined by `send_on_socket` (the section header).  It is
here, unchanged, because Rocq's dispatched `send_on_socket` depends on it
and OBL-4 of `tools/check_lean_port_obligations.py` refuses an `unported:`
entry for such a definition; the day a
connected state is modeled again it is the body to start from, and its
short-send rule is `tcp_sendmsg_locked`'s `do_error:` (net/ipv4/tcp.c:
1387-1391, Linux v6.18.46).  Rocq: `Net.Socket.send_bytes`. -/
def send_bytes (pre : List (word × Nat)) (acc : Nat → List (word × Nat))
    (total : word) (bs : List byte) (ch : word) : Sys SyscallEffect :=
  if w_is0 total then record_copyins pre (ret_only (Z_to_bv 64 0))
  else if bs.length = 0 then record_copyins pre (err_ret EFAULT)
  else
    ds <- choose (fun ds : List byte =>
            1 ≤ (ds.length : Int)
            ∧ (ds.length : Int) ≤ bv_unsigned total
            ∧ ds = bs.take ds.length) ;;
    emit (List.map (WriteEv ch) ds) ;;
    record_copyins (pre ++ acc ds.length) (ret_only (len_word ds))

set_option linter.unusedVariables false in
/-- The socket half of both calls.  A socket with no connection is -EPIPE
with `pre` in the ledger — the bytes the call really copied before it
reached the connection state, nothing for `sendto` and the header and the
descriptors for `sendmsg` — and no payload byte, because
`sk_stream_wait_connect` answers before `tcp_sendmsg_locked`'s copy loop
(net/ipv4/tcp.c:1159-1164, Linux v6.18.46); a zero-length request is the
same -EPIPE, since the state is consulted before the loop that would return
0.  THE TWO CONNECTED ARMS DECLINE where Rocq sends or answers the pending
error (the section header): Rocq's `SendErr` arm also moved the socket to
`SkReset`, and its `SendGoes` arm called `send_bytes`.  `acc`, `fd`,
`total`, `bs` and `m` are kept, unread, so the signature stays Rocq's.
Rocq: `Net.Socket.send_on_socket`. -/
def send_on_socket (pre : List (word × Nat)) (acc : Nat → List (word × Nat))
    (fd : word) (sk : SockState) (total : word) (bs : List byte) (m : Model)
    : Sys SyscallEffect :=
  match send_state sk with
  | .SendDead => record_copyins pre (err_ret EPIPE)
  | .SendErr _ _ _ => unmodeled       -- the error may not have been processed yet
  | .SendGoes _ => unmodeled          -- a processed reset may sit behind the head

/-- Whether qemu-user's `lock_user` of `len` bytes at `base` succeeds:
every byte of the range readable.  `lock_user` with `VERIFY_READ` is
`access_ok_untagged` (linux-user/qemu.h:187-195, QEMU 11.1.1), which
asks `page_check_range` for `PAGE_READ` on every page of the range.
A byte of a writable LOAD segment is readable in the model whether or not
qemu-user can lock it; see `load_write_free`.
Linux's `import_ubuf` and `__import_iovec` ask only `access_ok`, a
RANGE test, and read nothing, so an in-range buffer this refuses is
where the two part: qemu-user answers -EFAULT before the host call,
Linux answers by the fd and the socket.  `readable_bytes`
materialises the readable prefix, so every caller bounds `len` by
`Uaccess.rw_bytes_max` first. -/
def seg_lockable (mp : word → Option byte) (base len : word) : Bool :=
  (readable_bytes mp base len).length == bv_unsigned len

/-- No byte of the range is both writable and in a LOAD reservation.
qemu-user maps a PF_W-only LOAD with PROT_WRITE (linux-user/elfload.c:1163-1171, QEMU 11.1.1),
without PAGE_READ (linux-user/mmap.c:124, QEMU 11.1.1), so `page_check_range` refuses
`lock_user(VERIFY_READ)` before the host call (accel/tcg/user-exec.c:538-541, QEMU 11.1.1).
The model's `in_mem` reads the writable overlay first, `in_wmem` accepts any
writable segment, and `Run.segments_reserved` records page-rounded LOAD
reservations without permissions; the read bit is unavailable, as
bugs/setgroups-eperm-arm-admits-linux-alone.md records.  Check only each
reservation's overlap using integer endpoints: an empty reservation list
reads no byte, and each overlap has at most `len` bytes. -/
def load_write_free (res : List (word × word)) (wmp : word → Option byte)
    (base len : word) : Bool :=
  res.all (fun r =>
    let lo := max (bv_unsigned base) (bv_unsigned r.1)
    let hi := min (bv_unsigned base + bv_unsigned len) (bv_unsigned r.1 + bv_unsigned r.2)
    (List.range (hi - lo).toNat).all (fun k =>
      (wmp (Z_to_bv 64 (lo + Int.ofNat k))).isNone))

/-- An empty reservation list inspects no bytes. -/
theorem load_write_free_nil (wmp : word → Option byte) (base len : word) :
    load_write_free [] wmp base len = true := by
  rfl

set_option linter.unusedVariables false in
/-- `sendto fd buf len flags addr addrlen`, in `__sys_sendto`'s order
(net/socket.c:2210-2246, Linux v6.18.46, commit 1f99e9ab748f) after the
model's gates:

- the flag word (`send_flags_modeled`, the section header);
- a destination address declines: on a TCP socket `move_addr_to_kernel`
  (net/socket.c:248-257, v6.18.46), called at :2234-2240, validates it —
  -EINVAL outside `[0, 128]`,
  -EFAULT if unreadable — and the protocol then ignores it outside repair
  and Fast Open, two errnos for a value nothing reads;
- a count above `Uaccess.rw_bytes_max` declines, the model's bound and not
  a kernel one;
- then THE BUFFER BEFORE THE FD: `import_ubuf` (lib/iov_iter.c:1433-1442,
  v6.18.46), called at :2218-2220, caps to `MAX_RW_COUNT` and applies
  `access_ok`, a RANGE test that reads no byte, before `CLASS(fd, f)`
  (:2222-2224, -EBADF) and `sock_from_file` (net/socket.c:530-536, called at
  :2225-2227, -ENOTSOCK).  `Uaccess.access_ok_zero` is that verdict — the
  opposite of write(2) and of `sendmsg_spec` below — and the fd match has to
  stay INSIDE it;
- then the socket (`send_on_socket`), with an empty `pre`: `import_ubuf`
  copies nothing, so -EBADF, -ENOTSOCK and -EPIPE all leave the ledger empty.

QEMU-USER ANSWERS THREE SHAPES BEFORE THE HOST'S FD, AND THEY ARE
DECLINED.  `do_sendto` (linux-user/syscall.c:3636-3680, QEMU 11.1.1)
tests `(int)addrlen < 0` first (:3644-3646), with `addr` NULL too,
where Linux v6.18.46 (commit 1f99e9ab748f) reads `addr_len` only
inside `if (addr)` (`__sys_sendto`, net/socket.c:2210-2246); it locks
a nonzero buffer before the host call (:3648-3652) and answers
-EFAULT where `seg_lockable` fails, while `import_ubuf`
(lib/iov_iter.c:1433-1442, v6.18.46) passes an in-range buffer on
to the fd and the socket; and it never locks a zero-length buffer,
so a zero-length send outside the user range reaches the host's fd
and socket answers where `import_ubuf` answers -EFAULT.  So a
negative low half of `addrlen`, a zero count beside an `access_ok`
refusal, and a nonzero in-range buffer `seg_lockable` refuses are
each unmodeled, ahead of any answer.  The nonzero -EFAULT kept by
`access_ok_zero` is qemu-user's too, on the premises
`iov_fault_at_head` states
(bugs/send-qemu-agreement-rests-on-unchecked-premises.md): no guest page
lies past `TASK_SIZE`, so
`lock_user` refuses the range `access_ok` refuses — without `-R` a
range that wraps 2^64 is refused by `guest_range_valid_untagged`
(include/user/guest-host.h:116-119, QEMU 11.1.1) and any other is
left to `page_check_range` — and the lock is reached at all.  No
example constructs a `sendto` call, so these declines cost
`Equivalence.strong_equiv` no theorem.

Without `-R`, a range that
wraps 2^64 is refused by the range test in every configuration:
`access_ok_untagged` (linux-user/qemu.h:187-195, QEMU 11.1.1) asks
`guest_range_valid_untagged` (include/user/guest-host.h:116-119,
delegating to `guest_range_valid_untagged_vaddr` at :63-66, QEMU 11.1.1)
before `page_check_range`, and against a `guest_addr_max` of
`~0ul` (linux-user/main.c:852, QEMU 11.1.1) that test fails exactly when
the range wraps.  Every other range ending past `TASK_SIZE` is left to
`page_check_range`, which refuses it unless every page of it carries
`PAGE_READ`, `VERIFY_READ` (linux-user/qemu.h:184, QEMU 11.1.1), as a page
the guest mapped or `mprotect`ed with `PROT_READ` does until an `mremap`
restamps it (`validate_prot_to_pageflags`, linux-user/mmap.c:121-124,
QEMU 11.1.1; the restamp is on `recvfrom_spec`), so such a page past
`TASK_SIZE` lets that buffer reach the host's answers; under
`-R` the range test refuses a buffer ending past `reserved_va` first
(linux-user/main.c:847-848, QEMU 11.1.1).  The order of the gates Rocq
shares is argued in full on Rocq's `Net.Socket.sendto_spec`. -/
def sendto_spec (fd buf count flags addrp addrlen : word) : Sys SyscallEffect :=
  if ¬ (send_flags_modeled flags) then unmodeled
  else if ¬ (w_is0 addrp) then unmodeled
  else if addrlen.getLsbD 31 then unmodeled
  else if ¬ (Sys.Uaccess.modeled_rw_count count) then unmodeled   -- see `Uaccess.rw_bytes_max`
  else if w_is0 count && !access_okb buf 0 then unmodeled
  else
  i <- input ;;
  m <- get_model ;;
  Sys.Uaccess.access_ok_zero buf count
    (if !(w_is0 count) && !(seg_lockable i.in_mem buf count
        && load_write_free (m_vmmaps m).vm_reserved i.in_wmem buf count) then unmodeled
     else match fd_lookup (m_fds m) fd with
     | none => err_ret EBADF
     | some (.FdSocket sk) =>
         send_on_socket [] (fun n => [(buf, n)]) fd sk count
           (readable_bytes i.in_mem buf count) m
     | some _ => err_ret ENOTSOCK)

/-- `struct user_msghdr` on LP64 (include/linux/socket.h:83-91, Linux
v6.18.46): seven fields in 56 bytes — `msg_name` at 0, `msg_namelen` (an
`int`) at 8, `msg_iov` at 16, `msg_iovlen` (`__kernel_size_t`) at 24,
`msg_control` at 32, `msg_controllen` at 40, `msg_flags` (`unsigned int`)
at 48, the two 4-byte fields padded to 8.  Rocq: `Net.Socket.MSGHDR_SIZE`. -/
def MSGHDR_SIZE : Int := 56

/-- WHICH IMPORT -EFAULT QEMU-USER GIVES TOO.  Asked only where
`State.import_iovecs` has answered `ImpFault`: true when the fault is the
ARRAY's (its range, or a descriptor that cannot be read) or DESCRIPTOR 0's
own range under a nonzero length; false when the range test that failed
belongs to a zero-length descriptor or to one after the first.  Linux
v6.18.46 answers -EFAULT for every one of these: `__import_iovec`
(lib/iov_iter.c:1352-1400, v6.18.46) applies `access_ok` to each
segment's uncapped length, a zero length included, and on the
one-descriptor path `import_ubuf` (:1433-1442) does so on the capped
length.  qemu-user does not.  `do_sendrecvmsg_locked`
(linux-user/syscall.c:3327-3437, QEMU 11.1.1) imports through `lock_iovec`
(:3072-3158) before the host's sendmsg runs, and there the buffer of a
zero-length descriptor "is ignored" and never locked, while a descriptor whose
`lock_user` fails at an index past 0 sets `bad_address` and zeroes the
rest of the vector, "a partial write" — so on a dead socket the host
answers -EPIPE.  Neither errno is in the intersection there, and
`sendmsg_spec` declines.  The shapes kept are -EFAULT in both: the array
is one `lock_user` of `count * sizeof(struct target_iovec)` bytes
(:3097-3102), and descriptor 0 is `if (i == 0) { err = EFAULT; …`, because
a range `access_okb` refuses ends past `TASK_SIZE`, where the run holds no
guest page, and `lock_user` (linux-user/uaccess.c, QEMU 11.1.1) refuses a
range `access_ok_untagged` (linux-user/qemu.h:187-195) does not find
mapped page by page.  That premise, and not qemu-user's own range test,
is what keeps those -EFAULTs for a range that does not wrap: for a riscv64
guest run without `-R`,
`guest_addr_max` is `~0ul` (linux-user/main.c:847-853, QEMU 11.1.1), so
`guest_range_valid_untagged` (include/user/guest-host.h:116-119, QEMU
11.1.1, delegating to `guest_range_valid_untagged_vaddr` at :63-66) admits
every range that does not wrap, and the refusal is `page_check_range`'s
(accel/tcg/user-exec.c:496-574, QEMU 11.1.1, refusing a range with no page
at :529 and :534).  A guest mapping past `TASK_SIZE` falsifies it, and no
invariant of the model states the premise.  The -EFAULTs
kept rest on a SECOND premise too: `lock_iovec` (linux-user/syscall.c,
QEMU 11.1.1) allocates the host vector with `g_try_new0` before any lock
(linux-user/syscall.c:3091-3095) and answers -ENOMEM when that fails, on
every count from 1 to `IOV_MAX` (1024: a glibc host's `<limits.h>`
defines it through `__IOV_MAX`, bits/uio_lim.h:30 in glibc 2.41, and
QEMU's fallback for a host defining none, include/qemu/osdep.h:394-396,
QEMU 11.1.1, is the same value) and on a socket as on any other fd, so qemu-user gives those
-EFAULTs only where the allocation succeeds.  A larger count never
reaches the allocation: `lock_iovec` answers -EINVAL for it first
(linux-user/syscall.c:3086-3089, QEMU 11.1.1), and sendmsg and recvmsg
answer -EMSGSIZE before `lock_iovec` runs (:3365-3371).  Linux allocates only past
`UIO_FASTIOV` (`iovec_from_user`, lib/iov_iter.c:1308-1312, v6.18.46), a
band `sendmsg_spec` declines.  No invariant of the model states this
premise either.  Whether
descriptor 0 is mapped is not asked,
so an unmapped descriptor 0 in front of a later range fault, -EFAULT in
both, is declined with the rest. -/
def iov_fault_at_head (mp : word → Option byte) (a n : word) : Bool :=
  if bv_eqb n (Z_to_bv 64 1) then
    if !access_okb a 16 then true
    else
      match read_iovec_entry mp a with
      | IovEntry _ len => !(w_is0 len)      -- the fault was `import_ubuf`'s range test
      | _ => true
  else if !access_okb a (16 * bv_unsigned n) then true
  else
    match copy_iovecs_aux mp a (word_to_nat n) with
    | ImpOk ((base, len) :: _) => !(w_is0 len) && !access_okb base (bv_unsigned len)
    | _ => true

/-- WHICH IMPORT -EINVAL QEMU-USER GIVES TOO.  Asked only where
`State.import_iovecs` has answered `ImpInval`: some descriptor's
`iov_len` is negative as an `ssize_t`, found by an index-order walk
that met no unreadable descriptor first.  `lock_iovec`
(linux-user/syscall.c:3097-3115, QEMU 11.1.1) locks the WHOLE array
before it looks at a length, and in its loop a nonzero descriptor 0
it cannot lock is -EFAULT before a later negative length is reached.
So qemu-user's -EINVAL needs every descriptor readable and descriptor
0 negative, zero, or lockable — the last asked only up to
`Uaccess.rw_bytes_max`, since `seg_lockable` materialises the bytes. -/
def iov_inval_at_head (mp : word → Option byte) (a n : word) : Bool :=
  match read_iovecs mp a n with
  | some ((b0, l0) :: _) =>
      decide (2 ^ 63 ≤ bv_unsigned l0) || w_is0 l0
      || (decide (bv_unsigned l0 ≤ Sys.Uaccess.rw_bytes_max) && seg_lockable mp b0 l0)
  | _ => false

/-- Every nonzero descriptor of an imported vector lockable by qemu-user.
Where one is not, `lock_iovec` (linux-user/syscall.c:3120-3142, QEMU 11.1.1) answers -EFAULT at index 0 or sends the descriptors before
it whole, while Linux, whose `access_ok` passed, answers by the
socket's state or moves a readable prefix.  A descriptor meeting a
writable LOAD byte counts as unlockable (`load_write_free`): on a socket
that sends, qemu-user's truncated vector and Linux's whole one move
different byte counts. -/
def iovs_lockable (mp wmp : word → Option byte) (res : List (word × word))
    (iovs : List (word × word)) : Bool :=
  iovs.all (fun bl => w_is0 bl.2 || (seg_lockable mp bl.1 bl.2 && load_write_free res wmp bl.1 bl.2))

/-- Whether qemu-user reaches the host's sendmsg — and so the host's fd
answer — for `msgp`, whatever the fd.  `do_sendrecvmsg`
(linux-user/syscall.c:3439-3454, QEMU 11.1.1) locks the 56-byte
header first (-EFAULT); `do_sendrecvmsg_locked` (:3327-3437) then
converts a non-NULL `msg_name`, answers -EMSGSIZE for a count over
`IOV_MAX`, imports through `lock_iovec` (-EFAULT for the array or a
nonzero descriptor 0, -EINVAL for any negative length), and converts
a control block of at least 16 bytes (`target_to_host_cmsg`, :1777,
-EFAULT) — all before the host resolves the fd.  This is a
sufficient condition, not qemu-user's exact one: a non-NULL name or
a nonzero `msg_controllen` is refused outright, and descriptor 0 is
asked only up to `Uaccess.rw_bytes_max`.  An unlockable descriptor
past the first is a partial write there and stays quiet.
Reads the header as this twin's socket arm does, with `copy_bytes_map`; Rocq reads it
with `read_bytes_map`, see `sendmsg_spec`'s THE HEADER READ.  Rocq's twin also tests
descriptor 0 against `2 ^ 63`; that test is implied, so no
pin could separate it, and it is left out here. -/
def sendmsg_prehost_quiet (mp : word → Option byte) (msgp : word) : Bool :=
  match copy_bytes_map mp msgp MSGHDR_SIZE with
  | none => false
  | some hdr =>
      let name := le_bytes_to_word (hdr.take 8)
      let iov := le_bytes_to_word ((hdr.drop 16).take 8)
      let n := le_bytes_to_word ((hdr.drop 24).take 8)
      let ctllen := le_bytes_to_word ((hdr.drop 40).take 8)
      (w_is0 name && w_is0 ctllen && decide (bv_unsigned n ≤ IOV_MAX)
      && (w_is0 n
          || match read_iovecs mp iov n with
             | some ((b0, l0) :: rest) =>
                 ((w_is0 l0
                     || (decide (bv_unsigned l0 ≤ Sys.Uaccess.rw_bytes_max)
                         && seg_lockable mp b0 l0))
                 && rest.all (fun bl => decide (bv_unsigned bl.2 < 2 ^ 63)))
             | _ => false))

/-- QEMU 11.1.1 locks the header (`do_sendrecvmsg`, linux-user/syscall.c:3445-3450),
then the array and descriptor 0 (`lock_iovec`, :3097-3102 and :3120-3128)
before the host resolves the fd.  A later descriptor it cannot lock is sent
as length 0 (`lock_iovec`, :3129-3142), so the host's answers on the closed-fd,
non-socket and no-connection socket arms are Linux's, and later descriptors are not asked here;
`iovs_lockable` asks them where a socket would send.  Linux reads a PF_W-only page: `protection_map[VM_WRITE]` is
PAGE_COPY (arch/riscv/mm/init.c:376-380), which is PAGE_READ
(arch/riscv/include/asm/pgtable.h:185,192, Linux v6.18.46, commit 1f99e9ab748f).
Decline writable LOAD bytes in the ranges locked before the host; unreadable
headers or arrays and counts outside the existing bounds are left to their gates. -/
def sendmsg_load_free (mp wmp : word → Option byte) (res : List (word × word))
    (msgp : word) : Bool :=
  load_write_free res wmp msgp (Z_to_bv 64 MSGHDR_SIZE)
  && (match copy_bytes_map mp msgp MSGHDR_SIZE with
     | none => true
     | some hdr =>
         let iov := le_bytes_to_word ((hdr.drop 16).take 8)
         let n := le_bytes_to_word ((hdr.drop 24).take 8)
         if bv_unsigned n ≤ IOV_MAX then
           load_write_free res wmp iov (Z_to_bv 64 (16 * bv_unsigned n))
           && (match read_iovecs mp iov n with
              | some ((b0, l0) :: _) =>
                  if !(w_is0 l0) && decide (bv_unsigned l0 ≤ Sys.Uaccess.rw_bytes_max)
                  then load_write_free res wmp b0 l0 else true
              | _ => true)
         else true)

/-- With no LOAD reservations this gate inspects no writable bytes. -/
theorem sendmsg_load_free_nil (mp wmp : word → Option byte) (msgp : word) :
    sendmsg_load_free mp wmp [] msgp = true := by
  unfold sendmsg_load_free
  simp only [load_write_free_nil, Bool.true_and]
  all_goals
    split <;> first | rfl | (split <;> first | rfl | (split <;> simp))

/-- `sendmsg fd msg flags`, in the order `__sys_sendmsg`
(net/socket.c:2700-2718, Linux v6.18.46, commit 1f99e9ab748f) decides it:

- the flag word (`send_flags_modeled`) — THE ARGUMENT, never `msg_flags`:
  `____sys_sendmsg` does `flags |= (msg_sys->msg_flags &
  allowed_msghdr_flags)` (:2589) with `allowed_msghdr_flags` 0 from
  `__sys_sendmsg` (:2717) and then OVERWRITES the field with `flags`
  (:2614), so a `sendmsg(fd, &msg, 0)` whose field says MSG_NOSIGNAL takes
  SIGPIPE.  No field at offset 48 is read below;
- THE FD BEFORE THE HEADER, the opposite of `sendto_spec`: -EBADF and
  -ENOTSOCK (:2709-2715) come before `___sys_sendmsg` (:2670-2689) copies
  anything.
- the 56-byte header: `copy_msghdr_from_user` (net/socket.c:2553-2572,
  v6.18.46)
  copies it whole (:2561-2562), and `copy_from_user` is `access_ok` and
  then the copy (`_inline_copy_from_user`, include/linux/uaccess.h:159-185,
  at :168, v6.18.46), so an unreadable or out-of-range header is -EFAULT
  with nothing ledgered (`State.copy_bytes_map`);
- `__copy_msghdr` (net/socket.c:2507-2551): a non-NULL `msg_name` declines,
  for `sendto_spec`'s reason and because a negative `msg_namelen` beside it
  is -EINVAL (:2523-2524); with `msg_name` NULL the length is forced to 0
  (:2520-2521) and carries no condition; then `msg_iovlen > UIO_MAXIOV` is
  -EMSGSIZE (:2545-2546) on the full 64-bit field, with the header in the
  ledger — `__copy_msghdr`'s errno and NOT writev's -EINVAL.  The decline
  sits ahead of that test because the two orders differ there: Linux
  answers a negative `msg_namelen`'s -EINVAL or an unreadable name's
  -EFAULT (`move_addr_to_kernel`, :2532-2538) before it reads
  `msg_iovlen`, while qemu-user's `do_sendrecvmsg_locked` hands a name
  it cannot lock on as `(void *)-1` (linux-user/syscall.c:3336-3349,
  QEMU 11.1.1), a negative `msg_namelen` reaching it as the host's
  unsigned `socklen_t` (:3337-3338): at -1 the `alloca(msg_namelen + 1)`
  is of 0 bytes and the name's lock asks for 2^32 - 1 (:1687), and at any
  other negative the `alloca` itself asks for more than 2 GiB of stack
  before the lock, a qemu-user defect.  It answers -EMSGSIZE for a count
  over `IOV_MAX` (:3365-3371) before any host call.  Pinned as
  `sendmsg_named_header_over_uio_maxiov_*` and
  `sendmsg_negative_namelen_over_uio_maxiov_*`;
- a count in the heap-backed band `(UIO_FASTIOV, UIO_MAXIOV]`
  (include/uapi/linux/uio.h:45-46, v6.18.46) declines, for
  `Fs.ReadWrite.readv_heap_gap`'s reason: `iovec_from_user`
  (lib/iov_iter.c:1292-1325, v6.18.46) may fail its temporary allocation
  with -ENOMEM before it reads a descriptor;
- the import, `import_iovec` (lib/iov_iter.c:1424-1430), called at
  net/socket.c:2568-2570 — THE SAME PATH writev imports through, so this
  twin imports through `State.import_iovecs`, with its ledger
  `State.import_iovecs_accesses` after the header (see below); an
  -EFAULT qemu-user does not give declines (`iov_fault_at_head`);
- a nonzero `msg_controllen` declines — AFTER the import, because the
  control block is `____sys_sendmsg`'s (:2585-2612), called only once
  `sendmsg_copy_msghdr` (:2650-2668) has returned, so a control block
  beside an over-long `msg_iovlen` is still -EMSGSIZE; the test is on the
  LENGTH (`else if (ctl_len)`, :2599), so a non-NULL `msg_control` with
  length 0 is a plain send;
- a capped total above `Uaccess.rw_bytes_max` declines;
- then the socket (`send_on_socket`), with the header and the descriptors
  as `pre` and the capped vector's prefix ranges as `acc`.
  `security_socket_sendmsg` runs first (`__sock_sendmsg`,
  net/socket.c:737-742, v6.18.46) and can deny; the modeled environment's
  LSMs do not (the LSM note on `sock_fd`).

THE HEADER READ.  Rocq reads the header with `read_bytes_map` and no range
test, the wrapping-walk shape
bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md records;
`State.copy_bytes_map` asks `access_okb` first, as `copy_from_user` does.
qemu-user's -EFAULT for a header ending past `TASK_SIZE` comes from
`do_sendrecvmsg`'s lock (linux-user/syscall.c:3445-3450, QEMU 11.1.1),
and it agrees on a guest with no page there, `iov_fault_at_head`'s first
premise.  Without `-R`, a header whose range wraps 2^64 is refused by the
range test in every configuration (`guest_range_valid_untagged`,
include/user/guest-host.h:116-119, delegating to
`guest_range_valid_untagged_vaddr` at :63-66, QEMU 11.1.1, which
`access_ok_untagged`, linux-user/qemu.h:187-195, asks before
`page_check_range`), so no guest mapping lets it be read; every other
header ending past `TASK_SIZE` is left to `page_check_range`, which
refuses it unless every page of it carries `PAGE_READ`, `VERIFY_READ`
(linux-user/qemu.h:184, QEMU 11.1.1) being the send side's lock, as a
page the guest mapped or `mprotect`ed with `PROT_READ` does until an
`mremap` restamps it (`validate_prot_to_pageflags`,
linux-user/mmap.c:121-124, QEMU 11.1.1; the restamp is on
`recvfrom_spec`), so such a page there lets it be read.
Under `-R` the range test refuses a header ending past `reserved_va`
first.
Rocq reads the six fields with `read_u64` after the whole-header read and
needs an unreachable seventh arm for the total match; the twin decodes
them from the 56 bytes the read returned.

And on a socket too, an `msg_iovlen` from 1 to `IOV_MAX` whose host
vector `lock_iovec`'s `g_try_new0` cannot allocate is -ENOMEM there
(linux-user/syscall.c:3091-3095, QEMU 11.1.1), ahead of every answer
this arm gives after the header read: `iov_fault_at_head`'s second
premise.
The gates Rocq shares are argued
in full on Rocq's `Net.Socket.sendmsg_spec`; the
header read's range test is this twin's,
argued above.

QEMU-USER'S ORDER IS NOT LINUX'S, AND WHERE THE TWO PART THE ARM
DECLINES.  qemu-user resolves no fd itself: `do_sendrecvmsg`
(linux-user/syscall.c:3439-3454, QEMU 11.1.1) locks the header and
`do_sendrecvmsg_locked` (:3327-3437) converts and imports before the
host's sendmsg resolves the fd.  So -EBADF and -ENOTSOCK stand only
where `sendmsg_prehost_quiet` says that path answers nothing first.
On a socket the Linux order is kept, and the import's answers are
kept where qemu-user's `lock_iovec` (:3072-3158) gives them too:
-EFAULT under `iov_fault_at_head`, -EINVAL under `iov_inval_at_head`.
A vector Linux imports whole is declined unless `iovs_lockable`:
`lock_iovec` faults or truncates on a segment it cannot lock, where
Linux answers by the socket's state or moves a readable prefix.  The
premises the kept -EFAULTs rest on are `iov_fault_at_head`'s.  No
example constructs a `sendmsg` call, so these declines cost
`Equivalence.strong_equiv` no theorem. -/
def sendmsg_spec (fd msgp flags : word) : Sys SyscallEffect :=
  if ¬ (send_flags_modeled flags) then unmodeled
  else
  i <- input ;;
  m <- get_model ;;
  if !(sendmsg_load_free i.in_mem i.in_wmem (m_vmmaps m).vm_reserved msgp) then unmodeled
  else
  match fd_lookup (m_fds m) fd with
  | none => if sendmsg_prehost_quiet i.in_mem msgp then err_ret EBADF else unmodeled
  | some (.FdChannel _) => if sendmsg_prehost_quiet i.in_mem msgp then err_ret ENOTSOCK else unmodeled
  | some (.FdFile _ _) => if sendmsg_prehost_quiet i.in_mem msgp then err_ret ENOTSOCK else unmodeled
  | some (.FdFileW _ _) => if sendmsg_prehost_quiet i.in_mem msgp then err_ret ENOTSOCK else unmodeled
  | some (.FdFileA _ _) => unmodeled -- declined: see the file header
  | some (.FdFileRW _ _) => unmodeled -- declined: see the file header
  | some .FdDir => if sendmsg_prehost_quiet i.in_mem msgp then err_ret ENOTSOCK else unmodeled
  | some (.FdPipe _ _) => if sendmsg_prehost_quiet i.in_mem msgp then err_ret ENOTSOCK else unmodeled   -- pipeanon_fops is not socket_file_ops
  | some (.FdDevNull _ _) => if sendmsg_prehost_quiet i.in_mem msgp then err_ret ENOTSOCK else unmodeled
  | some .FdUrandom => if sendmsg_prehost_quiet i.in_mem msgp then err_ret ENOTSOCK else unmodeled
  | some (.FdSocket sk) =>
      match copy_bytes_map i.in_mem msgp MSGHDR_SIZE with
      | none => err_ret EFAULT                -- copy_from_user of the header
      | some hdr =>
          let name := le_bytes_to_word (hdr.take 8)
          let iov := le_bytes_to_word ((hdr.drop 16).take 8)
          let iovlen := le_bytes_to_word ((hdr.drop 24).take 8)
          let ctllen := le_bytes_to_word ((hdr.drop 40).take 8)
          if ¬ (w_is0 name) then unmodeled
          else if IOV_MAX < bv_unsigned iovlen
          then record_copyins [(msgp, MSGHDR_SIZE.toNat)] (err_ret EMSGSIZE)
          else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen then unmodeled
          else
            match import_iovecs i.in_mem iov iovlen with
            | .ImpFault =>
                if ¬ (iov_fault_at_head i.in_mem iov iovlen) then unmodeled   -- qemu-user skips it
                else
                record_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                                ++ import_iovecs_accesses i.in_mem iov iovlen)
                  (err_ret EFAULT)              -- the array, or descriptor 0's range
            | .ImpInval =>
                if ¬ (iov_inval_at_head i.in_mem iov iovlen) then unmodeled
                else
                record_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                                ++ import_iovecs_accesses i.in_mem iov iovlen)
                  (err_ret EINVAL)              -- iov_len negative as ssize_t
            | .ImpOk iovs0 =>
                if ¬ (w_is0 ctllen) then unmodeled       -- ancillary data
                else if ¬ (iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max)
                then unmodeled                            -- see `Uaccess.rw_bytes_max`
                else if ¬ (iovs_lockable i.in_mem i.in_wmem (m_vmmaps m).vm_reserved iovs0) then unmodeled
                else
                  send_on_socket
                    ([(msgp, MSGHDR_SIZE.toNat)] ++ import_iovecs_accesses i.in_mem iov iovlen)
                    (fun n => iov_prefix_accesses (cap_iovecs iovs0) n) fd sk
                    (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
                    (writev_gathered i.in_mem iovs0) m

/-! ## The descriptor gate the two recv calls end at -/

/-- The descriptor gate of `__sys_recvfrom` (net/socket.c:2270-2304, at
:2285-2291, Linux v6.18.46, commit 1f99e9ab748f) and of `__sys_recvmsg`
(net/socket.c:2909-2927, at :2918-2924): -EBADF when the descriptor is not
open, -ENOTSOCK when it is open and not a socket, because `sock_from_file`
(net/socket.c:530-536) is one comparison against `socket_file_ops`.  A
SOCKET is `none`: both entry points decline it (`recvfrom_spec`).  Spelled
out constructor by constructor, as Rocq spells it, so a new `FdEntry`
constructor stops the build here instead of inheriting an answer.
Rocq: `Net.Socket.sockfd_lookup_errno`. -/
def sockfd_lookup_errno (fds : List (word × FdEntry)) (fd : word) : Option Int :=
  match fd_lookup fds fd with
  | none => some EBADF
  | some (.FdChannel _) => some ENOTSOCK
  | some (.FdFile _ _) => some ENOTSOCK
  | some (.FdFileW _ _) => some ENOTSOCK
  | some (.FdFileA _ _) => some ENOTSOCK
  | some (.FdFileRW _ _) => some ENOTSOCK
  | some .FdDir => some ENOTSOCK
  | some (.FdPipe _ _) => some ENOTSOCK       -- pipeanon_fops
  | some (.FdDevNull _ _) => some ENOTSOCK    -- null_fops
  | some .FdUrandom => some ENOTSOCK          -- urandom_fops
  | some (.FdSocket _) => none

/-- That answer as a spec: the errno, or the decline a socket takes, as a
whole branch and never under an `alt`, so `Ok` and `Unmodeled` are never
both outcomes at one input.  Rocq: `Net.Socket.recv_fd_answer`. -/
def recv_fd_answer (fds : List (word × FdEntry)) (fd : word) : Sys SyscallEffect :=
  match sockfd_lookup_errno fds fd with
  | some e => err_ret e
  | none => unmodeled

/-! ## socketpair (199)

On the Linux AF_INET path reaching `sock_no_socketpair`, two descriptor
numbers have been written into `usockvec`.  `inet_stream_ops`,
`inet_dgram_ops` and `inet_sockraw_ops` all set `.socketpair =
sock_no_socketpair` (net/ipv4/af_inet.c:1055, :1090, :1122, Linux v6.18.46,
commit 1f99e9ab748f), and `sock_no_socketpair` (net/core/sock.c:3444-3447)
is `return -EOPNOTSUPP;`.  `__sys_socketpair` (net/socket.c:1769)
reaches it (:1828) only after `put_user(fd1, &usockvec[0])` (:1798-1800) and
`put_user(fd2, &usockvec[1])` (:1802-1804) have both run, and its `out:`
label (:1855-1858) then does `put_unused_fd` on both — so the call returns
-EOPNOTSUPP with two CLOSED descriptor numbers already stored in the
caller's array. -/

/-- `type` is an `int`, so only its low 32 bits reach the kernel
(`Syscall.abi_low32`); `flags = type & ~SOCK_TYPE_MASK; if (flags &
~(SOCK_CLOEXEC | SOCK_NONBLOCK)) return -EINVAL;` (`__sys_socketpair`,
net/socket.c:1776-1778, Linux v6.18.46, commit 1f99e9ab748f) is the first
test of the call, ahead of both descriptor reservations.  Unlike `socket`,
SOCK_NONBLOCK is NOT declined here: the call fails for every modeled triple
before either flag reaches a file.  Rocq:
`Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
(Z.lor SOCK_CLOEXEC SOCK_NONBLOCK) = 0`. -/
def socketpair_flags_ok (type : word) : Bool :=
  bv_unsigned (bv_and (bv_and (abi_low32 type) (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
                      (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0

/-- The socket type after `type &= SOCK_TYPE_MASK` (`__sys_socketpair`,
net/socket.c:1779, Linux v6.18.46, commit 1f99e9ab748f) — what
`sock_create` sees, and always in `[0, 15]`.  Rocq:
`Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK`. -/
def socketpair_base_type (type : word) : Int :=
  bv_unsigned (bv_and (abi_low32 type) (Z_to_bv 64 SOCK_TYPE_MASK))

/-- The (family, type, protocol) triples the model judges: AF_INET with
SOCK_STREAM or SOCK_DGRAM at the default protocol.  Both reach
`inet_create` (net/ipv4/af_inet.c:254, Linux v6.18.46, commit
1f99e9ab748f) and succeed there, so both arrive at
`sock1->ops->socketpair` and both are the -EOPNOTSUPP below.  Everything
else is declined, and each exclusion is a kernel fact: AF_UNIX SUCCEEDS and
hands back a PAIR of sockets connected to each other, which
`State.SockState` cannot express; SOCK_RAW reaches `inet_create`'s
CAP_NET_RAW test (:315-318), which the model does not track; a nonzero
protocol reaches its range test (:265-266) and `inetsw` match (:272-291)
and can answer -EINVAL or -EPROTONOSUPPORT, and a masked type outside
{1, 2} can answer -EINVAL or -ESOCKTNOSUPPORT — all AFTER both writes have
landed, three more errnos for shapes no program issues.  Argument on Rocq's
`Net.Socket.socketpair_modeled_b`. -/
def socketpair_modeled_b (family type protocol : word) : Bool :=
  (bv_unsigned (abi_low32 family) = AF_INET)
  && (socketpair_base_type type = SOCK_STREAM || socketpair_base_type type = SOCK_DGRAM)
  && (bv_unsigned (abi_low32 protocol) = 0)

/-- The two descriptors `__sys_socketpair` reserves — two calls of
`get_unused_fd_flags` (fs/file.c:620, v6.18.46), which `__sys_socketpair` makes at
net/socket.c:1788 and :1792 (Linux v6.18.46, commit 1f99e9ab748f) —
or `none` when `State.alloc_fd`'s scan bound is exhausted — the same
unreachable case the fd allocator's freeness test exists for, answered by
declining rather than by inventing a number.  Both are reserved before
either is written, so the second is the lowest free descriptor ABOVE the
first (`State.alloc_fd2`).  Rocq: `Net.Socket.socketpair_fds`. -/
def socketpair_fds (fds : List (word × FdEntry)) : Option (word × word) :=
  match fd_lookup fds (alloc_fd fds), fd_lookup fds (alloc_fd2 fds) with
  | none, none => some (alloc_fd fds, alloc_fd2 fds)
  | _, _ => none

/-- The two `put_user(fd, &usockvec[k])` stores (net/socket.c:1798 and
:1802, Linux v6.18.46, commit 1f99e9ab748f): two separate 4-byte
little-endian `int` writes, at `sv` and `sv + 4`, in that order.  Each is a
single store with an extable fixup on riscv64 (`__put_user`,
arch/riscv/include/asm/uaccess.h:377-390, v6.18.46), so an `int` write is
all-or-nothing.  Rocq: `Net.Socket.socketpair_writes`. -/
def socketpair_writes (sv fd1 fd2 : word) : List (word × List byte) :=
  [(sv, word_le4 fd1), (sv + Z_to_bv 64 4, word_le4 fd2)]

/-- The errnos socketpair can return BEFORE either `put_user` runs, so with
`usockvec` untouched: the two reservations `__sys_socketpair` makes (net/socket.c:
1788-1796, Linux v6.18.46, commit 1f99e9ab748f) through `get_unused_fd_flags`
(fs/file.c:620, v6.18.46), which fail with -EMFILE
past RLIMIT_NOFILE or sysctl_nr_open (`alloc_fd`, fs/file.c:570, at
:591) and with -ENOMEM on a failed table expansion (`alloc_fdtable`,
fs/file.c:162, v6.18.46, at :242).  Neither condition is one this model tracks,
so both are offered as environment choices.  Rocq:
`Net.Socket.socketpair_reserve_errnos`. -/
def socketpair_reserve_errnos : List Int := [EMFILE, ENOMEM]

/-- The errnos it can return AFTER both writes have landed, for the modeled
triples: -ENFILE when `sock_alloc` cannot take a sockfs inode
(`__sock_create`, net/socket.c:1570-1575, at :1573, Linux v6.18.46, commit
1f99e9ab748f) and -ENOMEM when `sk_alloc` fails inside `inet_create`
(net/ipv4/af_inet.c:327-330).  They carry the writes, because the writes
came first.  The two LSM hooks on that path — security_socket_create inside each
creation (net/socket.c:1561, v6.18.46) and security_socket_socketpair
(net/socket.c:1821) — can answer -EACCES with `usockvec` already written;
this set does not allow that, which makes the model NARROWER than Linux
here and never wider (bugs/socketpair-lsm-denials-not-admitted.md).  The
-ENOMEM is version-dependent: `inet_create` set `err = -ENOBUFS` before
its `sk_alloc` through v5.13 (read at v4.19, v5.10 and v5.13; v5.14 is the
first with -ENOMEM), and README's floor is v4.17, so the 4.19.y, 5.4.y and
5.10.y stable kernels answer -ENOBUFS where this set has only -ENOMEM.
Neither errno
register defines ENOBUFS yet, so widening the set is a base change on both
sides; Rocq's `socketpair_create_errnos` shares the gap, and its prose
places the window at v6.10-v6.15, which README does not.  Rocq:
`Net.Socket.socketpair_create_errnos`. -/
def socketpair_create_errnos : List Int := [ENFILE, ENOMEM]

/-- The outcome once the 8-byte destination is known writable: a
reservation errno with `usockvec` untouched, or the two writes carrying
-EOPNOTSUPP or one of the post-write errnos.  Rocq:
`Net.Socket.socketpair_written`. -/
def socketpair_written (sv fd1 fd2 : word) : Sys SyscallEffect :=
  alt (e <- errno_from socketpair_reserve_errnos ;; err_ret e)
      (alt (e <- errno_from socketpair_create_errnos ;;
            Monad.pure (mkEffect (errno_ret e) (socketpair_writes sv fd1 fd2) []))
           (Monad.pure (mkEffect (errno_ret EOPNOTSUPP) (socketpair_writes sv fd1 fd2) [])))

/-- The outcome once the FIRST `put_user`'s own 4-byte range is one every
riscv64 `access_ok` refuses: that store fails, so -EFAULT joins the two
reservation errnos and nothing is written on any path.  Rocq:
`Net.Socket.socketpair_faulted`. -/
def socketpair_faulted : Sys SyscallEffect :=
  alt (e <- errno_from socketpair_reserve_errnos ;; err_ret e) (err_ret EFAULT)

/-- WHEN BOTH `put_user`s ARE KNOWN TO LAND: the whole 8-byte destination
passes riscv64's own `access_ok` AND is mapped end to end.  Both conjuncts
are needed and neither implies the other.  The first is the one worth
explaining: `State.read_bytes_map` advances in WORD arithmetic and wraps at
`2^64`, so a destination in the last seven bytes of the address space walks
off the top, comes back at 0, and reads in full — while Linux answers
-EFAULT there and writes nothing: `put_user` on riscv64 is `access_ok(p,
sizeof *p) ? __put_user(x, p) : -EFAULT` (arch/riscv/include/asm/uaccess.h:
408-415, Linux v6.18.46, commit 1f99e9ab748f), `access_ok` is
`__access_ok(untagged_addr(addr), size)` (:42), and `__access_ok`
(include/asm-generic/access_ok.h:31-41) is `(size <= limit) && (addr <=
(limit - size))` (:40) with `limit = TASK_SIZE_MAX` — written as a
SUBTRACTION, so the wrapping sum is never formed.  `State.access_okb` is
that predicate over the kernel of record's `TASK_SIZE`.  THE WIDTH IS 8,
NOT 4: this conjunct guards the arm that says BOTH stores landed, so it is
the conjunction of both stores' own `access_ok` calls, which
`access_okb_both_stores` below proves rather than a sentence asserting it.
Argument on Rocq's `Net.Socket.socketpair_dest_writable`, including why the
guard sits at the caller rather than on `read_bytes_map`. -/
def socketpair_dest_writable (mp : word → Option byte) (sv : word) : Bool :=
  access_okb sv 8
  && (match read_bytes_map mp sv (Z_to_bv 64 8) with
      | some _ => true
      | none => false)

/-- THE WIDTH, AS A CHECK.  The two `put_user`s carry separate `access_ok`
calls over their own 4-byte ranges, at `sv` and at the WORD sum `sv + 4`;
`access_okb sv 8` is their conjunction at every `sv`, the wrapping ones
included.  What the lemma buys is the step the wrap makes non-obvious:
`access_okb (sv + 4) 4` ON ITS OWN is true for a wrapping `sv` (at `2^64 -
4` the second store's address is 0, which every `access_ok` accepts); what
rules the wrap out is the FIRST store's test.  Holds for any limit in
`[8, 2^64)`, so it survives a change to `State.TASK_SIZE`.  Twin of Rocq's
`Net.Socket.access_okb_both_stores`. -/
theorem access_okb_both_stores (sv : word) :
    (access_okb sv 4 && access_okb (sv + Z_to_bv 64 4) 4) = access_okb sv 8 := by
  have h4 : (Z_to_bv 64 4 : word).toNat = 4 := by decide
  have hsum : (sv + Z_to_bv 64 4).toNat = (sv.toNat + 4) % 2 ^ 64 := by
    rw [BitVec.toNat_add, h4]
  have hlt : sv.toNat < 2 ^ 64 := sv.isLt
  -- Both sides as propositions first: the `decide` instances depend on the
  -- terms, so the wrapped sum can only be rewritten once they are gone.
  unfold access_okb
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  simp only [bv_unsigned, TASK_SIZE]
  rw [hsum]
  by_cases hw : sv.toNat + 4 < 2 ^ 64
  · -- the first store passes, so `sv + 4` did not wrap
    rw [Nat.mod_eq_of_lt hw]
    constructor
    · intro h; omega
    · intro h; omega
  · -- the first store is refused, and so is the 8-byte range
    simp only [Nat.reducePow] at hw hlt ⊢
    constructor
    · intro h; omega
    · intro h; omega

/-- `socketpair family type protocol usockvec` (see the section header for
the kernel path).
An unknown type-flag bit is declined before reservations or writes.
Linux v6.18.46 net/socket.c `__sys_socketpair` (:1776-1778) returns
-EINVAL before either `put_user`. QEMU 11.1.1 linux-user/syscall.c
`target_to_host_sock_type` (:3183-3215) drops the bit; `do_socketpair`
(:3618-3633) ignores that helper's result, calls the host with the
stripped word into a local tab[2], and copies to the guest only on
success. Thus AF_INET STREAM with bit 8 set can answer -EOPNOTSUPP
with nothing written under qemu-user. The whole unknown-bit class is
declined; keeping this gate first prevents a later answer from bypassing
Linux's initial -EINVAL. The equivalence theorem loses modeled coverage
at these arguments; the examples do not construct them.

An unmodeled triple declines before either write; then the destination
decides: known writable, both stores land
(`socketpair_written`); the FIRST store's own 4-byte range refused by
`access_ok`, nothing is written (`socketpair_faulted`); and the band in
between — `sv` in `[TASK_SIZE - 7, TASK_SIZE - 4]`, where the first store
passes its own test and the second is refused, or a destination that is
in range but not wholly mapped — is a PARTIAL outcome this model does not
express (Linux stores `fd1` if that page is mapped and nothing if it is
not), so it declines rather than guesses.  The 4 in the second test IMPLIES
the 8 in the first, so the faulted arm answers a strict subset of the
ranges it would otherwise: a narrowing in the fail-closed direction.
Argument on Rocq's `Net.Socket.socketpair_spec`. -/
def socketpair_spec (family type protocol sv : word) : Sys SyscallEffect :=
  if ¬ (socketpair_flags_ok type) then unmodeled
  else if ¬ (socketpair_modeled_b family type protocol) then unmodeled
  else
  i <- input ;;
  m <- get_model ;;
  match socketpair_fds (m_fds m) with
  | none => unmodeled                      -- the allocator's scan bound exhausted: fail closed
  | some (fd1, fd2) =>
      if socketpair_dest_writable i.in_wmem sv
      then socketpair_written sv fd1 fd2
      else if ¬ (access_okb sv 4) then socketpair_faulted
      else unmodeled                       -- destination neither known-writable nor known-refused

/-! ## recvfrom (207), recvmsg (212)

Both entry points DECLINE A SOCKET, and the reason is here because a bare
decline reads as a bigger claim than it is: it declines these two entry
points, not socket reading — `read` and `readv` on a connected socket are
modeled (`Fs.ReadWrite.read_spec`), so a program that reads its socket
with `read` stays inside the surface.  Nor is it `read`'s arm under
another name, which is what makes modeling it real work rather than an
alias: `sock_read_iter` (net/socket.c:1154-1174, Linux v6.18.46, commit
1f99e9ab748f) answers a zero-length read 0 before the protocol (:1168-1169,
"Match SYS5 behaviour"), and `__sys_recvfrom` has no such short-circuit,
while `tcp_recvmsg_locked` (net/ipv4/tcp.c:2634-2910, v6.18.46) takes its
`target` at :2685 from `sock_rcvlowat` (include/net/sock.h:2672-2677,
v6.18.46), which ends `return v ?: 1;`, so a never-connected socket falls
to the TCP_CLOSE arm's -ENOTCONN (:2752-2756) at length 0: `read(s, buf,
0)` is 0 where `recv(s, buf, 0, 0)` is -ENOTCONN on the same socket.  No
modeled program is shut out: Rocq's `Net.Socket.recvfrom_spec` walks the
one caller that would reach them, musl's resolver, and shows it never
obtains the descriptor, because `socket_spec` declines SOCK_DGRAM. -/

/-- `recvfrom fd ubuf size flags src_addr addrlen`.  `__sys_recvfrom`
(net/socket.c:2270-2304, Linux v6.18.46, commit 1f99e9ab748f) opens with
`import_ubuf(ITER_DEST, …)` (:2281-2283; lib/iov_iter.c:1433-1442,
v6.18.46), so THE BUFFER IS VALIDATED BEFORE THE DESCRIPTOR IS RESOLVED
(:2285-2291) and `recvfrom(-1, <kernel address>, 1, 0, NULL, NULL)` is
-EFAULT rather than -EBADF — the opposite of `recvmsg_spec`'s order.  The
verdict is `Uaccess.access_ok_zero`, exact for a call that moves no bytes:
`import_ubuf`'s `access_ok` and nothing else, after its cap to
MAX_RW_COUNT (:1435-1436), which no count below `Uaccess.rw_bytes_max`
reaches.

THE OTHER THREE ARGUMENTS ARE NOT READ, a kernel fact rather than an
omission: `__sys_recvfrom` validates no flag, and `src_addr`/`addrlen` are
touched only by the `move_addr_to_user` under `err >= 0 && addr != NULL`
(:2297-2302), unreachable when the descriptor is not a socket.  They
become live with the socket arm, and `sockfd_lookup_errno`'s enumerated
match is what makes that a build failure rather than an inherited answer.
That is Linux's fact and not qemu-user's: `do_recvfrom`
(linux-user/syscall.c:3683-3741, QEMU 11.1.1) locks the destination
(:3692-3699) and, with `src_addr` non-NULL, reads `*addrlen` (:3700-3708)
before the host call, so on a non-socket fd, wherever `access_ok_zero`
passes the destination, a non-NULL, in-range destination of nonzero
length it cannot lock, an unreadable `addrlen` or a negative one is
-EFAULT or -EINVAL there and -EBADF or -ENOTSOCK here.  Where a count
`modeled_rw_count` admits reaches `access_ok_zero` and it refuses the
destination, the answer here is its -EFAULT on every fd, and qemu-user's
lock passes a zero-length one past `TASK_SIZE` wherever `buf` is at most
`guest_addr_max` and `g2h(buf)` is not NULL (below), so there, with
`src_addr` non-NULL, a negative `*addrlen` is qemu-user's -EINVAL before
any host call (:3705-3707), a residual like the ones above, and an
unreadable one its -EFAULT (:3701-3703), as here.
Beside a NULL `src_addr`, or a readable and nonnegative `*addrlen` short
of one too large for the host stack `do_recvfrom` `alloca`s it on
(linux-user/syscall.c:3709, QEMU 11.1.1: nothing bounds it first, and a
larger one overflows that stack before any host call, a qemu-user defect,
as `sendmsg_spec`'s `alloca(msg_namelen + 1)` is), a NULL destination is
never locked (linux-user/syscall.c:3692-3693, QEMU 11.1.1), so it reaches
the host's recvfrom, whose -EBADF or -ENOTSOCK on that fd is the answer
here too.  Call that condition on `src_addr` and `*addrlen` the `addrlen`
condition: every sentence below that has a destination reach the host's
recvfrom holds only under it, since past a destination lock that passes,
a non-NULL `src_addr` beside an unreadable or negative `*addrlen` is
qemu-user's -EFAULT or -EINVAL before any host call
(linux-user/syscall.c:3700-3708, QEMU 11.1.1), and beside one too large
for the host stack the `alloca` overflows it.  A
zero-length destination is tested against `guest_addr_max` alone, whatever
its mapping (linux-user/qemu.h:189-190; accel/tcg/user-exec.c:502-504,
QEMU 11.1.1).
At or below `TASK_SIZE`, where the answer here is the fd's, it reaches
the host's recvfrom under the `addrlen` condition and gets that answer
wherever `buf` is at most
`guest_addr_max` and `g2h(buf)` lies inside the host's user range; the
inputs where either fails, and those past `TASK_SIZE`, are taken up
below.  A NONZERO destination ending past `TASK_SIZE`, -EFAULT here, is -EFAULT
there on a guest with no page past it, the premise `iov_fault_at_head`
states, outside `page_check_range`'s hole below, a qemu-user defect that
can pass a destination ending in the first page past `TASK_SIZE`.  Without
`-R`, a destination whose
range wraps 2^64 is refused by the range test in every configuration
(`guest_range_valid_untagged`, include/user/guest-host.h:116-119,
delegating to `guest_range_valid_untagged_vaddr` at :63-66, QEMU 11.1.1,
which `access_ok_untagged`, linux-user/qemu.h:187-195, asks before
`page_check_range`); every other one is left to `page_check_range`, which
refuses it unless every page of it carries `PAGE_READ` and either
`PAGE_WRITE` or `PAGE_WRITE_ORG`, except that the range's last page is
never examined when the loop has called `page_unprotect` on every page
before it in turn, from `buf`'s on, and the range's last byte lies at a
lower in-page offset than `buf` (accel/tcg/user-exec.c:549-558,
QEMU 11.1.1: each unprotect advances `start` one page keeping that offset,
and `last - start < TARGET_PAGE_SIZE` then accepts), a defect against
its own contract, "Return false if any page is unmapped"
(include/user/page-protection.h:48-49, QEMU 11.1.1).  So outside that hole
only such pages there reach the host's answer on the fd; under `-R` the
range test refuses a destination ending past `reserved_va` first.  On a
non-socket fd a non-NULL, nonzero-length, in-range destination
`page_check_range` refuses is -EFAULT there and -EBADF or -ENOTSOCK here
as well.  The lock is `VERIFY_WRITE` (linux-user/syscall.c:3695,
QEMU 11.1.1), `PAGE_READ | PAGE_WRITE` (linux-user/qemu.h:185, QEMU 11.1.1).
Wherever it examines a page, `page_check_range` refuses one without
`PAGE_READ` outright (accel/tcg/user-exec.c:538-541, QEMU 11.1.1), and one
without `PAGE_WRITE` unless it carries `PAGE_WRITE_ORG`, which `page_unprotect` turns back into
`PAGE_WRITE` and accepts (accel/tcg/user-exec.c:543-552, QEMU 11.1.1).
`tb_lock_page0` clears `PAGE_WRITE`, keeping `PAGE_WRITE_ORG`, on a
writable page code is translated from and, on a host whose page is larger
than the target's, on every writable target page sharing that host page
(accel/tcg/user-exec.c:632-638, :654-655, QEMU 11.1.1).  `mmap` and
`mprotect` set a page's flags from its `PROT_READ`, `PROT_WRITE` and
`PROT_EXEC` bits and `PAGE_VALID` (`validate_prot_to_pageflags`,
linux-user/mmap.c:121-124, called at :191 and :977, QEMU 11.1.1),
replacing the old ones (:273, :576-585), and `page_set_flags` adds
`PAGE_WRITE_ORG` beside a `PAGE_WRITE` it sets and clears it beside one it
clears (accel/tcg/user-exec.c:476-481, QEMU 11.1.1), so, outside that
hole, a page mapped or `mprotect`ed without `PROT_READ` is refused, and so
is one without `PROT_WRITE`, until an `mremap` covers it: `target_mremap` reads the
first old page's flags (linux-user/mmap.c:1164, :1248, QEMU 11.1.1) and
stamps them over the whole new range (:1169-1170, :1251-1252), even for
an `mremap(p, n, n, 0)` that Linux answers with `p` without moving
anything (`mremap_at`, mm/mremap.c:1557-1559, v6.18.46), and a page
mapped read-write is refused after an `mremap` whose first old page is
read-only.  That stamp is a qemu-user defect no state the model reaches
has, since `mremap_spec` declines every flag word but `MREMAP_MAYMOVE`
and any source not wholly a read-write anonymous mapping
(`mremap_source_b`, Sys/Mm/Mremap.lean); it is why qemu-user's locks are
stated here in page flags rather than `PROT_*` bits.  And a ZERO-LENGTH
destination past `TASK_SIZE`, -EFAULT here from `access_ok_zero`, passes
qemu-user's range and page tests wherever `buf` is at most
`guest_addr_max`: `access_ok_untagged` (linux-user/qemu.h:187-195,
QEMU 11.1.1) tests it only against `guest_addr_max`, `~0ul` for riscv64
without `-R` and `reserved_va` under it (linux-user/main.c:847-853,
QEMU 11.1.1), which riscv64 lets reach `2^48 - 1`, past `TASK_SIZE`
(`MAX_RESERVED_VA`, linux-user/main.c:109-120 and :839-842;
target/riscv/cpu-param.h:11-12; QEMU 11.1.1), and `page_check_range` of
length 0 is true (accel/tcg/user-exec.c:502-504, QEMU 11.1.1).
`lock_user` then returns `g2h(buf)`, `buf` plus `guest_base` with no wrap
check (`g2h_untagged`, linux-user/uaccess.c:16 and
include/user/guest-host.h:48-51, QEMU 11.1.1), which is NULL where `buf`
is `2^64 - guest_base` for a nonzero `guest_base`; there `do_recvfrom`
answers -EFAULT (linux-user/syscall.c:3695-3697, QEMU 11.1.1), as here.
Everywhere else the host is handed `g2h(buf)`, and not the NULL
`do_sendto` passes for a zero length (linux-user/syscall.c:3648,
QEMU 11.1.1), so the host's
own `import_ubuf` range test, reached through `safe_recvfrom`
(linux-user/syscall.c:3711 or :3716, QEMU 11.1.1), runs before the fd:
under the `addrlen` condition qemu-user answers what the host's recvfrom
answers on that fd only where `g2h(buf)` lies inside the host's user
range, and -EFAULT like here otherwise.  On x86-64 that range is
`__access_ok`'s `valid_user_address` (arch/x86/include/asm/uaccess_64.h:56-57,
:98-107, v6.18.46) against the `USER_PTR_MAX` `arch_cpu_finalize_init` sets
(arch/x86/kernel/cpu/common.c:2592, v6.18.46): `2^47 - 4096` with 4-level
paging, `2^56 - 4096` under LA57.  On arm64 it is `access_ok`
(arch/arm64/include/asm/uaccess.h:38-50, v6.18.46) against `TASK_SIZE_MAX`
(arch/arm64/include/asm/processor.h:57, v6.18.46), `2^48` at 48-bit VA and
`2^39` at 39-bit.  So, with `guest_base` 0, under the `addrlen` condition and
wherever `buf` is at most `guest_addr_max`, an LA57
x86-64 host gives the fd's answer on `(2^47, 2^56 - 4096]` and a 48-bit arm64 one on
`(2^47, 2^48]`, where this is -EFAULT.  Conversely, at or below
`TASK_SIZE` a zero-length destination is -EFAULT there and the fd's answer
here wherever `buf` is past `guest_addr_max` (`reserved_va` under `-R`,
linux-user/main.c:847-848, QEMU 11.1.1), or, under the `addrlen`
condition, `g2h(buf)` is past the host's range: with `guest_base` 0, `(2^47 - 4096, 2^47]` on a 4-level x86-64 host
and `(2^39, 2^47]` on a 39-bit arm64 one.
bugs/read-write-transfer-answers-are-linux-order-not-qemu-user.md records
the `-R` half of this zero-count shape for `read` and `write`.  All of these
are Rocq's answers, reported to the lead rather than declined; the destination ones are pinned in
Checks/Cases/Net/Socket.lean beside `recvfrom_unmapped_buffer_efault_rejected`.
Rocq binds the input here and never reads it; the twin does not bind it.
Rocq: `Net.Socket.recvfrom_spec`. -/
def recvfrom_spec (fd buf size : word) : Sys SyscallEffect :=
  if ¬ (Sys.Uaccess.modeled_rw_count size) then unmodeled   -- see `Uaccess.rw_bytes_max`
  else
  m <- get_model ;;
  Sys.Uaccess.access_ok_zero buf size (recv_fd_answer (m_fds m) fd)

/-- `recvmsg fd msg flags`.  `__sys_recvmsg` (net/socket.c:2909-2927,
Linux v6.18.46, commit 1f99e9ab748f) tests `forbid_cmsg_compat && (flags &
MSG_CMSG_COMPAT)` (:2915-2916), which `SYSCALL_DEFINE3(recvmsg)`
(:2929-2933) calls with `true`, then resolves the descriptor (:2918-2924)
and only then calls `___sys_recvmsg` (:2926), which copies the header.
So THE DESCRIPTOR IS RESOLVED BEFORE THE HEADER IS READ: `recvmsg(-1,
<kernel address>, 0)` is -EBADF, `recvmsg(<open file>, <kernel address>,
0)` is -ENOTSOCK, the 56-byte `struct user_msghdr` is never touched, and
the dispatcher does not bind `msg`.  That is Linux v6.18.46's order and not
qemu-user's, which checks no fd first; QEMU 11.1.1 throughout.
`do_sendrecvmsg` (linux-user/syscall.c:3439-3454) locks the header for
writing, and `do_sendrecvmsg_locked` (:3327-3437) then imports the vector
before the host call resolves the fd, so on a closed or non-socket fd,
where this arm answers -EBADF or -ENOTSOCK, qemu-user answers:

- -EFAULT beside a header it cannot lock for writing (:3445-3450), which
  `page_check_range` decides as `recvfrom_spec` says, `VERIFY_WRITE`
  being `PAGE_READ | PAGE_WRITE` (linux-user/qemu.h:185, QEMU 11.1.1), so
  both of the calls above are -EFAULT there wherever no guest page maps
  the kernel address;
- -EMSGSIZE beside an `msg_iovlen` over `IOV_MAX`
  (linux-user/syscall.c:3365-3371);
- -ENOMEM beside an `msg_iovlen` from 1 to `IOV_MAX` whose host vector
  `lock_iovec`'s `g_try_new0` cannot allocate (:3091-3095), before the
  array lock;
- -EFAULT beside an iov array it cannot lock (`lock_iovec`, :3072-3158,
  at :3097-3102);
- -EINVAL beside a negative `iov_len` (:3113-3115);
- -EFAULT beside a nonzero descriptor 0 it cannot lock, `VERIFY_WRITE`
  here (:3373-3374, :3120, :3125-3128);
- 0 beside an `msg_iovlen` of 0: `lock_iovec` returns NULL with `errno`
  0 (:3082-3085), and `do_sendrecvmsg_locked`'s test `!send || ret`
  (:3378) sends every receive to `out2`, which returns that 0 without a
  host call (:3375-3380); the pass-through for a packet without any iov
  that its comment states (:3377) is taken by sends alone, and readv and
  writev return the same 0 for a zero count (:11886-11907).

Each is Rocq's answer too, reported to the lead rather than declined.

MSG_CMSG_COMPAT DECLINES because its value is a configuration fact:
`0x80000000` under CONFIG_COMPAT and `0` without it
(include/linux/socket.h:337-341, v6.18.46; `Uapi.MSG_CMSG_COMPAT`), so the
bit is -EINVAL on one riscv64 kernel and inert on another, and nothing a
binary observes says which.  It is tested on the low 32 bits, `flags`
being `unsigned int`.  Rocq: `Net.Socket.recvmsg_spec`. -/
def recvmsg_spec (fd flags : word) : Sys SyscallEffect :=
  if ¬ (bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = 0)
  then unmodeled   -- CONFIG_COMPAT decides this one: fail closed
  else
  m <- get_model ;;
  recv_fd_answer (m_fds m) fd

end LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket
