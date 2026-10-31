-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Fs/Ioctl.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Sys.Fs.Ioctl — ioctl (29)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Ioctl.v`, which answers to Linux
`fs/ioctl.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The Rocq header reads the kernel over a v5.15–v6.14 window and quotes no
line numbers — only Rocq's `ioctl_spec` arm comments do, fs/pipe.c:619 and
:653-654 for the pipe end, re-checked at v6.18.46 with its `/dev/null` and
`/dev/urandom` arms; every number below was read at v6.18.46, where
`vfs_ioctl` has the `int` return type the Rocq header says v6.15 gave it
and otherwise the body it quotes.

The enumeration in `ioctl_spec` names every kind, as Rocq's does (the
Rocq docstring on `ioctl_spec` says why a wildcard would be wrong).  That
is how the eighth kind arrived: #712 gave both trees `FdUrandom`, the
match stopped the build, and the arm below was written against the
driver's own handler.  The baseline names the day tip because the day
branch was rewritten under this port: the Rocq file it mirrors last
changed in #794's squash of the 2026-09-11 work (the `FdUrandom` arm),
and reads the same at the tip.

FDFILERW, FDFILEA AND FDDEVNULL ANSWER -ENOTTY, as Rocq's arm does.  An
earlier state of this file declined all three and gated the whole spec on
a five-request `ioctl_fd_first_request`; neither is in
`theories/LinuxProcessSem/Sys/Fs/Ioctl.v` at f1006fe8, so the twin carries
neither (gaps ledger P-C02, P-C03, P-C04, P-C05). -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The eight requests no file that is not a terminal implements, and so
the ones every fd this model can produce answers -ENOTTY.  The list, and
why it is a list rather than a magic-letter test, is argued on Rocq's
`Ioctl.tty_only_request`; what the kernel does with them:

`SYSCALL_DEFINE3(ioctl, …)` (fs/ioctl.c:583-600, Linux v6.18.46) tries
`do_vfs_ioctl` (fs/ioctl.c:492-581) and, on its -ENOIOCTLCMD, `vfs_ioctl`
(fs/ioctl.c:44-56).  `do_vfs_ioctl`'s switch is an explicit list none of
these eight is in — its 0x54xx members are FIOCLEX, FIONCLEX, FIONBIO,
FIOASYNC, FIOQSIZE and FIONREAD (:499-554) — and its `default` arm runs
`file_ioctl` (fs/ioctl.c:322-338, Linux v6.18.46) only for a regular file, whose own
switch (FIBMAP and the preallocate commands) has none of them either, so
every one falls out at -ENOIOCTLCMD (:580).  `vfs_ioctl` then starts from
-ENOTTY (:46), takes it as the answer when the file has no
`unlocked_ioctl` (:48-49), and maps a handler's -ENOIOCTLCMD to it too
(:51-53).

The handlers that DO claim these requests all sit behind a terminal:
TIOCGWINSZ / TIOCSWINSZ in `tty_ioctl` (drivers/tty/tty_io.c:2707-2710,
Linux v6.18.46), TIOCNOTTY / TIOCSCTTY in `tty_jobctrl_ioctl`
(drivers/tty/tty_jobctrl.c:578-584), TCGETS / TCSETS in `tty_mode_ioctl`
(drivers/tty/tty_ioctl.c:802-803 and :811-815 — the `TCGETS` arm compiled
when `TCGETS2` is defined, the `#else` of :804 at :810, which
include/uapi/asm-generic/ioctls.h:61 (Linux v6.18.46) makes riscv64's), TIOCSPTLCK /
TIOCGPTN in `pty_unix98_ioctl` (drivers/tty/pty.c:646-655, Linux v6.18.46).  None answers
-ENOTTY unconditionally — `tty_jobctrl_ioctl` gives TIOCNOTTY -ENOTTY only
when the tty is not the caller's controlling terminal (:579-580) — which
is why this model must never hand one of them to a terminal; that
it does not is the environment obligation the Rocq header records in
bugs/ioctl-constant-answer-surface.md.

The constants are `Sys.Uapi.Fs`'s, each cited there to
include/uapi/asm-generic/ioctls.h.  Rocq: eight `bv_eqb` tests joined by
`||`, kept verbatim. -/
def tty_only_request (req : word) : Bool :=
  bv_eqb req TCGETS     || bv_eqb req TCSETS    || bv_eqb req TIOCSCTTY ||
  bv_eqb req TIOCGWINSZ || bv_eqb req TIOCSWINSZ || bv_eqb req TIOCNOTTY ||
  bv_eqb req TIOCGPTN   || bv_eqb req TIOCSPTLCK


/-- `ioctl fd req …`: modeled for the eight terminal-only requests of
`tty_only_request`, each answered -EBADF on a closed fd and -ENOTTY on
every open fd this model can hold other than `/dev/urandom`; every other
request is `unmodeled` on an open fd, and every request on `/dev/urandom`
is `unmodeled`.  The argument for
each arm is on Rocq's `Ioctl.ioctl_spec` and its header; the kernel lines it
rests on, read at Linux v6.18.46:

THE FD IS RESOLVED FIRST.  `SYSCALL_DEFINE3(ioctl, …)` (fs/ioctl.c:583-600)
opens with `CLASS(fd, f)(fd)` and returns -EBADF on `fd_empty(f)`
(:585-589) before `cmd` is read by anything; the model answers that
-EBADF for every request, as Rocq does.
`fd` and `req` arrive already truncated to 32 bits (`Syscall.fd32`,
`Syscall.cmd32`, from the `unsigned int` parameters of that signature).
`security_file_ioctl` (security/security.c:3064-3067, Linux v6.18.46) runs next (:591-593)
and can answer first under a policy; the arm is a null-LSM claim, as the
Rocq header says.

EVERY OPEN KIND TAKES -ENOTTY, each from its own handler, all through the
two halves `tty_only_request`'s docstring walks:
- a regular file (`FdFile`, `FdFileW`, `FdFileA`, `FdFileRW`): ext4's
  `__ext4_ioctl`
  (fs/ext4/ioctl.c:1536, default arm :1929-1930) answers -ENOTTY itself;
  on the harness's tmpfs, whose `shmem_file_operations` (mm/shmem.c, Linux v6.18.46) has
  no `.unlocked_ioctl`, it is `vfs_ioctl`'s own first branch (:48-49) —
  the same errno from the same absence of a terminal;
- a pipe end (`FdPipe`): `pipe_ioctl` (fs/pipe.c:619-656, Linux v6.18.46) answers
  -ENOIOCTLCMD from its default arm (:653-654), which `vfs_ioctl` maps to
  -ENOTTY; none of the eight is its FIONREAD or an IOC_WATCH_QUEUE
  command, so all eight take that arm;
- a socket (`FdSocket`, an AF_INET stream): `sock_ioctl`
  (net/socket.c:1282-1380, Linux v6.18.46) takes its default arm into `sock_do_ioctl`
  (:1375-1376), whose `ops->ioctl` is `inet_ioctl`
  (net/ipv4/af_inet.c:954, Linux v6.18.46, default arm :1000-1005) → `sk_ioctl`
  (net/core/sock.c:4408-4425, which for a TCP socket returns
  `sock_ioctl_out` at :4424) → `sock_ioctl_out` (net/core/sock.c:4392-4401, Linux v6.18.46,
  calling `sk_prot->ioctl` at :4396 and writing through `arg` at :4400 only
  on success) → `tcp_ioctl` (net/ipv4/tcp.c:644, Linux v6.18.46, default arm :682-683,
  -ENOIOCTLCMD); back in `sock_do_ioctl` (net/socket.c:1245-1275, Linux v6.18.46) an
  -ENOIOCTLCMD whose `cmd` fails `is_socket_ioctl_cmd`
  (include/linux/netdevice.h:4251-4254, `_IOC_TYPE(cmd) == SOCK_IOC_TYPE`)
  is -ENOTTY (:1264-1265).  All eight have `_IOC_TYPE` 0x54 ('T') and
  `SOCK_IOC_TYPE` is 0x89 (include/uapi/linux/sockios.h:29, Linux v6.18.46), so the
  answer is decided from the request alone, with no user memory touched;
- a directory (`FdDir`) and a standard channel (`FdChannel`): the Rocq
  header's argument, and its ASSUMPTION that no standard descriptor is a
  terminal, which the harness meets by construction.

`/dev/null` (`FdDevNull`) TAKES THE SAME -ENOTTY for the eight, as in
Rocq, and it is the one open kind that reaches it through `vfs_ioctl`'s
FIRST branch rather than through -ENOIOCTLCMD: `null_fops`
(drivers/char/mem.c:644-652, Linux v6.18.46) has no `.unlocked_ioctl`, so `vfs_ioctl`
takes its first branch with the initialiser `error = -ENOTTY` never
overwritten.  The requests `do_vfs_ioctl` does claim on this kind (FIONBIO,
FIOCLEX and their kin) change state this model does not carry and stay
`unmodeled` here, as on every other kind.  Rocq's arm says why the kind is
worth answering rather than declining: musl's `__fdopen` issues TIOCGWINSZ
on a freshly opened writable stream, so a declining kind would leave the
modeled surface one syscall after an `fopen` of the null device.

`/dev/urandom` (`FdUrandom`) is FAIL-CLOSED on every request, as in
Rocq, and here the decline hides a DIFFERENT real answer: `urandom_fops`
(drivers/char/random.c:1572-1581) has `.unlocked_ioctl = random_ioctl`
(:1575), and `random_ioctl` (drivers/char/random.c:1492-1553, Linux v6.18.46) answers
RNDGETENTCNT with the pool's entropy count through `arg` (:1498-1502),
gates RNDADDTOENTCNT, RNDADDENTROPY, RNDZAPENTCNT, RNDCLEARPOOL and
RNDRESEEDCRNG on `capable(CAP_SYS_ADMIN)`, and answers everything that
reaches it — the eight of `tty_only_request` among them, none being in
`do_vfs_ioctl`'s switch — -EINVAL from its default arm (:1550-1551), never
-ENOTTY, since `vfs_ioctl` maps only -ENOIOCTLCMD to it.  What never
reaches it is what `do_vfs_ioctl` claims first (fs/ioctl.c:499-522, Linux v6.18.46):
FIOCLEX, FIONCLEX, FIONBIO and FIOASYNC are answered there, and FIOQSIZE on
a character device is its own -ENOTTY (:522).  A real answer would be a
switch over the request word and a
capability set neither of which is written, so the arm declines, and the
pins fix that neither -EINVAL nor -ENOTTY is admitted there.

DELIBERATELY UNMODELED on an open fd, for the reasons Rocq's docstring
gives: FIONREAD / TIOCINQ (`do_vfs_ioctl`, fs/ioctl.c:549-554, Linux v6.18.46, and
`pipe_ioctl`, fs/pipe.c:625-637, Linux v6.18.46) succeeds with an answer written through
the third argument; FIONBIO (:507-508) changes O_NONBLOCK and FIOCLEX /
FIONCLEX (:499-505) the close-on-exec flag, neither of which this model
carries; and every request that writes through the third argument, which
`ioctl_spec` does not take. -/
def ioctl_spec (fd req : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) | some (.FdFile _ _) | some (.FdFileW _ _)
  | some (.FdFileA _ _) | some (.FdFileRW _ _) | some .FdDir
  | some (.FdSocket _) | some (.FdPipe _ _) | some (.FdDevNull _ _) =>
      if tty_only_request req then err_ret ENOTTY else unmodeled
  | some .FdUrandom => unmodeled

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl
