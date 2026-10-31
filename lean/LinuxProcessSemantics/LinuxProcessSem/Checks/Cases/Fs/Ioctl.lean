-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Fs/Ioctl.v
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.Ioctl — what `ioctl` admits, read off against Linux

Worked examples over `Sys.Fs.Ioctl.ioctl_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Ioctl.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  The Rocq file's examples run the executable
checker on `init_model`; here each is an `iff` over every outcome `o` of
the spec on `demo_model`, Rocq's `init_model [] 0 0 demo_sp demo_limit
(demo_input [] IEof)` under one name, closed by `sys_norm`, with the
concrete lie a kernel could tell refuted beside it by `sys_refute`.

HOW THESE ARE STATED.  `ioctl_spec`'s admitted set is always a singleton —
one errno, the model untouched, no events — or `Unmodeled`, so every pin is
an `iff` with one outcome on its right, which fixes the positive half
(that outcome is admitted) and the negative half (no other errno, no
success, no model change, no event, no `Unmodeled`) in one statement.  The
refutations restate the negative half on the lies worth naming.

NAMES.  `<fixture>_<request>_is_<answer>` is an `iff`; `_rejected` refutes
a lie no supported kernel tells; `_declined` refutes the kernel's REAL
answer on a kind the arm fails closed on (`/dev/null`, `/dev/urandom`),
so a reader grepping for refuted lies does not take a coverage gap for
one.

EVIDENCE LINES.  A positive pin's `kernel:` line must name a span that
spells every constant its statement names (`tools/check_lean_pin_evidence.py`,
KMENTION), and the request words are spelled by the terminal handlers
that claim them, not by `fs/ioctl.c`; so a -EBADF or -ENOTTY pin names
`tty_mode_ioctl`, `tty_ioctl`, `tty_jobctrl_ioctl` or `pty_unix98_ioctl`
beside the function that decides its answer.  The tty handler is where
the request's name lives, never part of why the answer is what it is.  A
`probe:` line names a recorded case whose call has the pin's fd kind and
request; every `ioctl_spec.c` call is on a write-only regular file or a
closed fd, never on fd 0/1/2, so where a channel pin and a recorded call
differ in kind, the file pin that matches the call carries the `probe:`
line and the channel pin cites the kernel.

PROBES.  The recorded ioctls reach a regular file and a closed fd
(`ioctl_spec.c`), a pipe's read end (`pipe2_spec.c`), the stdout pipe
(`musl_start.c`) and a fresh socket (`socket_rw.c`).  None reaches a
directory, `/dev/null` or `/dev/urandom`, and none issues TIOCOUTQ,
FIOCLEX or FIOQSIZE; those arms rest on the kernel reading alone.  The
probes that would close the gap, each one `CASE:` line on an existing or
new probe: `ioctl(dirfd, TIOCSCTTY, 0)` -ENOTTY (`conform`, with a `ret=0`
reject twin), `ioctl(dirfd, FIOQSIZE, &q)` 0 (`fail-closed`),
`ioctl(devnull, TCGETS, buf)` -ENOTTY (`conform`, with a `ret=0` reject
twin),
`ioctl(urandom, TCGETS, buf)` -EINVAL (`fail-closed`), TIOCOUTQ on a
socket and FIOCLEX on a file, both 0 (`fail-closed`), and `socket_rw.c`'s
first `ioctl` mutated to -EFAULT (`reject`).

The order of the sections is the order the kernel's checks fire, walked
from `SYSCALL_DEFINE3(ioctl, …)` (fs/ioctl.c:583-600, Linux v6.18.46,
commit 1f99e9ab748f) down: `fd_empty` → -EBADF (:588-589);
`security_file_ioctl` (:591-593, null under the harness); `do_vfs_ioctl`
(:595, the fd-generic list); `vfs_ioctl` (:596-597, the file's own
handler, -ENOTTY by default).  The `unmodeled` pins say, each, what the
model lacks to answer.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Ioctl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! The spec's unfolding, registered for `sys_norm` here rather than in
`Checks/Cases/Tactic.lean`'s register, which a port PR does not edit; the
gate `tty_only_request` is decided, never unfolded, as that file's header
asks. -/
attribute [sys_simp low] ioctl_spec.eq_1

/-! ## The requests these checks name

The eight of `tty_only_request` are `Sys.Uapi.Fs`'s.  The seven below are
the neighbours the gate refuses, spelled here as `word` literals because
no spec names them: six that `do_vfs_ioctl` claims — FIOCLEX, FIONCLEX,
FIONBIO and FIOASYNC for every file kind, FIONREAD and FIOQSIZE by kind
(fs/ioctl.c:499-522 and :549-554, Linux v6.18.46) — and TIOCOUTQ, which
no fd-generic arm claims and whose answer is the file's own handler's.
Each value is pinned against the kernel header right below its
definition, so a mistyped number fails the build, not the reader. -/

/-- `#define FIONREAD 0x541B` (include/uapi/asm-generic/ioctls.h:46, Linux
v6.18.46, commit 1f99e9ab748f); `TIOCINQ` is its alias (:47). -/
def FIONREAD : word := 0x541B
/-- kernel: include/uapi/asm-generic/ioctls.h:FIONREAD@v6.18.46 -/
example : FIONREAD = 21531 := by decide

/-- `#define FIONBIO 0x5421` (include/uapi/asm-generic/ioctls.h:53, Linux
v6.18.46, commit 1f99e9ab748f). -/
def FIONBIO : word := 0x5421
/-- kernel: include/uapi/asm-generic/ioctls.h:FIONBIO@v6.18.46 -/
example : FIONBIO = 21537 := by decide

/-- `#define FIONCLEX 0x5450` (include/uapi/asm-generic/ioctls.h:85, Linux
v6.18.46, commit 1f99e9ab748f). -/
def FIONCLEX : word := 0x5450
/-- kernel: include/uapi/asm-generic/ioctls.h:FIONCLEX@v6.18.46 -/
example : FIONCLEX = 21584 := by decide

/-- `#define FIOCLEX 0x5451` (include/uapi/asm-generic/ioctls.h:86, Linux
v6.18.46, commit 1f99e9ab748f). -/
def FIOCLEX : word := 0x5451
/-- kernel: include/uapi/asm-generic/ioctls.h:FIOCLEX@v6.18.46 -/
example : FIOCLEX = 21585 := by decide

/-- `#define FIOASYNC 0x5452` (include/uapi/asm-generic/ioctls.h:87, Linux
v6.18.46, commit 1f99e9ab748f). -/
def FIOASYNC : word := 0x5452
/-- kernel: include/uapi/asm-generic/ioctls.h:FIOASYNC@v6.18.46 -/
example : FIOASYNC = 21586 := by decide

/-- `#define TIOCOUTQ 0x5411` (include/uapi/asm-generic/ioctls.h:36, Linux
v6.18.46, commit 1f99e9ab748f); `SIOCOUTQ` is its alias
(include/uapi/linux/sockios.h:27). -/
def TIOCOUTQ : word := 0x5411
/-- kernel: include/uapi/asm-generic/ioctls.h:TIOCOUTQ@v6.18.46 -/
example : TIOCOUTQ = 21521 := by decide

/-- `#define FIOQSIZE 0x5460` (include/uapi/asm-generic/ioctls.h:105-106,
Linux v6.18.46, commit 1f99e9ab748f, under `#ifndef FIOQSIZE`, which no
riscv64 header pre-empts). -/
def FIOQSIZE : word := 0x5460
/-- kernel: include/uapi/asm-generic/ioctls.h:FIOQSIZE@v6.18.46 -/
example : FIOQSIZE = 21600 := by decide

/-- The eight terminal-only requests. -/
def tty_only_requests : List word :=
  [TCGETS, TCSETS, TIOCSCTTY, TIOCGWINSZ, TIOCSWINSZ, TIOCNOTTY, TIOCGPTN, TIOCSPTLCK]

/-- The gate admits EXACTLY the eight: `tty_only_request` is membership in
`tty_only_requests`, in both directions.  The direction a one-way helper
would miss is the one that matters — a gate widened by FIONCLEX or
FIOASYNC would still satisfy every pin that quantifies over the list, and
the arm would answer -ENOTTY where `do_vfs_ioctl` returns 0.  This is the
model's own shape; the kernel claims are the refusals beside it, one per
neighbour: FIONREAD, FIONBIO, FIOCLEX, FIONCLEX and FIOASYNC are requests
`do_vfs_ioctl` answers (fs/ioctl.c:499-511, :549-554, Linux v6.18.46), so
a gate that admitted one would answer -ENOTTY where Linux succeeds;
TIOCOUTQ and FIOQSIZE are the two 'T' neighbours whose answer depends on
the fd kind (their own section below).  What makes exactly these eight
the gate is the kernel: `do_vfs_ioctl` claims none of them on any kind
(fs/ioctl.c:492-581, Linux v6.18.46), so every one reaches `vfs_ioctl`
(:44-56), where a terminal's driver would answer and nothing this model
holds does.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem tty_only_request_iff_mem (r : word) :
    tty_only_request r = true ↔ r ∈ tty_only_requests := by
  simp only [tty_only_request, Bool.or_eq_true, bv_eqb_eq, tty_only_requests,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc]
/-- FIONREAD is claimed by `do_vfs_ioctl` (fs/ioctl.c:549-554, Linux v6.18.46), so the gate refuses it.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem tty_only_request_fionread : tty_only_request FIONREAD = false := by decide
/-- FIONBIO is claimed by `do_vfs_ioctl` (fs/ioctl.c:507-508, Linux v6.18.46), so the gate refuses it.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem tty_only_request_fionbio : tty_only_request FIONBIO = false := by decide
/-- FIOCLEX is claimed by `do_vfs_ioctl` (fs/ioctl.c:499-501, Linux v6.18.46), so the gate refuses it.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem tty_only_request_fioclex : tty_only_request FIOCLEX = false := by decide
/-- FIONCLEX is claimed by `do_vfs_ioctl` (fs/ioctl.c:503-505, Linux v6.18.46): `set_close_on_exec(fd, 0)` and 0 on every kind, so the gate refuses it.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem tty_only_request_fionclex : tty_only_request FIONCLEX = false := by decide
/-- FIOASYNC is claimed by `do_vfs_ioctl` (fs/ioctl.c:510-511, Linux v6.18.46): `ioctl_fioasync` (:363-383) reads the flag through `arg` and, when it changes FASYNC, calls the file's `fasync` or answers -ENOTTY without one — an answer that depends on memory and state the arm has neither of, so the gate refuses it.
kernel: fs/ioctl.c:do_vfs_ioctl,ioctl_fioasync@v6.18.46 -/
theorem tty_only_request_fioasync : tty_only_request FIOASYNC = false := by decide
/-- TIOCOUTQ is a terminal's unsent-output count (the line discipline's `n_tty_ioctl`, drivers/tty/n_tty.c:2498-2499, Linux v6.18.46) and a socket's `SIOCOUTQ` (`tcp_ioctl`, net/ipv4/tcp.c:663-671): an answer that depends on the kind, so the gate refuses it.
kernel: drivers/tty/n_tty.c:n_tty_ioctl; net/ipv4/tcp.c:tcp_ioctl@v6.18.46 -/
theorem tty_only_request_tiocoutq : tty_only_request TIOCOUTQ = false := by decide
/-- FIOQSIZE is answered by `do_vfs_ioctl` itself (fs/ioctl.c:513-522, Linux v6.18.46), so the gate refuses it.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem tty_only_request_fioqsize : tty_only_request FIOQSIZE = false := by decide

/-- `_IOC_TYPE` of every one of the eight is 'T' (0x54): bits 8-15 of the
request (include/uapi/asm-generic/ioctl.h:23-47 and :95, Linux v6.18.46).
This is the fact the socket arm turns on — `is_socket_ioctl_cmd`
(include/linux/netdevice.h:4251-4254) compares it with `SOCK_IOC_TYPE`
0x89 (include/uapi/linux/sockios.h:29) — and it holds for the two
`_IOR`/`_IOW` requests as much as for the six bare 0x54xx ones.  The
full decode of each word is `Checks/Cases/Sys/Uapi/Fs.lean`'s
`tty_ioctls_decode`; this states the one byte the socket arm reads.
kernel: include/linux/netdevice.h:is_socket_ioctl_cmd; include/uapi/asm-generic/ioctl.h:_IOC_TYPE@v6.18.46 -/
theorem ioc_type_of_tty_only_requests :
    ∀ r ∈ tty_only_requests, bv_unsigned r / 256 % 256 = 84 := by
  intro r hr
  simp only [tty_only_requests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Closed descriptors

`SYSCALL_DEFINE3(ioctl, …)` returns -EBADF from `fd_empty(f)`
(fs/ioctl.c:588-589, Linux v6.18.46) before `cmd` is read by anything, so
the arm answers that errno for EVERY request on a closed fd, the eight of
`tty_only_request` and their neighbours alike.
`demo_model` holds fds 0, 1 and 2 only. -/

/-- TCGETS on fd 7, which is not open: -EBADF, the model untouched.
kernel: fs/ioctl.c:ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem closed_fd_tcgets_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 7 TCGETS i demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- FIONBIO on a closed fd is -EBADF, as every request is: the fd check
fires first (fs/ioctl.c:588-589 precedes :507, Linux v6.18.46), so the
request the file's own handler would have answered never reaches it.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl@v6.18.46 -/
theorem closed_fd_fionbio_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 7 FIONBIO i demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- …so the closed fd is not a decline here: a request outside the eight
is `Unmodeled` only on an OPEN fd (fs/ioctl.c:588-589 before :507, Linux
v6.18.46).
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl@v6.18.46 -/
theorem closed_fd_fionbio_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 7 FIONBIO i demo_model Unmodeled := by
  sys_refute

/-- A kernel answering -ENOTTY on a closed fd is lying: `fd_empty` returns
before `vfs_ioctl` could (fs/ioctl.c:588-589, Linux v6.18.46 vs :596-597).  `ioctl_spec.c`'s
`base` mode, eighth `ioctl`: TCGETS on the never-opened fd 999.
probe: testing/syscall-check/tests/ioctl_spec.c#reject --mutate ioctl#8:ret=-ENOTTY -- base -/
theorem closed_fd_enotty_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 7 TCGETS i demo_model (Ok (mkEffect (errno_ret ENOTTY) [] []) m' evs) := by
  sys_refute

/-- On every model and for every request, a closed fd answers EBADF.
Linux fs/ioctl.c ioctl checks fd_empty before cmd is read by anything, so
the request does not enter the claim.
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem closed_fd_is_ebadf (fd req : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = none) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h]
  sys_norm

/-! ## `vfs_ioctl` answers -ENOTTY on every open kind

Each kind's handler is walked on `ioctl_spec`'s docstring; the pins here
take one fd of each kind the Lean `FdEntry` can hold, and each of the
eight terminal-only requests is -ENOTTY on every one of them.  The
refutations name the lies: a success (the answer a real terminal gives
TCGETS, `tty_mode_ioctl`, drivers/tty/tty_ioctl.c:811-815, Linux v6.18.46),
-EBADF, a written byte, a changed model, and `Unmodeled`. -/

/-- TIOCGWINSZ on stdout — the request musl's stdio issues to choose a
buffering mode (`Sys.Uapi.Fs`'s header) — is -ENOTTY on the standard
channel; Rocq's `ioctl_tiocgwinsz_enotty`.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 1 TIOCGWINSZ i demo_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- All eight terminal-only requests on stdout are -ENOTTY; Rocq's
`ioctl_tty_only_requests_all_enotty`.  Each falls out of `do_vfs_ioctl` at
-ENOIOCTLCMD (fs/ioctl.c:580) and `vfs_ioctl` answers -ENOTTY (:46-53).
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem stdout_tty_only_requests_all_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ∀ r ∈ tty_only_requests,
      (ioctl_spec 1 r i demo_model o ↔
        o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model []) := by
  intro r hr
  simp only [tty_only_requests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> sys_norm

/-- Standard input and standard error take the same answer as standard
output: the arm reads the fd kind, not the number.
kernel: fs/ioctl.c:vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem stdin_tcgets_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 0 TCGETS i demo_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm
/-- Standard error takes the same answer as standard output: the arm reads the fd kind, not the number.
kernel: fs/ioctl.c:vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem stderr_tcgets_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 2 TCGETS i demo_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- A regular file, read-only: ext4's `__ext4_ioctl` answers -ENOTTY from
its default arm (fs/ext4/ioctl.c:1929-1930, Linux v6.18.46); on the
harness's tmpfs, whose `shmem_file_operations` (mm/shmem.c) has no
`.unlocked_ioctl`, `vfs_ioctl`'s first branch (fs/ioctl.c:48-49) answers
the same -ENOTTY — which is what `ioctl_spec.c`'s `tty` mode records.
kernel: fs/ext4/ioctl.c:__ext4_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem file_tcgets_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TCGETS i (fixture_of (fds := [(3, .FdFile [97] 0)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdFile [97] 0)])) [] := by
  sys_norm

/-- TIOCSWINSZ on a write-only file: -ENOTTY, as on a file open for
reading — `__ext4_ioctl`'s default arm (fs/ext4/ioctl.c:1929-1930, Linux
v6.18.46) reads neither the access mode nor the window it is handed.
kernel: fs/ext4/ioctl.c:__ext4_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem filew_tiocswinsz_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TIOCSWINSZ i (fixture_of (fds := [(3, .FdFileW [97] 0)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdFileW [97] 0)])) [] := by
  sys_norm

/-- A directory: `do_vfs_ioctl`'s default arm runs `file_ioctl` only for
`S_ISREG` (fs/ioctl.c:574-577, Linux v6.18.46), so a directory falls out at
:580 into `vfs_ioctl`, and which -ENOTTY it hands back depends on the
filesystem: an ext4 directory's `ext4_dir_operations` has `.unlocked_ioctl
= ext4_ioctl` (fs/ext4/dir.c:687), so the -ENOTTY is `__ext4_ioctl`'s
default arm (fs/ext4/ioctl.c:1929-1930), relayed at :51 and :55; the
harness's cwd is a tmpfs, whose directories take
`simple_offset_dir_operations` (mm/shmem.c:3138; fs/libfs.c:568-573) with
no `.unlocked_ioctl`, so there it is `vfs_ioctl`'s own first branch
(:48-49).  The same errno either way.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl; fs/ext4/ioctl.c:__ext4_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl@v6.18.46 -/
theorem dir_tiocsctty_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TIOCSCTTY i (fixture_of (fds := [(3, .FdDir)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdDir)])) [] := by
  sys_norm

/-- A socket: `sock_do_ioctl` answers -ENOTTY to an -ENOIOCTLCMD whose
request is not of type 0x89 (net/socket.c:1264-1265, Linux v6.18.46), from
the request alone; `ioc_type_of_tty_only_requests` above is why TIOCGWINSZ
is one.
kernel: net/socket.c:sock_do_ioctl; include/linux/netdevice.h:is_socket_ioctl_cmd; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem socket_tiocgwinsz_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TIOCGWINSZ i (fixture_of (fds := [(3, .FdSocket .SkFresh)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdSocket .SkFresh)])) [] := by
  sys_norm

/-- …and TIOCGPTN, whose `_IOR` encoding carries a direction and a size
above the type byte, is still type 'T' and still -ENOTTY there.
kernel: net/socket.c:sock_do_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem socket_tiocgptn_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TIOCGPTN i (fixture_of (fds := [(3, .FdSocket .SkFresh)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdSocket .SkFresh)])) [] := by
  sys_norm

/-- A pipe's read end: `pipe_ioctl` answers -ENOIOCTLCMD from its default
arm (fs/pipe.c:653-654, Linux v6.18.46) and `vfs_ioctl` maps it to -ENOTTY
(fs/ioctl.c:51-53).  This is `pipe2_spec.c`'s `ioctl` case.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- ioctl -/
theorem pipe_reader_tiocgwinsz_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TIOCGWINSZ i (fixture_of (fds := [(3, .FdPipe 0 false)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdPipe 0 false)])) [] := by
  sys_norm

/-- TCSETS on a pipe writer: -ENOTTY.  The direction of the end does not
enter `pipe_ioctl`, whose default arm (fs/pipe.c:653-654, Linux v6.18.46)
answers -ENOIOCTLCMD for this request as for the other seven, and
`vfs_ioctl` maps it (fs/ioctl.c:51-53).
kernel: fs/pipe.c:pipe_ioctl; fs/ioctl.c:vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem pipe_writer_tcsets_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 4 TCSETS i (fixture_of (fds := [(4, .FdPipe 0 true)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(4, .FdPipe 0 true)])) [] := by
  sys_norm

/-! ### The same, for every model and every payload of each kind

The concrete fixtures above evaluate; these state the same answer with the
fd's payload symbolic — any channel, any path and offset, any socket state,
either pipe end — on any model whose table holds it, and with the request
symbolic behind `tty_only_request`.  They are the claim the docstring makes: the
handler each kind reaches reads none of that.  `pipe_ioctl`'s default arm
(fs/pipe.c:653-654, Linux v6.18.46) reads neither the pipe nor the end;
`__ext4_ioctl`'s (fs/ext4/ioctl.c:1929-1930) neither path nor offset;
`tcp_ioctl`'s (net/ipv4/tcp.c:682-683) and `is_socket_ioctl_cmd`
(include/linux/netdevice.h:4251-4254) no socket state. -/

/-- Any standard channel, on any model, for any terminal-only request: -ENOTTY from `vfs_ioctl`'s default (fs/ioctl.c:46-53, Linux v6.18.46) once `do_vfs_ioctl` has declined (:580).
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem channel_tty_request_is_enotty (fd req c : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some (.FdChannel c))
    (hr : tty_only_request req = true) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, hr, ↓reduceIte]
  sys_norm

/-- Any regular file, any path and offset: ext4's `__ext4_ioctl` default arm (fs/ext4/ioctl.c:1929-1930, Linux v6.18.46) reads neither.
kernel: fs/ext4/ioctl.c:__ext4_ioctl@v6.18.46 -/
theorem file_tty_request_is_enotty (fd req : word) (p : Fs.path) (off : word) (i : SyscallInput)
    (m : Model) (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some (.FdFile p off))
    (hr : tty_only_request req = true) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, hr, ↓reduceIte]
  sys_norm

/-- …and one open for writing: the same handler, the same answer.
kernel: fs/ext4/ioctl.c:__ext4_ioctl@v6.18.46 -/
theorem filew_tty_request_is_enotty (fd req : word) (p : Fs.path) (off : word) (i : SyscallInput)
    (m : Model) (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some (.FdFileW p off))
    (hr : tty_only_request req = true) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, hr, ↓reduceIte]
  sys_norm

/-- Any directory: `do_vfs_ioctl`'s default arm runs `file_ioctl` only for `S_ISREG` (fs/ioctl.c:574-577, Linux v6.18.46), so the answer comes through `vfs_ioctl` — its own first-branch -ENOTTY (:48-49) where the directory's `file_operations` has no `.unlocked_ioctl` (tmpfs, `simple_offset_dir_operations`, fs/libfs.c:568-573), and `__ext4_ioctl`'s default-arm -ENOTTY (fs/ext4/ioctl.c:1929-1930) relayed at :55 on ext4, whose `ext4_dir_operations` sets `.unlocked_ioctl = ext4_ioctl` (fs/ext4/dir.c:687); neither reads the directory.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl; fs/ext4/ioctl.c:__ext4_ioctl@v6.18.46 -/
theorem dir_tty_request_is_enotty (fd req : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some .FdDir)
    (hr : tty_only_request req = true) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, hr, ↓reduceIte]
  sys_norm

/-- Any socket state: `tcp_ioctl`'s default arm (net/ipv4/tcp.c:682-683, Linux v6.18.46) and `is_socket_ioctl_cmd` read no socket state, so the answer is `sock_do_ioctl`'s -ENOTTY (net/socket.c:1264-1265).
kernel: net/socket.c:sock_do_ioctl; net/ipv4/tcp.c:tcp_ioctl; include/linux/netdevice.h:is_socket_ioctl_cmd@v6.18.46 -/
theorem socket_tty_request_is_enotty (fd req : word) (sk : SockState) (i : SyscallInput)
    (m : Model) (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hr : tty_only_request req = true) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, hr, ↓reduceIte]
  sys_norm

/-- Either end of any pipe: `pipe_ioctl`'s default arm (fs/pipe.c:653-654, Linux v6.18.46) reads neither.
kernel: fs/pipe.c:pipe_ioctl; fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem pipe_tty_request_is_enotty (fd req id : word) (w : Bool) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some (.FdPipe id w))
    (hr : tty_only_request req = true) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, hr, ↓reduceIte]
  sys_norm

/-- THE TERMINAL LIE: TCGETS succeeding on stdout is what a real terminal
answers (`tty_mode_ioctl`, drivers/tty/tty_ioctl.c:811-815, Linux
v6.18.46) and what this arm must refuse, because the run's standard
descriptors are not terminals
(linux-process-semantics@ff0313ba4f:bugs/ioctl-constant-answer-surface.md).
kernel: drivers/tty/tty_ioctl.c:tty_mode_ioctl; fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem stdout_tcgets_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 TCGETS i demo_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and the lie as it is RECORDED on the standard channel: musl's stdio
TIOCGWINSZ on the stdout pipe mutated to 0, which `musl_start.c` requires
the model to refuse.
probe: testing/syscall-check/tests/musl_start.c#reject --mutate ioctl:ret=0 -/
theorem stdout_tiocgwinsz_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 TIOCGWINSZ i demo_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The same lie on a regular file: TCGETS succeeding is a terminal's
answer (`tty_mode_ioctl`, drivers/tty/tty_ioctl.c:811-815, Linux v6.18.46)
where ext4's `__ext4_ioctl` answers -ENOTTY (fs/ext4/ioctl.c:1929-1930).
`ioctl_spec.c`'s `tty` mode, first `ioctl`, on the file it creates
write-only.
probe: testing/syscall-check/tests/ioctl_spec.c#reject --mutate ioctl#1:ret=0 -- tty -/
theorem filew_tcgets_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TCGETS i (fixture_of (fds := [(3, .FdFileW [97] 0)]))
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and on a fresh socket: TIOCGWINSZ succeeding, `socket_rw.c`'s first
`ioctl` mutated to 0; `sock_do_ioctl` answers -ENOTTY from the request
alone (net/socket.c:1264-1265, Linux v6.18.46).
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate ioctl#1:ret=0 -- rw -/
theorem socket_tiocgwinsz_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TIOCGWINSZ i (fixture_of (fds := [(3, .FdSocket .SkFresh)]))
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- An open fd is not -EBADF.
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem stdout_tcgets_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 TCGETS i demo_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- TIOCGPTN on a pipe is not -EINVAL: that is a BSD pty master's answer,
`pty_bsd_ioctl` (drivers/tty/pty.c:453-471, Linux v6.18.46) returning it at
:467-468 because "glibc expects EINVAL here", and no pipe reaches a tty
driver.
kernel: drivers/tty/pty.c:pty_bsd_ioctl; fs/pipe.c:pipe_ioctl@v6.18.46 -/
theorem pipe_tiocgptn_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TIOCGPTN i (fixture_of (fds := [(3, .FdPipe 0 false)]))
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and -EINVAL is not admitted for TIOCGWINSZ on the read end either:
`pipe_ioctl`'s default arm is -ENOIOCTLCMD (fs/pipe.c:653-654, Linux
v6.18.46), which `vfs_ioctl` maps to -ENOTTY and nothing else
(fs/ioctl.c:51-53).  `pipe2_spec.c`'s `ioctl` reject twin.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate ioctl:ret=-EINVAL -- ioctl -/
theorem pipe_reader_tiocgwinsz_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TIOCGWINSZ i (fixture_of (fds := [(3, .FdPipe 0 false)]))
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- -ENOTTY writes nothing: `vfs_ioctl` returns before any handler could
touch the third argument (fs/ioctl.c:46-53), so a write in the effect, or
a byte on the channel, is refused.
kernel: fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_write_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 TIOCGWINSZ i demo_model
        (Ok (mkEffect (errno_ret ENOTTY) [(4096, [0, 0, 0, 0])] []) m' evs) := by
  sys_refute
/-- …and no byte reaches the channel either: nothing on `vfs_ioctl`'s -ENOTTY path writes (fs/ioctl.c:46-53, Linux v6.18.46).
kernel: fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_event_rejected (i : SyscallInput) (m' : Model) :
    ¬ ioctl_spec 1 TIOCGWINSZ i demo_model
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m' [WriteEv 1 0]) := by
  sys_refute

/-- The model is untouched: -ENOTTY changes no descriptor and no file.  A
post-state with fd 1 closed is refuted on the fd table.
kernel: fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_model_change_rejected (i : SyscallInput) :
    ¬ ioctl_spec 1 TIOCGWINSZ i demo_model
        (Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [])) []) := by
  sys_refute

/-- A modeled request on an open fd is never `Unmodeled`.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_not_unmodeled (i : SyscallInput) :
    ¬ ioctl_spec 1 TIOCGWINSZ i demo_model Unmodeled := by
  sys_refute

/-! ## What the arm declines on an open fd

Each `Unmodeled` below is a request the kernel ANSWERS — the pins name the
answer and refuse it — and the reason is never a disagreement between the
supported implementations.  It is that the answer depends on state
`ioctl_spec` does not carry (a file's O_NONBLOCK, a descriptor's
close-on-exec flag) or is written through the third argument the spec
does not take (FIONREAD's count).  The Rocq docstring on `ioctl_spec`
lists them; Rocq's `ioctl_other_request_is_error` runs FIONREAD and
FIONBIO. -/

/-- FIONREAD on stdout: `do_vfs_ioctl` claims it (fs/ioctl.c:549-554,
Linux v6.18.46).  Under the harness the channel is a pipe, so it is handed
to `vfs_ioctl` (:550-551), where `pipe_ioctl` answers the queued count
through `arg` (fs/pipe.c:625-637); redirected to a regular file it would be
the size left past the offset, `put_user`'d at :553-554.  Either count is
written through the third argument, which the spec does not take:
declined.
kernel: fs/ioctl.c:do_vfs_ioctl; fs/pipe.c:pipe_ioctl@v6.18.46 -/
theorem stdout_fionread_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 1 FIONREAD i demo_model o ↔ o = Unmodeled := by
  sys_norm

/-- FIONBIO on stdout: `do_vfs_ioctl` claims it (fs/ioctl.c:507-508, Linux
v6.18.46) and `ioctl_fionbio` (fs/ioctl.c:340-361) reads the flag through
`arg` (-EFAULT if that `get_user` fails, :345-347), sets or clears
O_NONBLOCK on the file and returns 0; the model carries no such flag, so
the arm declines, and the success it really returns is not admitted.
kernel: fs/ioctl.c:do_vfs_ioctl,ioctl_fionbio@v6.18.46 -/
theorem stdout_fionbio_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 1 FIONBIO i demo_model o ↔ o = Unmodeled := by
  sys_norm
/-- FIONBIO on a regular file open for writing: `do_vfs_ioctl` claims it
(fs/ioctl.c:507-508, Linux v6.18.46) and `ioctl_fionbio` (:340-361) sets
O_NONBLOCK and returns 0; declined here as on the channel.
kernel: fs/ioctl.c:do_vfs_ioctl,ioctl_fionbio@v6.18.46 -/
theorem filew_fionbio_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIONBIO i (fixture_of (fds := [(3, .FdFileW [97] 0)])) o ↔ o = Unmodeled := by
  sys_norm
/-- …and the 0 the kernel returned there is not admitted: `ioctl_spec.c`'s
`fionbio` mode, on the file it creates write-only, is the recorded run.
(The `iff` above carries kernel evidence because the evidence tool reads a
statement up to its first `:=`, which an inline `fixture_of (fds := …)`
supplies before the `Unmodeled`; a refutation is read correctly.)
probe: testing/syscall-check/tests/ioctl_spec.c#fail-closed -- fionbio -/
theorem filew_fionbio_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 FIONBIO i (fixture_of (fds := [(3, .FdFileW [97] 0)]))
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute
/-- The 0 `ioctl_fionbio` really returns (fs/ioctl.c:340-361, Linux v6.18.46) is not admitted: the flag it sets is state this model lacks.
kernel: fs/ioctl.c:do_vfs_ioctl,ioctl_fionbio@v6.18.46 -/
theorem stdout_fionbio_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 FIONBIO i demo_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and -ENOTTY is not admitted for it either: the gate, not a wildcard,
decides what is -ENOTTY (`tty_only_request_fionbio`).
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem stdout_fionbio_enotty_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 FIONBIO i demo_model (Ok (mkEffect (errno_ret ENOTTY) [] []) m' evs) := by
  sys_refute

/-- FIOCLEX: `do_vfs_ioctl` (fs/ioctl.c:499-501, Linux v6.18.46) calls
`set_close_on_exec` (fs/file.c:1248), which succeeds on every kind and sets
the descriptor's flag; the model carries no such flag: declined.
kernel: fs/ioctl.c:do_vfs_ioctl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem file_fioclex_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIOCLEX i (fixture_of (fds := [(3, .FdFile [97] 0)])) o ↔ o = Unmodeled := by
  sys_norm

/-- FIONCLEX on a regular file: `do_vfs_ioctl` (fs/ioctl.c:503-505, Linux
v6.18.46) clears the descriptor's close-on-exec flag and returns 0 on every
kind; the model carries no such flag: declined, and the 0 is not admitted.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem file_fionclex_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIONCLEX i (fixture_of (fds := [(3, .FdFile [97] 0)])) o ↔ o = Unmodeled := by
  sys_norm

/-- FIOASYNC on a pipe end: `do_vfs_ioctl` (fs/ioctl.c:510-511, Linux
v6.18.46) hands it to `ioctl_fioasync` (:363-383), which reads the flag
through `arg` and runs `pipe_fasync` when FASYNC changes; an answer that
turns on memory the spec does not take: declined.
kernel: fs/ioctl.c:do_vfs_ioctl,ioctl_fioasync@v6.18.46 -/
theorem pipe_fioasync_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIOASYNC i (fixture_of (fds := [(3, .FdPipe 0 false)])) o ↔ o = Unmodeled := by
  sys_norm

/-- FIONREAD on a pipe end: `pipe_ioctl` really answers the queued byte
count (fs/pipe.c:625-637, Linux v6.18.46), through `arg`: declined, as on
every other kind.
kernel: fs/pipe.c:pipe_ioctl@v6.18.46 -/
theorem pipe_fionread_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIONREAD i (fixture_of (fds := [(3, .FdPipe 0 false)])) o ↔ o = Unmodeled := by
  sys_norm

/-- TIOCOUTQ (0x5411), the 'T' neighbour whose answer DEPENDS ON THE FD
KIND: on a TCP socket it is `SIOCOUTQ`, which `tcp_ioctl` answers with the
unacknowledged byte count (net/ipv4/tcp.c:663-671, Linux v6.18.46), written
through `arg` by `sock_ioctl_out` (net/core/sock.c:4400); on a terminal it
is the line discipline's unsent count (`n_tty_ioctl`, drivers/tty/n_tty.c:2498-2499);
on a pipe it is -ENOTTY.  The arm declines it on every kind, and the
socket's real success is not admitted.
kernel: net/ipv4/tcp.c:tcp_ioctl; net/core/sock.c:sock_ioctl_out; drivers/tty/n_tty.c:n_tty_ioctl@v6.18.46 -/
theorem socket_tiocoutq_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TIOCOUTQ i (fixture_of (fds := [(3, .FdSocket .SkFresh)])) o ↔ o = Unmodeled := by
  sys_norm
/-- …and the count `tcp_ioctl` really answers (net/ipv4/tcp.c:663-671, Linux v6.18.46) is not admitted.
kernel: net/ipv4/tcp.c:tcp_ioctl; net/core/sock.c:sock_ioctl_out@v6.18.46 -/
theorem socket_tiocoutq_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TIOCOUTQ i (fixture_of (fds := [(3, .FdSocket .SkFresh)]))
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- FIOQSIZE (0x5460): answered by `do_vfs_ioctl` ITSELF (fs/ioctl.c:513-522,
Linux v6.18.46) — for a directory, a regular file or a symlink it returns 0
after copying the 8-byte `loff_t` from `inode_get_bytes` to `arg` (:517-519;
fs/stat.c:960-968, `(i_blocks << 9) + i_bytes` per include/linux/fs.h:3597-3600),
-EFAULT if that copy fails, and -ENOTTY for everything else (:522), before
`vfs_ioctl` is reached.  It is the request that would go wrong first if the
gate became a magic-letter test, the eight and it being all 'T': a
directory's real answer is a SUCCESS — return 0 with the count written
through `arg`, the directory's allocated bytes (4096 for a one-block ext4
directory; 0 on tmpfs, whose directories are charged no `i_blocks`,
mm/shmem.c:3096) — and the arm declines it.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem dir_fioqsize_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIOQSIZE i (fixture_of (fds := [(3, .FdDir)])) o ↔ o = Unmodeled := by
  sys_norm
/-- …and no success is admitted.  The outcome refuted here — return 0 with nothing written — is the kernel's return value shorn of its 8-byte write through `arg` (`do_vfs_ioctl`, fs/ioctl.c:517-519, Linux v6.18.46), the lie a return-only view of the syscall would tell; the `iff` above already refuses every `Ok`, the real one — 0 with `inode_get_bytes` at `arg` — included.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem dir_fioqsize_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 FIOQSIZE i (fixture_of (fds := [(3, .FdDir)])) (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and on a pipe FIOQSIZE really is -ENOTTY (fs/ioctl.c:522), from the
fd-generic half rather than the file's handler.  The arm declines it all
the same — the gate names the eight and nothing else — so this is a real
answer left unmodeled, like `/dev/null`'s below, not a wrong one.
kernel: fs/ioctl.c:do_vfs_ioctl@v6.18.46 -/
theorem pipe_fioqsize_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIOQSIZE i (fixture_of (fds := [(3, .FdPipe 0 false)])) o ↔ o = Unmodeled := by
  sys_norm

/-- For EVERY request outside the eight, on the standard channel: the arm
declines.  `tty_only_request` is the whole decision, so the pin is stated
on it.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem stdout_other_request_is_unmodeled (req : word) (i : SyscallInput)
    (o : outcome SyscallEffect) (h : tty_only_request req = false) :
    ioctl_spec 1 req i demo_model o ↔ o = Unmodeled := by
  sys_norm
  simp only [h, Bool.false_eq_true, ↓reduceIte, unmodeled_iff]

/-- For EVERY open kind, `/dev/null` and `/dev/urandom` included, EVERY
request outside the eight, on any model: the arm declines.  Stated over the entry itself, so a
kind that answered such a request would fail here rather than be missed
by a wildcard.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem open_fd_other_request_is_unmodeled (fd req : word) (e : FdEntry) (i : SyscallInput)
    (m : Model) (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some e)
    (hr : tty_only_request req = false) :
    ioctl_spec fd req i m o ↔ o = Unmodeled := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h]
  cases e <;> simp only [hr, Bool.false_eq_true, ↓reduceIte, unmodeled_iff]

/-! ## `/dev/null` answers the eight and declines the rest

`null_fops` (drivers/char/mem.c:644-652, Linux v6.18.46) has no
`.unlocked_ioctl`, so `vfs_ioctl` answers -ENOTTY to the eight from its
first branch (fs/ioctl.c:48-49), and the arm writes that answer down, as
Rocq's does: the kind is the one that reaches -ENOTTY through the
no-method branch rather than through an -ENOIOCTLCMD, and musl's
`__fdopen` issues TIOCGWINSZ on a stream freshly opened on the device, so
a declining kind would leave the modeled surface one syscall after an
`fopen` of "/dev/null".  Every request outside the eight is declined here
as on every other open kind. -/

/-- TCGETS on `/dev/null`: -ENOTTY, from `vfs_ioctl`'s first branch (fs/ioctl.c:48-49, Linux v6.18.46), `null_fops` having no `.unlocked_ioctl`.
kernel: fs/ioctl.c:vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem devnull_tcgets_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TCGETS i (fixture_of (fds := [(3, .FdDevNull true false)])) o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdDevNull true false)])) [] := by
  sys_norm
/-- …and -EINVAL is not admitted there: that is `/dev/urandom`'s answer,
`random_ioctl`'s default arm (drivers/char/random.c:1550-1551, Linux
v6.18.46), and the lie a model confusing the two character devices would
tell; `null_fops` has no handler to reach it.
kernel: drivers/char/random.c:random_ioctl; fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem devnull_tcgets_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TCGETS i (fixture_of (fds := [(3, .FdDevNull true false)]))
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute
/-- All eight terminal-only requests on `/dev/null`, opened for writing as
an `fopen` of the device leaves it; Rocq's
`ioctl_devnull_tty_only_requests_all_enotty`.
kernel: fs/ioctl.c:vfs_ioctl; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem devnull_tty_only_requests_all_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ∀ r ∈ tty_only_requests,
      (ioctl_spec 3 r i (fixture_of (fds := [(3, .FdDevNull false true)])) o ↔
        o = Ok (mkEffect (errno_ret ENOTTY) [] [])
          (fixture_of (fds := [(3, .FdDevNull false true)])) []) := by
  intro r hr
  simp only [tty_only_requests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> sys_norm
/-- FIONBIO on `/dev/null` opened for writing: declined, as on every open kind; `do_vfs_ioctl` (fs/ioctl.c:507-508, Linux v6.18.46) would set O_NONBLOCK on it.
kernel: fs/ioctl.c:vfs_ioctl,do_vfs_ioctl@v6.18.46 -/
theorem devnull_fionbio_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 FIONBIO i (fixture_of (fds := [(3, .FdDevNull false true)])) o ↔ o = Unmodeled := by
  sys_norm

/-- …with either access mode, on any model, for every terminal-only
request: the answer does not read the mode `open` granted.
kernel: fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem devnull_tty_request_is_enotty (fd req : word) (rd wr : Bool) (i : SyscallInput)
    (m : Model) (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some (.FdDevNull rd wr))
    (hr : tty_only_request req = true) :
    ioctl_spec fd req i m o ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, hr, ↓reduceIte]
  sys_norm

/-! ## `/dev/urandom` is declined on every request, and its real answer is -EINVAL

Unlike `/dev/null`, the random device HAS a handler: `urandom_fops`
(drivers/char/random.c:1572-1581, Linux v6.18.46) sets `.unlocked_ioctl =
random_ioctl` (:1575), and `random_ioctl` (:1492-1553) answers the RND*
requests — RNDGETENTCNT through `arg` (:1498-1502), the rest behind
`capable(CAP_SYS_ADMIN)` — and everything else that reaches it -EINVAL
from its default arm (:1550-1551); what `do_vfs_ioctl` claims first never
does (fs/ioctl.c:499-522, Linux v6.18.46).  So the eight of `tty_only_request` are -EINVAL there,
not -ENOTTY: a wildcard that let this kind inherit the -ENOTTY arm would
be WRONG, not merely incomplete, which is the case the enumerated match
exists for.  The arm declines, as Rocq's does, and the pins fix both
halves: `Unmodeled` is the only outcome, and neither the real -EINVAL nor
the wildcard's -ENOTTY is admitted. -/

/-- TCGETS on `/dev/urandom`: declined.  The request is a terminal's
(`tty_mode_ioctl`, drivers/tty/tty_ioctl.c:811-815, Linux v6.18.46); the
device's own handler answers it -EINVAL.
kernel: drivers/char/random.c:random_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem urandom_tcgets_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 3 TCGETS i (fixture_of (fds := [(3, .FdUrandom)])) o ↔ o = Unmodeled := by
  sys_norm

/-- …and the -EINVAL `random_ioctl`'s default arm really answers
(drivers/char/random.c:1550-1551, Linux v6.18.46) is not admitted: the
arm is fail-closed on this kind, as Rocq's is.
kernel: drivers/char/random.c:random_ioctl@v6.18.46 -/
theorem urandom_tcgets_einval_declined (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TCGETS i (fixture_of (fds := [(3, .FdUrandom)]))
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …nor is -ENOTTY, which is what a wildcard over the open kinds would
have answered and what `vfs_ioctl` never gives a file whose handler
answers (fs/ioctl.c:51-53, Linux v6.18.46).
kernel: drivers/char/random.c:random_ioctl; fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem urandom_tcgets_enotty_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 3 TCGETS i (fixture_of (fds := [(3, .FdUrandom)]))
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m' evs) := by
  sys_refute

/-- For every request, on any model holding the device: the decline reads
neither the request nor the model, exactly as `random_ioctl`'s answer
would depend on both (drivers/char/random.c:1492-1553, Linux v6.18.46).
kernel: drivers/char/random.c:random_ioctl@v6.18.46 -/
theorem urandom_any_request_is_unmodeled (fd req : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (h : fd_lookup (m_fds m) fd = some .FdUrandom) :
    ioctl_spec fd req i m o ↔ o = Unmodeled := by
  simp only [ioctl_spec.eq_1, bind_get_model_iff, h, unmodeled_iff]

/-! ## Through the dispatcher: the table line and the two 32-bit arguments

`SYSCALL_DEFINE3(ioctl, unsigned int, fd, unsigned int, cmd, unsigned
long, arg)` (fs/ioctl.c:583, Linux v6.18.46): `fd` and `cmd` are `unsigned
int`, so the high 32 bits of a0 and a1 are gone before `fd_empty` or the
switch sees them (`Syscall.fd32`, `Syscall.cmd32`), and `arg` is never
read on any path the arm models.  `ioctl_spec.c`'s `conform -- base` case
is the recorded run: `fd | HI`, `fd | HI_NEG` and `HI | TIOCGWINSZ` on the
open file (its 2nd, 3rd and 4th `ioctl`s, -ENOTTY), then `fd | HI` on the
closed fd, `HI + 999` and `BIT31 | 1` (its 6th, 10th and 11th, -EBADF).
`fd_truncation.c` issues no `ioctl`; its header defers to that probe. -/

/-- An argument of a literal input is the list's entry: what `in_arg` is,
stated so that `sys_norm` can read a register off an input whose memories
are symbolic (a closed term is evaluated by the second pass, and an input
carrying `mem` is not closed).
model: the reading of `in_arg` on a literal input, a rewrite for `sys_norm`; not a kernel claim. -/
@[local sys_simp] theorem in_arg_mkInput (n : word) (args : List word)
    (mem wmem : word → Option byte) (k : Nat) :
    in_arg (SyscallInput.mkInput n args mem wmem) k = args.getD k (Z_to_bv 64 0) := rfl

/-! …and the list's entry at a literal index, for a list that carries a
symbolic register (core's two `getD` equations). -/
attribute [local sys_simp] List.getD_cons_zero List.getD_cons_succ

/-- Syscall 29 is `ioctl`.  riscv64's number is scripts/syscall.tbl:42
(`29 common ioctl sys_ioctl compat_sys_ioctl`, Linux v6.18.46), rendered
by scripts/Makefile.asm-headers (its `unistd_%.h` rule) into the generated
`asm/unistd_64.h` that arch/riscv/include/uapi/asm/Kbuild:3 lists and
arch/riscv/include/uapi/asm/unistd.h:19-20 includes; since v6.11 riscv no
longer reads include/uapi/asm-generic/unistd.h at all
(Documentation/process/adding-syscalls.rst:256-269).  That header's
`#define __NR_ioctl 29` (include/uapi/asm-generic/unistd.h:95) is the same
table in `#define` form, spelling the same 29, and is what the evidence
line names because the checker resolves only a function or a `#define`.
Here fd 1, TIOCGWINSZ, a 4096 argument.
kernel: include/uapi/asm-generic/unistd.h:__NR_ioctl; fs/ioctl.c:vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem sysno_29_is_ioctl (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [1, TIOCGWINSZ, 4096, 0, 0, 0] mem wmem) demo_model o
      ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- …and 29 is in the modeled set the dispatcher is compared against
(`modeled_sysnos_iff_dispatched`).
kernel: include/uapi/asm-generic/unistd.h:__NR_ioctl@v6.18.46 -/
theorem ioctl_is_dispatched : (29 : Int) ∈ modeled_sysnos := by decide

/-- Input builder for request-shape declines, following `Select.ps_in`.
These pins decline argument shapes, not syscall 29 itself; the decline
register reader documents this helper form for that distinction.
`ioctl` takes fd, cmd, arg in this order (fs/ioctl.c:ioctl, Linux v6.18.46). -/
def ioctl_dispatch_input (fd req arg : word) (mem wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 29 [fd, req, arg, 0, 0, 0] mem wmem

attribute [local sys_simp low] ioctl_dispatch_input.eq_1

/-- All eight terminal-only requests through the dispatcher, each
-ENOTTY on stdout.  `cmd32` is the identity on each request word — the two
`_IOR`/`_IOW` ones carry bits 30 and 31, inside the low 32.
kernel: fs/ioctl.c:do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem sysno_29_tty_only_requests_all_enotty (mem wmem : word → Option byte)
    (o : outcome SyscallEffect) :
    ∀ r ∈ tty_only_requests,
      (syscall_spec (ioctl_dispatch_input 1 r 4096 mem wmem) demo_model o ↔
        o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model []) := by
  intro r hr
  simp only [tty_only_requests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> sys_norm

/-- FIONREAD through the dispatcher, the first half of Rocq's
`ioctl_other_request_is_error`, which offers the checker the success effect
and requires `CheckUnmodeled`: `do_vfs_ioctl` claims the request
(fs/ioctl.c:549-554, Linux v6.18.46) and writes the count through the third
argument the spec does not take, so the 0 the kernel really returns is not
admitted through syscall 29 either — `stdout_fionread_is_unmodeled` says the
arm declines; this says the dispatcher does not turn that decline into an
answer.  (Stated as a refutation rather than `↔ o = Unmodeled` because
`tools/check_decline_registers.py` reads a `syscall_spec … Unmodeled` pin on
a literal number as a decline register entry, and 29 is dispatched.)
kernel: fs/ioctl.c:do_vfs_ioctl; fs/pipe.c:pipe_ioctl@v6.18.46 -/
theorem sysno_29_fionread_success_rejected (mem wmem : word → Option byte) (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 29 [1, FIONREAD, 4096, 0, 0, 0] mem wmem) demo_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- FIONBIO through the dispatcher, the second half: `ioctl_fionbio`
(fs/ioctl.c:340-361, Linux v6.18.46) sets or clears O_NONBLOCK, state the
model does not carry, and returns 0; that 0 is not admitted through syscall
29.
kernel: fs/ioctl.c:do_vfs_ioctl,ioctl_fionbio@v6.18.46 -/
theorem sysno_29_fionbio_success_rejected (mem wmem : word → Option byte) (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 29 [1, FIONBIO, 4096, 0, 0, 0] mem wmem) demo_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- a0 = 2^32 + 1 is fd 1: -ENOTTY, not the -EBADF a 64-bit fd would get.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem fd_high_bits_dropped (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [4294967297, TIOCGWINSZ, 4096, 0, 0, 0] mem wmem)
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- The same on the RECORDED row: a0 = 2^32 + 3 is fd 3, a regular file
open for writing, -ENOTTY.  `ioctl_spec.c`'s `base` mode, second `ioctl`
(`fd | HI`), a2 = 0.
probe: testing/syscall-check/tests/ioctl_spec.c#conform -- base -/
theorem filew_fd_high_bits_dropped (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [4294967299, TIOCGWINSZ, 0, 0, 0, 0] mem wmem)
        (fixture_of (fds := [(3, .FdFileW [97] 0)])) o
      ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdFileW [97] 0)])) [] := by
  sys_norm

/-- Bit 31 of `fd` is part of the `unsigned int`, not high-half junk: a0 =
2^31 + 1 is fd 2147483649, not fd 1 — closed, -EBADF, on the same model.
`ioctl_spec.c`'s `base` mode, eleventh `ioctl` (`BIT31 | 1`).
probe: testing/syscall-check/tests/ioctl_spec.c#conform -- base -/
theorem fd_bit31_is_closed (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [2147483649, TIOCGWINSZ, 0, 0, 0, 0] mem wmem)
        (fixture_of (fds := [(3, .FdFileW [97] 0)])) o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) (fixture_of (fds := [(3, .FdFileW [97] 0)])) [] := by
  sys_norm
/-- …so -EBADF, the answer to the untruncated register, is refused: `fd_empty` sees fd 1 (fs/ioctl.c:583-589, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem fd_high_bits_ebadf_rejected (mem wmem : word → Option byte) (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 29 [4294967297, TIOCGWINSZ, 4096, 0, 0, 0] mem wmem)
        demo_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and a0 = 2^32 + 7 is fd 7, closed: -EBADF.
kernel: fs/ioctl.c:ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem fd_high_bits_closed_is_ebadf (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [4294967303, TIOCGWINSZ, 4096, 0, 0, 0] mem wmem)
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- `ioctl(-1, …)`, what a program passes after a failed `open`: a0 =
2^64-1 is fd 4294967295 after the `unsigned int` truncation, past the
table's `max_fds`, so in `files_lookup_fd_raw` (include/linux/fdtable.h:72-86,
Linux v6.18.46) `array_index_mask_nospec(fd, fdt->max_fds)` is zero (:75),
the load reads slot `fd & mask` = 0 — stdin's, an OPEN one (:84) — and the
mask then clears the loaded pointer to NULL (:85; the kernel's own comment
at :79-82 says so).  `__fget_light` returns `EMPTY_FD` on that NULL
(fs/file.c:1153-1178, the `!file` test at :1169-1170) and `fd_empty`
answers -EBADF.  The model's `fd_lookup` finds no such fd: the same answer
by a shorter road.
kernel: fs/ioctl.c:ioctl; include/linux/fdtable.h:files_lookup_fd_raw; fs/file.c:__fget_light; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem negative_fd_is_ebadf (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [18446744073709551615, TCGETS, 4096, 0, 0, 0] mem wmem)
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- A closed fd with the request AND the third argument SYMBOLIC, through
the dispatcher: -EBADF whatever they are.  `cmd` is truncated and then
never read, and `arg` is never read at all, because `fd_empty` returns
first (fs/ioctl.c:585-589, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem closed_fd_cmd_is_ebadf (req arg : word) (mem wmem : word → Option byte)
    (o : outcome SyscallEffect) :
    syscall_spec (ioctl_dispatch_input 7 req arg mem wmem) demo_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- A NULL third argument on a socket is not -EFAULT: before v5.15
`sock_do_ioctl` copied an `ifreq` from `arg` before testing the request
(the Rocq header's SOCKETS paragraph), and at v6.18.46 `get_user_ifreq`
sits behind `is_socket_ioctl_cmd` (include/linux/netdevice.h, Linux v6.18.46),
tested at net/socket.c:1264-1267, which no 'T'
request passes.  The spec admits -ENOTTY alone.
kernel: net/socket.c:sock_do_ioctl@v6.18.46 -/
theorem socket_tcgets_null_arg_efault_rejected (mem wmem : word → Option byte) (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 29 [3, TCGETS, 0, 0, 0, 0] mem wmem)
        (fixture_of (fds := [(3, .FdSocket .SkFresh)]))
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- a1 = 2^32 + TIOCGWINSZ is TIOCGWINSZ: -ENOTTY, where a 64-bit request
would be one the arm declines.
kernel: fs/ioctl.c:ioctl,vfs_ioctl@v6.18.46 -/
theorem cmd_high_bits_dropped (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [1, 4294988819, 4096, 0, 0, 0] mem wmem) demo_model o
      ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- The same on the RECORDED row, a regular file open for writing:
`ioctl_spec.c`'s `base` mode, fourth `ioctl` (`HI | TIOCGWINSZ`), a2 = 0.
probe: testing/syscall-check/tests/ioctl_spec.c#conform -- base -/
theorem filew_cmd_high_bits_dropped (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [3, 4294988819, 0, 0, 0, 0] mem wmem)
        (fixture_of (fds := [(3, .FdFileW [97] 0)])) o
      ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) (fixture_of (fds := [(3, .FdFileW [97] 0)])) [] := by
  sys_norm

/-- Bit 31 of `cmd` survives too: TIOCGPTN (0x80045430, its `_IOR`
direction bit) passes `cmd32` whole and reaches the gate — -ENOTTY, where
a 31-bit truncation would have left a request the arm declines.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem cmd_bit31_kept (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [1, TIOCGPTN, 4096, 0, 0, 0] mem wmem) demo_model o
      ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm
/-- …so `Unmodeled`, the arm's answer to the untruncated request, is refused: `cmd` is `unsigned int` (fs/ioctl.c:583, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem cmd_high_bits_unmodeled_rejected (mem wmem : word → Option byte) :
    ¬ syscall_spec (SyscallInput.mkInput 29 [1, 4294988819, 4096, 0, 0, 0] mem wmem)
        demo_model Unmodeled := by
  sys_refute

/-- The third argument is not read on the -ENOTTY path: ANY a2, and any
memory behind it, changes nothing — both are left symbolic to say so.
kernel: fs/ioctl.c:vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem arg_not_read (arg : word) (mem wmem : word → Option byte) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [2, TCGETS, arg, 0, 0, 0] mem wmem) demo_model o
      ↔ o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- A request outside the eight on a CLOSED fd: -EBADF, like every other
request there.  Linux `ioctl` resolves the fd first (fs/ioctl.c:585-589,
Linux v6.18.46), so the unknown request never reaches a handler.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_unknown_request_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 7 0xdeadbeef i demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- …so the arm does not decline there: the fd decides, not the request
(fs/ioctl.c:585-589, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_unknown_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 7 0xdeadbeef i demo_model Unmodeled := by
  sys_refute

/-- -ENOTTY on that closed fd is a lie: `fd_empty` answers before
`vfs_ioctl` could (fs/ioctl.c:588-589 against :596-597, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_unknown_enotty_not_ok (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 7 0xdeadbeef i demo_model (Ok (mkEffect (errno_ret ENOTTY) [] []) m' evs) := by
  sys_refute

/-- TCSETS on a closed fd: -EBADF, decided before the termios pointer is
read (fs/ioctl.c:585-589, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tcsets_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 7 TCSETS i demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- …and the arm does not decline it.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tcsets_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 7 TCSETS i demo_model Unmodeled := by
  sys_refute

/-- -EFAULT on that closed fd is not admitted: a terminal's `set_termios`
copy-in (drivers/tty/tty_ioctl.c:462-465, Linux v6.18.46) is reached only
through an OPEN descriptor, and `fd_empty` answers first
(fs/ioctl.c:588-589).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tcsets_efault_not_ok (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 7 TCSETS i demo_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- TCSETS on the standard channel: -ENOTTY, as the other seven are
(fs/ioctl.c:46-53 after :580, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tcsets_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 1 TCSETS i demo_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- …so the arm does not decline it on an open fd either.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tcsets_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 1 TCSETS i demo_model Unmodeled := by
  sys_refute

/-- -EFAULT is not admitted on the open channel: the copy-in that returns
it is a terminal's (`set_termios`, drivers/tty/tty_ioctl.c:462-465, Linux
v6.18.46), and the standard channels are not terminals.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tcsets_efault_not_ok (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 TCSETS i demo_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- TIOCSWINSZ on a closed fd: -EBADF.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocswinsz_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 7 TIOCSWINSZ i demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- …and the arm does not decline it.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocswinsz_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 7 TIOCSWINSZ i demo_model Unmodeled := by
  sys_refute

/-- -EFAULT on that closed fd is not admitted: the window a terminal reads
through the pointer (`tty_ioctl`, drivers/tty/tty_io.c:2709-2710, Linux
v6.18.46) is never read, `fd_empty` answering first (fs/ioctl.c:588-589).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocswinsz_efault_not_ok (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 7 TIOCSWINSZ i demo_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- TIOCSWINSZ on the standard channel: -ENOTTY.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocswinsz_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 1 TIOCSWINSZ i demo_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- …so the arm does not decline it on an open fd.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocswinsz_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 1 TIOCSWINSZ i demo_model Unmodeled := by
  sys_refute

/-- -EFAULT is not admitted on the open channel: only a terminal reads the
window through the pointer (`tty_ioctl`, drivers/tty/tty_io.c:2709-2710,
Linux v6.18.46).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocswinsz_efault_not_ok (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 TIOCSWINSZ i demo_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- TIOCSPTLCK on a closed fd: -EBADF.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocsptlck_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 7 TIOCSPTLCK i demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-- …and the arm does not decline it.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocsptlck_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 7 TIOCSPTLCK i demo_model Unmodeled := by
  sys_refute

/-- -EFAULT on that closed fd is not admitted: the lock flag a pty master
reads through the pointer (`pty_unix98_ioctl`, drivers/tty/pty.c:654-655,
Linux v6.18.46) is never read, `fd_empty` answering first
(fs/ioctl.c:588-589).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocsptlck_efault_not_ok (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 7 TIOCSPTLCK i demo_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- TIOCSPTLCK on the standard channel: -ENOTTY.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocsptlck_is_enotty (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 1 TIOCSPTLCK i demo_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model [] := by
  sys_norm

/-- …so the arm does not decline it on an open fd.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocsptlck_unmodeled_rejected (i : SyscallInput) :
    ¬ ioctl_spec 1 TIOCSPTLCK i demo_model Unmodeled := by
  sys_refute

/-- -EFAULT is not admitted on the open channel: only a pty master reads
the lock flag through the pointer (`pty_unix98_ioctl`,
drivers/tty/pty.c:654-655, Linux v6.18.46).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocsptlck_efault_not_ok (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ioctl_spec 1 TIOCSPTLCK i demo_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- TIOCGWINSZ on a closed fd: -EBADF, as on every closed fd.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocgwinsz_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ioctl_spec 7 TIOCGWINSZ i demo_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) demo_model [] := by
  sys_norm

/-! ## A17: FdFileRW and FdFileA -/

def a17_ioctl_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_ioctl_model.eq_1

/-- `ioctl(TCGETS)` through a read-write file is -ENOTTY, the answer the
same call takes on an `FdFile` (`vfs_ioctl`, fs/ioctl.c, Linux v6.18.46:
a regular file's `f_op` has no terminal handler), so the access mode the
`open` granted is not read.
kernel: fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem a17_rdwr_ioctl_is_enotty (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [3, 0x5401, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_ioctl_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) a17_ioctl_model [] := by
  sys_norm

def a17_ioctl_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_ioctl_append_model.eq_1

/-- `ioctl(TCGETS)` through an append-mode file is -ENOTTY, the answer the
same call takes on an `FdFileW` (`vfs_ioctl`, fs/ioctl.c, Linux v6.18.46:
a regular file's `f_op` has no terminal handler), so O_APPEND is not read.
kernel: fs/ioctl.c:vfs_ioctl@v6.18.46 -/
theorem a17_append_ioctl_is_enotty (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 29 [3, 0x5401, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_ioctl_append_model o ↔
      o = Ok (mkEffect (errno_ret ENOTTY) [] []) a17_ioctl_append_model [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Ioctl
