import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Ioctl

/-! # Checks.Cases.Checks.Sys.Fs.Ioctl — what the ioctl checker accepts, refuses and declines, read off against Linux

Pins over `Checks.Sys.Fs.Ioctl.check_ioctl`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/Ioctl.v`.  Not part of the trusted
specification: this file is QA on the checker, written to be READ, and every
claim in it is a claim about what the kernel does, with the citation beside
it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f), read in a
checkout at that commit.

WHAT THIS TWINS.  Rocq keeps the checker's worked examples for this syscall
in `Checks/Cases/Fs/Ioctl.v`, beside the spec's, as `Example`s over `check_syscall` on the demo process: the fd-first
requests on stdout answer -ENOTTY, the IOC_W requests decline, and
FIONREAD and FIONBIO decline.  The Lean tree keeps
spec pins and checker pins apart — `Checks/Cases/Fs/Ioctl.lean` pins the
spec, this file the checker — and this file is where those examples land.
They are stated on `check_ioctl_row`, the argument narrowing of Rocq's
`Dispatch.arm_ioctl` (`fd32` of a0 and `cmd32` of a1, handed to
`check_ioctl`).  The `V_Fs_Ioctl` section below restates the cases through
`check_syscall` beside the registration in `Checks/Arms/Fs/Ioctl.lean`.

The Rocq file is registered nowhere in the Lean tree yet: `tools/check_lean_cases_parity.py`
reads a coverage register only from the file that mirrors the Rocq file's
path, `Checks/Cases/Fs/Ioctl.lean`, which is the spec port's and not this
ticket's to edit, and a register at THIS path would claim a Rocq file that
does not exist.  The mapping is therefore prose, read by no guard; each
line is the Rocq `Example` followed by the theorems here that restate its
`check_syscall` conjuncts.  It stops being complete the day a theorem
restating a Rocq conjunct is added without a line.

- `ioctl_tiocgwinsz_enotty`: `stdout_tiocgwinsz_enotty_accepted`
- `ioctl_fd_first_requests_all_enotty`: `stdout_all_eight_enotty_accepted_or_declined`;
  `stdout_all_eight_success_rejected_or_declined` is the refusing half Rocq's example
  does not state, added here
- `ioctl_write_requests_are_unmodeled`: the three IOC_W conjuncts in
  `stdout_all_eight_enotty_accepted_or_declined` and the named
  `open_fd_*_efault_unmodeled` pins
- `ioctl_other_request_is_error`: `stdout_fionread_fionbio_declined`

WHY A CHECKER NEEDS PINS OF ITS OWN.  The lemmas of the checker's file tie
`check_ioctl` to `ioctl_spec` in both directions, and a checker that
declined every input would still meet them if the spec were changed to
match — which is the anti-pattern the port's acceptance names, and the one
this syscall is most exposed to, since two of its arms DO decline and a
third declines on most requests.  What the lemmas cannot see is a lie told
from OUTSIDE: an errno the kernel would not return, a ledger beside the one
it does, or a return that agrees only in its low half, offered to the
checker and required to be refused; and, on the declining arms, the
kernel's REAL answer offered and required to be neither accepted nor
refused.  That is what the pins below do.  Every equality is closed by
`rfl`: `Model` has no `DecidableEq`, so `decide` is unavailable, and the
checker on a closed input reduces to a constructor by evaluation alone.

WHAT MEASURES THESE PINS.  Nothing in the tree yet: `tools/lean_mutate.py`
builds a spec mutant against `Checks/Cases/Fs/Ioctl.lean` alone, so no
mutant of the checker is compiled against this file until that tool lists
a checker's pins beside the spec's.  The one measurement so far is the
hand-run pass in the deep-review record of the PR that landed this file:
every mutant of `check_ioctl` — each arm's answer swapped for a
neighbour's, the `tty_only_request` gate dropped or inverted, each kind
moved to the declining side, the model or the event list changed on an
accepting arm, the ledgers or the high half of the return ignored — died
under these pins alone, with the checker's relating lemmas stubbed out.

WHY EVERY EVIDENCE LINE IS A KERNEL READING.  `testing/syscall-check/tests/ioctl_spec.c`
runs most of these shapes against the kernel, but `tools/check_lean_pin_evidence.py`'s
polarity reader classes a statement by `¬`, `≠`, `False` and the word
`Unmodeled`, and `CheckUnmodeled` is not that word: a `= CheckReject` or
`= CheckUnmodeled` verdict reads as positive there, so the `reject --mutate`
or `fail-closed` case that matches it would be refused as the wrong
polarity.  The spec pins beside these carry the probe lines.  The same
tool holds every request name a statement spells to a cited function that
spells it, and TCGETS and its seven siblings are spelled, of the handlers
any fd kind this model holds can reach, only in the terminal ones —
`tty_mode_ioctl`, `tty_ioctl`, `tty_jobctrl_ioctl`, `pty_unix98_ioctl` and
its BSD twin `pty_bsd_ioctl`: that is why a terminal handler is cited on pins where no terminal code
runs — a closed fd, a character device, the width and truncation pins —
and on those the function that decides the pin is the one named first on
the line.  The header of `Checks/Cases/Fs/Ioctl.lean` says the same of
the spec pins.

THE FIXTURES.  Rocq's examples run on the demo process, `demo_model` of
`Checks/Cases/Prelude.lean` (the three standard channels and nothing
else), and the pins that restate them do too.  The kinds Rocq's examples
do not reach are on `ioctl_kinds_model` below, one fd per kind the Lean
`FdEntry` can hold; which fd holds which kind is said once, at its
definition, and each pin names the kind it relies on.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree on what is
accepted, what is refused and what is left unanswered. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Ioctl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Ioctl

/-- The register file of an `ioctl(fd, req, arg)` call, as the tracer
records it: syscall 29, the fd in a0, the request in a1, a page-aligned
third argument the checker never reads, no memory.  Rocq's examples pass
4096 there too.  With no memory the page at 4096 is unmapped, so for a
request that reads or writes through the pointer the kernel's answer under
THIS input would be -EFAULT; where a pin below offers "the real answer" to
such a request it offers what a readable pointer earns, the shape the
probes record, and the checker declines the request either way. -/
def ioctl_in (fd req : word) : SyscallInput :=
  SyscallInput.mkInput 29 [fd, req, 4096, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The body of the arm the checked table will hold for 29: Rocq's
`Dispatch.arm_ioctl` hands `check_ioctl` the low 32 bits of a0 and a1,
the `unsigned int fd, cmd` of `SYSCALL_DEFINE3(ioctl, …)` (fs/ioctl.c:583,
Linux v6.18.46).  Spelled once so every pin below applies the checker the
way the dispatcher will. -/
def check_ioctl_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m

/-- One fd of every kind the Lean `FdEntry` can hold, beside the three
channels: a read-only file, a file opened for writing, a directory, a
socket, both ends of one pipe, /dev/null and /dev/urandom.  fd 10 is
left closed. -/
def ioctl_kinds_fds : List (word × FdEntry) :=
  init_fds ++
  [ (3, .FdFile [97] 0), (4, .FdFileW [98] 0), (5, .FdDir),
    (6, .FdSocket .SkFresh), (7, .FdPipe 0 false), (8, .FdPipe 0 true),
    (9, .FdDevNull true false), (11, .FdUrandom) ]

def ioctl_kinds_model : Model :=
  fixture_of (fds := ioctl_kinds_fds) (pipes := [(0, ([], 0))]) (fs := [([97], [120]), ([98], [121])])

/-! ## Rocq's examples: the channel arm on stdout

`SYSCALL_DEFINE3(ioctl, …)` (fs/ioctl.c:583-600, Linux v6.18.46) resolves
the fd (:585-589), tries `do_vfs_ioctl` (fs/ioctl.c:492-581) and, on its
-ENOIOCTLCMD (:580), `vfs_ioctl` (fs/ioctl.c:44-56), which starts from
-ENOTTY (:46) and keeps it for a file whose table has no `.unlocked_ioctl`
(:48-49) or whose handler answers -ENOIOCTLCMD (:51-53).  The model's
channels are pipe ends under the harness, whose `pipe_ioctl`
(fs/pipe.c:619-656, Linux v6.18.46) answers -ENOIOCTLCMD to every request
of type 'T' but FIONREAD (:653-654; the two `CONFIG_WATCH_QUEUE` arms,
:639-651, are type 'W'); none of the eight of `tty_only_request` is
claimed by any handler a pipe end reaches — the terminal handlers the
spec's docstring walks are the only claimants among the tables any fd kind
of this model can hold — so on stdout each is -ENOTTY.  The second conjunct of the
first pin is what makes the first non-vacuous: a kernel claiming SUCCESS
is refused, so this pins -ENOTTY rather than merely accepting it. -/

/-- Rocq's first example: TIOCGWINSZ on stdout is -ENOTTY with the model
unchanged and no event, and a kernel reporting 0 there — the answer
`tty_ioctl` gives a real terminal (drivers/tty/tty_io.c:2707-2708, Linux
v6.18.46) — is refused.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_enotty_accepted :
    check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect 0 [] []) demo_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- Retain all eight terminal-only requests. Linux returns ENOTTY on
stdout for them; only the five fd-first cases are accepted across the
supported implementations. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

Of the handlers any fd kind of this model can reach,
each is claimed only by terminal ones — the four named here and, under
`CONFIG_LEGACY_PTYS`, the BSD twin `pty_bsd_ioctl` (drivers/tty/pty.c:453,
Linux v6.18.46) for TIOCSPTLCK and TIOCGPTN (:457, :467-468, the latter
answered -EINVAL there) — and by nothing a pipe end reaches: TCGETS and
TCSETS by `tty_mode_ioctl`
(drivers/tty/tty_ioctl.c:802-803, :811-815, Linux v6.18.46), TIOCSCTTY and
TIOCNOTTY by `tty_jobctrl_ioctl` (drivers/tty/tty_jobctrl.c:578-584),
TIOCGWINSZ and TIOCSWINSZ by `tty_ioctl` (drivers/tty/tty_io.c:2707-2710),
TIOCGPTN and TIOCSPTLCK by `pty_unix98_ioctl` (drivers/tty/pty.c:646-647,
:654-655).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/pipe.c:pipe_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem stdout_all_eight_enotty_accepted_or_declined :
    check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 TCSETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 TIOCSCTTY) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 TIOCSWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 TIOCNOTTY) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 TIOCGPTN) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 TIOCSPTLCK) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Success on stdout is rejected for the five fd-first requests and
declined for the three IOC_W requests: the handlers named in the pin above return 0 or write through the
third argument only on a tty (`pty_bsd_ioctl`'s TIOCGPTN arm answers
-EINVAL instead, never 0), and the standard channels are not one (the
spec twin's header records that environment obligation).

The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem stdout_all_eight_success_rejected_or_declined :
    check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TCSETS) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 TIOCSCTTY) (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCSWINSZ) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 TIOCNOTTY) (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCGPTN) (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCSPTLCK) (mkEffect 0 [] []) demo_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Rocq's third example, and its fail-closed half made explicit.  FIONREAD
and FIONBIO are `do_vfs_ioctl`'s own (fs/ioctl.c:549-554 and :507-508,
Linux v6.18.46): on a pipe end FIONREAD is answered by `pipe_ioctl` with
the buffered byte count written through the third argument (fs/pipe.c:625-637),
and FIONBIO flips O_NONBLOCK, a flag this model does not carry.  A success
offered for either is DECLINED, not accepted and not refused; and so is
the -ENOTTY a checker might have copied from the terminal-only arm — the
kernel's answer to both is 0 when the third argument is a usable pointer
(FIONREAD writes through it, fs/pipe.c:637; FIONBIO reads its flag through
it first, `ioctl_fionbio`, fs/ioctl.c:345) and -EFAULT when it is not, and
neither is -ENOTTY while the far end is the pipe the harness installs (on
a `/dev/null` far end FIONREAD would be -ENOTTY, `vfs_ioctl`'s no-method
answer, fs/ioctl.c:48-49), so under the environment obligation the spec
twin's header records, accepting -ENOTTY would accept a lie, and rejecting
it would claim an answer the model does not have.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; fs/pipe.c:pipe_ioctl@v6.18.46 -/
theorem stdout_fionread_fionbio_declined :
    check_ioctl_row (ioctl_in 1 FIONREAD) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 FIONBIO) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 FIONREAD) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 FIONBIO) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 FIONREAD) (mkEffect 0 [(4096, [0, 0, 0, 0])] []) demo_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The other four requests `do_vfs_ioctl` claims before any handler runs
(fs/ioctl.c:499-522, Linux v6.18.46) — FIOCLEX and FIONCLEX, which set
and clear close-on-exec (:499-505), FIOASYNC (:510-511) and FIOQSIZE,
which on a pipe end is `do_vfs_ioctl`'s own -ENOTTY (:522) — are
declined on stdout with the kernel's real answer offered: 0 for the first
three (FIOASYNC, like FIONBIO, first reads its flag through the third
argument, `ioctl_fioasync`, fs/ioctl.c:369; 0 is its answer for a readable
one that leaves the FASYNC state as it is — when the flag changes, :375-382
hand the request to the table's `.fasync`, `pipe_fasync` on a pipe end,
and answer -ENOTTY where a table has none), -ENOTTY for the last.  The decline on FIOQSIZE hides a real
-ENOTTY, which is what fail-closed costs here.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem stdout_do_vfs_ioctl_requests_declined :
    check_ioctl_row (ioctl_in 1 FIOCLEX) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 FIONCLEX) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 FIOASYNC) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 1 FIOQSIZE) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Lies on the answering arm

`vfs_ioctl` (fs/ioctl.c:44-56, Linux v6.18.46) returns -ENOTTY without
calling anything when the table has no method, and `pipe_ioctl`'s default
arm (fs/pipe.c:653-654) returns before it touches user memory; the
terminal handlers that would write are never entered.  So -ENOTTY comes
with no write, no zero-fill, no unmap, no copy and no copy-in, and it is
the only errno on this path. -/

/-- A ledger beside -ENOTTY is refused, one conjunct per ledger, on the
TIOCGWINSZ of Rocq's first example.  The relating lemmas cannot see an
acceptor widened on one arm in both twins at once, and the prelude's own
refutations pin the helper, not that an arm uses it; a conjunct per
ledger can.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/pipe.c:pipe_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem stdout_enotty_with_a_ledger_rejected :
    check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [(4096, [0])] []) demo_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] [(4096, 4096)]) demo_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCGWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [(4096, 4096)] [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCGWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) demo_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TIOCGWINSZ)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret ENOTTY) [] [])) demo_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The wrong errnos on stdout, each real somewhere and each refused here:
-EBADF is the syscall's answer to a CLOSED fd (fs/ioctl.c:588-589, Linux
v6.18.46), which fd 1 is not; -EINVAL is `random_ioctl`'s default answer
(drivers/char/random.c:1550-1551), reached through `random_fops` (:1564)
and `urandom_fops` (:1575), of which this model holds only the latter;
-ENOIOCTLCMD (515, include/linux/errno.h:17) is the handler's answer
`vfs_ioctl` translates and never lets out (fs/ioctl.c:51-53); -EFAULT is
`tty_mode_ioctl`'s on a terminal whose user buffer is unwritable
(drivers/tty/tty_ioctl.c:813-814), and there is no terminal; -ENOSYS (38)
is `sys_ni_syscall`'s answer for a number with no entry (kernel/sys_ni.c:20-22),
and 29 has one.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/char/random.c:random_ioctl; include/linux/errno.h:ENOIOCTLCMD; drivers/tty/tty_ioctl.c:tty_mode_ioctl; include/uapi/asm-generic/errno.h:ENOSYS; kernel/sys_ni.c:sys_ni_syscall@v6.18.46 -/
theorem stdout_wrong_errnos_rejected :
    check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (errno_ret 515) [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (errno_ret 38) [] []) demo_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The return is compared at 64 bits.  `vfs_ioctl`'s `int` is widened
into the `long` the `SYSCALL_DEFINE3` body returns (fs/ioctl.c:583-600,
Linux v6.18.46), so -ENOTTY fills the register with ones: its
zero-extended low half, 2^32 - 25, is refused on stdout, and -EBADF's,
2^32 - 9, on a closed fd.  A checker comparing `abi_low32` of both sides
accepts both.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem return_is_compared_at_full_width :
    check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (Z_to_bv 64 (2 ^ 32 - 25)) [] []) demo_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (Z_to_bv 64 (2 ^ 32 - 9)) [] []) demo_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-! ## Linux resolves the fd first; the model first checks agreement with QEMU

`SYSCALL_DEFINE3(ioctl, …)` (fs/ioctl.c:583-600, Linux v6.18.46) opens with
`CLASS(fd, f)(fd)` (:585) and returns -EBADF on `fd_empty(f)` (:588-589)
before `security_file_ioctl` or `do_vfs_ioctl` sees `cmd`.
The spec's fd-first gate explains why that order is not universal across
supported implementations. fd 3 is closed in demo_model. -/

/-- fd 3 is -EBADF on TCGETS, with 0 and -ENOTTY refused.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem closed_fd_ebadf_accepted :
    check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The former closed-fd EBADF rule must not bypass the request gate:
FIONBIO and FIONREAD now decline even with the Linux answer offered.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl@v6.18.46 -/
theorem closed_fd_other_requests_declined :
    check_ioctl_row (ioctl_in 3 FIONBIO) (mkEffect (errno_ret EBADF) [] []) demo_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 3 FIONBIO) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 3 FIONREAD) (mkEffect (errno_ret EBADF) [] []) demo_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 3 FIONREAD) (mkEffect 0 [] []) demo_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An errno return is as inert as a success: the syscall returns before
any file is touched (fs/ioctl.c:588-589, Linux v6.18.46), so a write, a
zero-fill, an unmap, a copy or a copy-in beside -EBADF is refused — one
conjunct per ledger.
kernel: fs/ioctl.c:ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem closed_fd_ebadf_with_a_ledger_rejected :
    check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret EBADF) [(4096, [0])] []) demo_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret EBADF) [] [(4096, 4096)]) demo_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS)
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [(4096, 4096)] [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS)
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) demo_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret EBADF) [] [])) demo_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Both arguments arrive truncated to 32 bits

`SYSCALL_DEFINE3(ioctl, unsigned int, fd, unsigned int, cmd, unsigned long, arg)`
(fs/ioctl.c:583, Linux v6.18.46) takes the fd and the request as
`unsigned int`, and the wrapper narrows each register to it
(`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-88,
through `__SC_CAST`, include/linux/syscalls.h:132, Linux v6.18.46).  So
`ioctl(2^32 + 1, …)` IS `ioctl(1, …)`, and a request whose high half is
set names the request in its low half.  Truncation ALIASES rather than
REJECTS: the refused conjuncts offer the answer of an arm that handed the
whole register on. -/

/-- 2^32 + 1 and 1 name the same fd, the shared answer is an acceptance of
-ENOTTY, and -EBADF — the answer of a checker that did not truncate — is
refused; 2^32 + 3 names the closed fd 3, and -1 truncates to 0xFFFFFFFF,
which names no fd.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem fd_truncates_to_32_bits :
    check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 32 + 1)) TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = check_ioctl_row (ioctl_in 1 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 32 + 1)) TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 32 + 1)) TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 32 + 3)) TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (-1)) TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (-1)) TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The request is truncated the same way: 2^32 + TCGETS and a negative
register whose low half is TCGETS (21505, include/uapi/asm-generic/ioctls.h:20,
Linux v6.18.46) both name TCGETS and are -ENOTTY on stdout, where a
checker matching the whole register would have declined them; and a
request whose low half is FIONREAD with its high half set is declined as
FIONREAD is, not answered.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem cmd_truncates_to_32_bits :
    check_ioctl_row (ioctl_in 1 (Z_to_bv 64 (2 ^ 32 + 21505))) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 (Z_to_bv 64 (-(2 ^ 32) + 21505))) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 (Z_to_bv 64 (2 ^ 32 + 21505))) (mkEffect 0 [] []) demo_model
      = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 (Z_to_bv 64 (2 ^ 32 + 21531))) (mkEffect 0 [] []) demo_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## `vfs_ioctl`: -ENOTTY on every open kind, from its own handler

The kinds Rocq's examples do not reach, on the wider fixture.  Each open
kind reaches -ENOTTY through a different table, all walked on the spec's
docstring: a regular file and a directory through ext4's `__ext4_ioctl`
default arm (fs/ext4/ioctl.c:1929-1930, Linux v6.18.46), or through
`vfs_ioctl`'s no-method branch on tmpfs; a pipe end through `pipe_ioctl`'s
-ENOIOCTLCMD (fs/pipe.c:653-654) mapped by `vfs_ioctl` (fs/ioctl.c:51-53);
a socket through `sock_do_ioctl` (net/socket.c:1264-1265), whose
`is_socket_ioctl_cmd` test fails every request of type 'T'.  The refusal
beside each is 0, the answer of a real terminal. -/

/-- Preserve the original request/kind fixtures: TCSETS and TIOCSWINSZ
decline, while the other requests still accept ENOTTY. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

One request per kind is enough here because the six kinds share
one alternative of `check_ioctl`, gated by the spec's own
`tty_only_request` and pinned five-fold on stdout above; the symbolic
pins at the end of this file fix each kind for every request and model.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/ext4/ioctl.c:__ext4_ioctl; fs/pipe.c:pipe_ioctl; net/socket.c:sock_do_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl@v6.18.46 -/
theorem enotty_on_every_open_kind_or_declined :
    check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckOk ioctl_kinds_model []
    ∧ check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect 0 [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckOk ioctl_kinds_model []
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY) (mkEffect 0 [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckOk ioctl_kinds_model []
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect 0 [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckOk ioctl_kinds_model []
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ) (mkEffect 0 [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 8 TCSETS) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 TCSETS) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Wrong errnos are rejected on answering requests; on the original
IOC_W fixtures every offered effect is declined. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

The precedence lie and the neighbour's errno on every open kind: an
OPEN fd passes the syscall's `fd_empty` test (fs/ioctl.c:588-589, Linux
v6.18.46), so -EBADF is refused on each answering request; -EINVAL, `random_ioctl`'s default
(drivers/char/random.c:1550-1551) and `do_vfs_ioctl`'s for FIGETBSZ on an
anonymous superblock (fs/ioctl.c:535-536), is reached by none of these
requests on any of these tables; and the socket is not -ENOTSOCK, which is
`sockfd_lookup`'s answer (net/socket.c:552-565) to a descriptor that is
NOT a socket — the ioctl path never asks.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/char/random.c:random_ioctl; net/socket.c:sockfd_lookup; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl@v6.18.46 -/
theorem open_kinds_wrong_errnos_rejected_or_declined :
    check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ) (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY) (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect (errno_ret ENOTSOCK) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ) (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 8 TCSETS) (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 TCSETS) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original per-kind ledger lies are rejected on fd-first requests
and declined on IOC_W requests. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

Every -ENOTTY on these tables is returned before any
user memory is touched: `vfs_ioctl`'s no-method branch (fs/ioctl.c:48-49,
Linux v6.18.46) calls nothing, `__ext4_ioctl`'s default arm returns the
errno outright (fs/ext4/ioctl.c:1929-1930), `pipe_ioctl`'s default arm
(fs/pipe.c:653-654) and `tcp_ioctl`'s (net/ipv4/tcp.c:682-683) return
-ENOIOCTLCMD without a `put_user`, and `sock_do_ioctl` reaches
`get_user_ifreq` only for a socket-type command (net/socket.c:1264-1267).
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/ext4/ioctl.c:__ext4_ioctl; fs/pipe.c:pipe_ioctl; net/socket.c:sock_do_ioctl; net/ipv4/tcp.c:tcp_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl@v6.18.46 -/
theorem enotty_with_a_ledger_rejected_or_declined_on_every_kind :
    -- fd 3, the read-only file: a write, a zero-fill, an unmap, a copy, a copy-in
    check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret ENOTTY) [(4096, [0])] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (errno_ret ENOTTY) [] [(4096, 4096)]) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [(4096, 4096)] [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 3 TCGETS)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret ENOTTY) [] [])) ioctl_kinds_model = CheckReject
    -- fd 4, the write fd
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ) (mkEffect (errno_ret ENOTTY) [(4096, [0])] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ) (mkEffect (errno_ret ENOTTY) [] [(4096, 4096)]) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [(4096, 4096)] [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret ENOTTY) [] [])) ioctl_kinds_model = CheckUnmodeled
    -- fd 5, the directory
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY) (mkEffect (errno_ret ENOTTY) [(4096, [0])] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY) (mkEffect (errno_ret ENOTTY) [] [(4096, 4096)]) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [(4096, 4096)] [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret ENOTTY) [] [])) ioctl_kinds_model = CheckReject
    -- fd 6, the socket
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [(4096, [0])] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] [(4096, 4096)]) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [(4096, 4096)] [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret ENOTTY) [] [])) ioctl_kinds_model = CheckReject
    -- fd 7, the read end of the pipe
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [(4096, [0])] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] [(4096, 4096)]) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [(4096, 4096)] [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret ENOTTY) [] [])) ioctl_kinds_model = CheckReject
    -- fd 8, the write end of the pipe
    ∧ check_ioctl_row (ioctl_in 8 TCSETS) (mkEffect (errno_ret ENOTTY) [(4096, [0])] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 TCSETS) (mkEffect (errno_ret ENOTTY) [] [(4096, 4096)]) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 TCSETS)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [(4096, 4096)] [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 TCSETS)
        (SyscallEffect.mkEffectU (errno_ret ENOTTY) [] [] [] [MemCopy.mkCopy 4096 8192 16] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 TCSETS)
        (with_copyins [(4096, 1)] (mkEffect (errno_ret ENOTTY) [] [])) ioctl_kinds_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Truncated errnos are rejected on the answering requests and declined
on the original IOC_W fixtures. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

The 64-bit comparison on the wider fixture: 2^32 - 25, -ENOTTY's
zero-extended low half, is refused on every open kind for the five fd-first requests, as
`return_is_compared_at_full_width` refuses it on stdout.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl@v6.18.46 -/
theorem return_width_rejected_or_declined_on_every_kind :
    check_ioctl_row (ioctl_in 3 TCGETS) (mkEffect (Z_to_bv 64 (2 ^ 32 - 25)) [] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 4 TIOCSWINSZ) (mkEffect (Z_to_bv 64 (2 ^ 32 - 25)) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 5 TIOCSCTTY) (mkEffect (Z_to_bv 64 (2 ^ 32 - 25)) [] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 6 TIOCGWINSZ) (mkEffect (Z_to_bv 64 (2 ^ 32 - 25)) [] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 7 TIOCGWINSZ) (mkEffect (Z_to_bv 64 (2 ^ 32 - 25)) [] []) ioctl_kinds_model
        = CheckReject
    ∧ check_ioctl_row (ioctl_in 8 TCSETS) (mkEffect (Z_to_bv 64 (2 ^ 32 - 25)) [] []) ioctl_kinds_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## What the open arms decline, with the real answer offered

A request outside the eight is declined on every open kind, whatever is
offered, and the offers below are the kernel's real answers, so that each
decline is seen to hide one: FIONREAD on a regular file is
`i_size - f_pos` written through the third argument (fs/ioctl.c:549-554,
Linux v6.18.46), on a pipe end the buffered count (fs/pipe.c:625-637), on
a TCP socket the unread bytes (`tcp_ioctl`'s SIOCINQ arm,
net/ipv4/tcp.c:651-657, written through the pointer by its caller); on a
directory `do_vfs_ioctl` hands FIONREAD to `vfs_ioctl` (:550-551), which
reaches `__ext4_ioctl`'s default arm on ext4 and `vfs_ioctl`'s own
no-method branch (:48-49) on the tmpfs the harness runs in — so the
directory's real answer is -ENOTTY either way, and the checker declines it
all the same.  That is the
fail-closed cost Rocq accepts, and these pins fix that it is paid as a
decline, never as an acceptance and never as a refusal. -/

/-- FIONREAD on every open kind: a success with a four-byte write is
declined — 1 on the two one-byte files of the fixture (`i_size` 1 less
`f_pos` 0, fs/ioctl.c:553-554, Linux v6.18.46; `FMODE_READ` is not
checked there, so the write-only fd is answered too), 0 on the fresh
socket and on both ends of the empty pipe; so is a bare success; and so
is -ENOTTY, the directory's real answer and a lie on the others.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; fs/pipe.c:pipe_ioctl; fs/ext4/ioctl.c:__ext4_ioctl@v6.18.46 -/
theorem fionread_declined_on_every_open_kind :
    check_ioctl_row (ioctl_in 3 FIONREAD) (mkEffect 0 [(4096, [1, 0, 0, 0])] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 3 FIONREAD) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 FIONREAD) (mkEffect 0 [(4096, [1, 0, 0, 0])] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 FIONREAD) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 5 FIONREAD) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 5 FIONREAD) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 6 FIONREAD) (mkEffect 0 [(4096, [0, 0, 0, 0])] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 7 FIONREAD) (mkEffect 0 [(4096, [0, 0, 0, 0])] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 FIONREAD) (mkEffect 0 [(4096, [0, 0, 0, 0])] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 8 FIONREAD) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every open kind declines every request outside the eight, whatever the
effect offered: the spec's own pin `open_fd_other_request_is_unmodeled`
carried through the checker's completeness lemma for declines.  Stated
over the entry itself, so a kind that answered such a request would fail
here rather than be missed by a wildcard.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem open_fd_other_request_declined (fd req : word) (e : FdEntry) (eff : SyscallEffect)
    (m : Model) (h : fd_lookup (m_fds m) fd = some e) (hr : tty_only_request req = false) :
    check_ioctl fd req eff m = CheckUnmodeled :=
  check_ioctl_complete_unmodeled fd req m (ioctl_in fd req) eff
    ((open_fd_other_request_is_unmodeled fd req e (ioctl_in fd req) m Unmodeled h hr).mpr rfl)

/-! ## `/dev/null` and `/dev/urandom` decline every request

Two arms decline even the eight, and on each the decline hides a real
answer the pins offer and require left unanswered.  `null_fops`
(drivers/char/mem.c:644-652, Linux v6.18.46) has no `.unlocked_ioctl`, so
`vfs_ioctl` answers -ENOTTY to the eight from its no-method branch
(fs/ioctl.c:48-49); `urandom_fops` (drivers/char/random.c:1572-1581) has
`.unlocked_ioctl = random_ioctl` (:1575), whose default arm answers
-EINVAL (drivers/char/random.c:1550-1551, Linux v6.18.46) to everything
`do_vfs_ioctl` does not claim first — the eight among them.  Neither
answer is written
into the model, so neither is accepted; and neither is REFUSED, because a
`CheckReject` there would claim an answer the model does not have. -/

/-- `/dev/null` (fd 9): TCGETS is declined with -ENOTTY (the real answer),
0 and -EINVAL (the neighbouring `/dev/urandom`'s answer, `random_ioctl`'s
default, offered here as the lie a checker confusing the two devices would
tell) offered; FIONBIO is declined with 0 (the real answer for a readable
third argument, `do_vfs_ioctl`'s, fs/ioctl.c:507-508 and :345) offered.
`memory_open` (drivers/char/mem.c:707-727, Linux v6.18.46) is the `.open`
that hands the null minor its table, `null_fops` (`devlist[3]`, :694;
the assignment at :720), which has no `.unlocked_ioctl` (:644-652) — the
no-method branch of `vfs_ioctl` (fs/ioctl.c:48-49) is where the real
-ENOTTY comes from.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/char/mem.c:memory_open; drivers/char/random.c:random_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem devnull_declines_every_request :
    check_ioctl_row (ioctl_in 9 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 9 TCGETS) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 9 TCGETS) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 9 FIONBIO) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `/dev/urandom` (fd 11): TCGETS is declined with -EINVAL (the real
answer), -ENOTTY (the answer of a checker that treated it as one more
open kind) and 0 offered; FIONBIO is declined with 0 offered.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/char/random.c:random_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem urandom_declines_every_request :
    check_ioctl_row (ioctl_in 11 TCGETS) (mkEffect (errno_ret EINVAL) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 11 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 11 TCGETS) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 11 FIONBIO) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- fd 10 is the gap in `ioctl_kinds_fds`: -EBADF is accepted there, and 0
and -ENOTTY are refused, as on `demo_model`'s fd 3.  The `none` arm reads
no fixture, so this pins only that the wider table did not fill the
number.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem closed_fd_on_kinds_is_ebadf :
    check_ioctl_row (ioctl_in 10 TCGETS) (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model
        = CheckOk ioctl_kinds_model []
    ∧ check_ioctl_row (ioctl_in 10 TCGETS) (mkEffect 0 [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 10 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-! ## Where nothing declines

A checker that answered `CheckUnmodeled` on every input would meet its
five obligations against a spec that declined everywhere, and no lemma of
the checker's file could tell.  After the fd-first request gate, the spec answers on a closed fd and
on a terminal-only request over every channel, whatever the model
(`Checks/Cases/Fs/Ioctl.lean`'s `closed_fd_is_ebadf` and
`channel_tty_request_is_enotty`), and the checker's soundness for declines
carries that over: on those arms, whatever the offered effect,
`check_ioctl` answers. -/

/-- No closed fd is declined, on any model and for any request passing the fd-first gate, and -EBADF
is accepted there with the model unchanged: a decline of the checker would
be a decline of the spec, and the spec's only outcome there is -EBADF (the
first half through the checker's soundness for declines, the second
through its completeness for acceptances — the half the concrete pins
above cannot state, since a checker that hands back a model differing from
the given one only off both fixtures passes every `rfl` here).
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem closed_fd_never_declines (fd req : word) (eff : SyscallEffect) (m : Model)
    (h : fd_lookup (m_fds m) fd = none) (hg : ioctl_fd_first_request req = true) :
    check_ioctl fd req eff m ≠ CheckUnmodeled
    ∧ check_ioctl fd req (mkEffect (errno_ret EBADF) [] []) m = CheckOk m [] := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hs := (closed_fd_is_ebadf fd req (ioctl_in fd req) m Unmodeled h hg).mp
      (check_ioctl_sound_unmodeled fd req eff m (ioctl_in fd req) hu)
    cases hs
  · exact check_ioctl_complete_ok fd req (mkEffect (errno_ret EBADF) [] []) m m [] (ioctl_in fd req)
      ((closed_fd_is_ebadf fd req (ioctl_in fd req) m
        (Ok (mkEffect (errno_ret EBADF) [] []) m []) h hg).mpr rfl)

/-- No fd-first terminal-only request on a channel is declined, on any model, and
-ENOTTY is accepted there: the first from the spec's pin through the
checker's soundness for declines, the second through its completeness for
acceptances.
kernel: fs/ioctl.c:ioctl,vfs_ioctl@v6.18.46 -/
theorem channel_tty_request_never_declines (fd req c : word) (eff : SyscallEffect) (m : Model)
    (h : fd_lookup (m_fds m) fd = some (.FdChannel c)) (hr : tty_only_request req = true) (hg : ioctl_fd_first_request req = true) :
    check_ioctl fd req eff m ≠ CheckUnmodeled
    ∧ check_ioctl fd req (mkEffect (errno_ret ENOTTY) [] []) m = CheckOk m [] := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hs := (channel_tty_request_is_enotty fd req c (ioctl_in fd req) m Unmodeled h hr hg).mp
      (check_ioctl_sound_unmodeled fd req eff m (ioctl_in fd req) hu)
    cases hs
  · exact check_ioctl_complete_ok fd req (mkEffect (errno_ret ENOTTY) [] []) m m [] (ioctl_in fd req)
      ((channel_tty_request_is_enotty fd req c (ioctl_in fd req) m
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m []) h hr hg).mpr rfl)

/-- The same refusal on one concrete answer, WITHOUT the checker's lemmas
in the proof: the pins above die with `check_ioctl_sound_unmodeled`, this
one with the checker alone.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_never_declines_directly :
    check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      ≠ CheckUnmodeled := by
  intro h
  have h0 : check_ioctl_row (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model [] := rfl
  rw [h0] at h
  cases h

/-! ## The other five answering kinds, symbolically

`channel_tty_request_never_declines` above fixes the channel kind for every
request and model; the five kinds beside it in the -ENOTTY alternative get
the same statement here, each through the spec's own per-kind pin
(`Checks/Cases/Fs/Ioctl.lean`) and the checker's two relating lemmas.  The
concrete pins on `ioctl_kinds_model` see one request per kind, so a
checker (with the spec moved in step) that answered a socket only
TIOCGWINSZ and declined TCGETS there would pass them; it fails here.  The
two character devices get the symbolic decline the same way. -/

/-- No fd-first terminal-only request on a regular file is declined, on any model,
and -ENOTTY is accepted there.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/ext4/ioctl.c:__ext4_ioctl@v6.18.46 -/
theorem file_tty_request_never_declines (fd req : word) (p : Fs.path) (off : word)
    (eff : SyscallEffect) (m : Model) (h : fd_lookup (m_fds m) fd = some (.FdFile p off))
    (hr : tty_only_request req = true) (hg : ioctl_fd_first_request req = true) :
    check_ioctl fd req eff m ≠ CheckUnmodeled
    ∧ check_ioctl fd req (mkEffect (errno_ret ENOTTY) [] []) m = CheckOk m [] := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hs := (file_tty_request_is_enotty fd req p off (ioctl_in fd req) m Unmodeled h hr hg).mp
      (check_ioctl_sound_unmodeled fd req eff m (ioctl_in fd req) hu)
    cases hs
  · exact check_ioctl_complete_ok fd req (mkEffect (errno_ret ENOTTY) [] []) m m [] (ioctl_in fd req)
      ((file_tty_request_is_enotty fd req p off (ioctl_in fd req) m
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m []) h hr hg).mpr rfl)

/-- The same on a write-only file, the kind the probe's own file is.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/ext4/ioctl.c:__ext4_ioctl@v6.18.46 -/
theorem filew_tty_request_never_declines (fd req : word) (p : Fs.path) (off : word)
    (eff : SyscallEffect) (m : Model) (h : fd_lookup (m_fds m) fd = some (.FdFileW p off))
    (hr : tty_only_request req = true) (hg : ioctl_fd_first_request req = true) :
    check_ioctl fd req eff m ≠ CheckUnmodeled
    ∧ check_ioctl fd req (mkEffect (errno_ret ENOTTY) [] []) m = CheckOk m [] := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hs := (filew_tty_request_is_enotty fd req p off (ioctl_in fd req) m Unmodeled h hr hg).mp
      (check_ioctl_sound_unmodeled fd req eff m (ioctl_in fd req) hu)
    cases hs
  · exact check_ioctl_complete_ok fd req (mkEffect (errno_ret ENOTTY) [] []) m m [] (ioctl_in fd req)
      ((filew_tty_request_is_enotty fd req p off (ioctl_in fd req) m
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m []) h hr hg).mpr rfl)

/-- The same on a directory.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/ext4/ioctl.c:__ext4_ioctl@v6.18.46 -/
theorem dir_tty_request_never_declines (fd req : word) (eff : SyscallEffect) (m : Model)
    (h : fd_lookup (m_fds m) fd = some .FdDir) (hr : tty_only_request req = true) (hg : ioctl_fd_first_request req = true) :
    check_ioctl fd req eff m ≠ CheckUnmodeled
    ∧ check_ioctl fd req (mkEffect (errno_ret ENOTTY) [] []) m = CheckOk m [] := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hs := (dir_tty_request_is_enotty fd req (ioctl_in fd req) m Unmodeled h hr hg).mp
      (check_ioctl_sound_unmodeled fd req eff m (ioctl_in fd req) hu)
    cases hs
  · exact check_ioctl_complete_ok fd req (mkEffect (errno_ret ENOTTY) [] []) m m [] (ioctl_in fd req)
      ((dir_tty_request_is_enotty fd req (ioctl_in fd req) m
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m []) h hr hg).mpr rfl)

/-- The same on a socket in any state: `sock_do_ioctl` answers -ENOTTY to
every request whose type is not the socket type, before it reads the state.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; net/socket.c:sock_do_ioctl@v6.18.46 -/
theorem socket_tty_request_never_declines (fd req : word) (sk : SockState) (eff : SyscallEffect)
    (m : Model) (h : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hr : tty_only_request req = true) (hg : ioctl_fd_first_request req = true) :
    check_ioctl fd req eff m ≠ CheckUnmodeled
    ∧ check_ioctl fd req (mkEffect (errno_ret ENOTTY) [] []) m = CheckOk m [] := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hs := (socket_tty_request_is_enotty fd req sk (ioctl_in fd req) m Unmodeled h hr hg).mp
      (check_ioctl_sound_unmodeled fd req eff m (ioctl_in fd req) hu)
    cases hs
  · exact check_ioctl_complete_ok fd req (mkEffect (errno_ret ENOTTY) [] []) m m [] (ioctl_in fd req)
      ((socket_tty_request_is_enotty fd req sk (ioctl_in fd req) m
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m []) h hr hg).mpr rfl)

/-- The same on either end of any pipe.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/pipe.c:pipe_ioctl@v6.18.46 -/
theorem pipe_tty_request_never_declines (fd req id : word) (w : Bool) (eff : SyscallEffect)
    (m : Model) (h : fd_lookup (m_fds m) fd = some (.FdPipe id w))
    (hr : tty_only_request req = true) (hg : ioctl_fd_first_request req = true) :
    check_ioctl fd req eff m ≠ CheckUnmodeled
    ∧ check_ioctl fd req (mkEffect (errno_ret ENOTTY) [] []) m = CheckOk m [] := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hs := (pipe_tty_request_is_enotty fd req id w (ioctl_in fd req) m Unmodeled h hr hg).mp
      (check_ioctl_sound_unmodeled fd req eff m (ioctl_in fd req) hu)
    cases hs
  · exact check_ioctl_complete_ok fd req (mkEffect (errno_ret ENOTTY) [] []) m m [] (ioctl_in fd req)
      ((pipe_tty_request_is_enotty fd req id w (ioctl_in fd req) m
        (Ok (mkEffect (errno_ret ENOTTY) [] []) m []) h hr hg).mpr rfl)

/-- `/dev/null` declines every request on every model, whatever is offered:
the spec's `devnull_any_request_is_unmodeled` through the checker's
completeness for declines.
kernel: fs/ioctl.c:ioctl,vfs_ioctl@v6.18.46 -/
theorem devnull_declines_symbolically (fd req : word) (rd wr : Bool) (eff : SyscallEffect)
    (m : Model) (h : fd_lookup (m_fds m) fd = some (.FdDevNull rd wr)) :
    check_ioctl fd req eff m = CheckUnmodeled :=
  check_ioctl_complete_unmodeled fd req m (ioctl_in fd req) eff
    ((devnull_any_request_is_unmodeled fd req rd wr (ioctl_in fd req) m Unmodeled h).mpr rfl)

/-- `/dev/urandom` likewise.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/char/random.c:random_ioctl@v6.18.46 -/
theorem urandom_declines_symbolically (fd req : word) (eff : SyscallEffect) (m : Model)
    (h : fd_lookup (m_fds m) fd = some .FdUrandom) :
    check_ioctl fd req eff m = CheckUnmodeled :=
  check_ioctl_complete_unmodeled fd req m (ioctl_in fd req) eff
    ((urandom_any_request_is_unmodeled fd req (ioctl_in fd req) m Unmodeled h).mpr rfl)

/-! ## The witness, the two other channels, the probe's lies, and the boundaries the fixtures miss -/

/-- The witness on each arm, without `ioctl_witness_ok` in the proof: the
spec's outcome on stdout, on a closed fd, on a request outside the eight
and on both character devices.  `ioctl_witness_ok` forces these already,
the spec being deterministic on every arm; these lines make the witness
die under this file alone.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem witness_answers_as_the_checker_accepts :
    ioctl_witness 1 TIOCGWINSZ demo_model = Ok (mkEffect (errno_ret ENOTTY) [] []) demo_model []
    ∧ ioctl_witness 3 TCGETS demo_model = Ok (mkEffect (errno_ret EBADF) [] []) demo_model []
    ∧ ioctl_witness 1 FIONREAD demo_model = Unmodeled
    ∧ ioctl_witness 9 TCGETS ioctl_kinds_model = Unmodeled
    ∧ ioctl_witness 11 TCGETS ioctl_kinds_model = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- stdin and stderr answer as stdout does: -ENOTTY accepted, 0 refused.
The channel pin above says so for every channel; these two are the
concrete twins the probes' stdin and stderr runs would replay.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem stdin_stderr_tcgets_enotty :
    check_ioctl_row (ioctl_in 0 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 0 TCGETS) (mkEffect 0 [] []) demo_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 2 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 2 TCGETS) (mkEffect 0 [] []) demo_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Keep the probe's old offered effects: TCGETS success is rejected,
while TCSETS, TIOCSPTLCK and FIONBIO decline. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

The lies `testing/syscall-check/tests/ioctl_spec.c` tells are told on a
WRITE-ONLY file (its `WR_CREATE` open), so their twins belong on fd 4: a
success on TCGETS and on TIOCSPTLCK (`--mutate` `ret=0`), -EFAULT on
TCSETS (a terminal's answer to an unreadable termios: `tty_mode_ioctl`'s
TCSETS arm (drivers/tty/tty_ioctl.c:802-803, Linux v6.18.46) hands it to
`set_termios` (:444-524), whose TERMIOS_OLD copy-in, the TCGETS2 branch
riscv takes, fails at :462-465; told here about a file that never reaches
it) are rejected for TCGETS and declined for TCSETS and TIOCSPTLCK, and a 0 on FIONBIO is declined; -EFAULT on a closed fd is
declined for TCSETS, though Linux `ioctl` answers -EBADF before it looks at the pointer
(fs/ioctl.c:588-589).
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl,set_termios; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem filew_probe_lies_refused_or_declined :
    check_ioctl_row (ioctl_in 4 TCGETS) (mkEffect 0 [] []) ioctl_kinds_model = CheckReject
    ∧ check_ioctl_row (ioctl_in 4 TIOCSPTLCK) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 TCSETS) (mkEffect (errno_ret EFAULT) [] []) ioctl_kinds_model
      = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 4 FIONBIO) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 3 TCSETS) (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- FIOQSIZE on a regular file and on a directory SUCCEEDS in the kernel,
writing the inode's byte count as an eight-byte `loff_t` (`do_vfs_ioctl`,
fs/ioctl.c:513-519, Linux v6.18.46; 4096 offered, the block a one-byte
tmpfs file occupies); the decline hides a success there, not an error as
on the pipe end above.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl@v6.18.46 -/
theorem fioqsize_success_declined_on_file_and_dir :
    check_ioctl_row (ioctl_in 3 FIOQSIZE) (mkEffect 0 [(4096, [0, 16, 0, 0, 0, 0, 0, 0])] [])
        ioctl_kinds_model
      = CheckUnmodeled
    ∧ check_ioctl_row (ioctl_in 5 FIOQSIZE) (mkEffect 0 [(4096, [0, 16, 0, 0, 0, 0, 0, 0])] [])
        ioctl_kinds_model
      = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The boundaries the truncation pins above step over: 2^32 itself folds
to fd 0, stdin, and is -ENOTTY there where -EBADF is refused; 2^31 + 1 is
NOT folded — `unsigned int` keeps bit 31 — and names no fd, so -EBADF is
accepted and -ENOTTY refused, which a checker masking to 31 bits would get
backwards; and the one negative request register a C caller really
produces, TIOCGPTN (0x80045430, bit 31 set) sign-extended by musl's
`int ioctl(int, int, ...)` to 0xFFFFFFFF80045430, is TIOCGPTN after
`cmd32`, -ENOTTY on stdout with 0 refused.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem truncation_boundaries :
    check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 32)) TCGETS) (mkEffect (errno_ret ENOTTY) [] [])
        demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 32)) TCGETS) (mkEffect (errno_ret EBADF) [] [])
        demo_model
      = CheckReject
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 31 + 1)) TCGETS) (mkEffect (errno_ret EBADF) [] [])
        demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in (Z_to_bv 64 (2 ^ 31 + 1)) TCGETS) (mkEffect (errno_ret ENOTTY) [] [])
        demo_model
      = CheckReject
    ∧ check_ioctl_row (ioctl_in 1 (Z_to_bv 64 (-(2 ^ 32) + 2147767344)))
        (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_ioctl_row (ioctl_in 1 (Z_to_bv 64 (-(2 ^ 32) + 2147767344))) (mkEffect 0 [] [])
        demo_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- lean-port sentinel: ticket V-Fs-Ioctl appends below this line
/-- QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_unknown_any_effect_unmodeled (eff : SyscallEffect) :
    check_ioctl 7 0xdeadbeef eff demo_model = CheckUnmodeled := rfl

/-- Offer the named EBADF answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_unknown_ebadf_unmodeled :
    check_ioctl 7 0xdeadbeef (mkEffect (errno_ret EBADF) [] []) demo_model = CheckUnmodeled := rfl

/-- Offer the named ENOTTY answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_unknown_enotty_unmodeled :
    check_ioctl 7 0xdeadbeef (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckUnmodeled := rfl

/-- The old EBADF acceptance is no longer sound across supported implementations.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_unknown_ebadf_not_ok (m' : Model) (evs : List event) :
    check_ioctl 7 0xdeadbeef (mkEffect (errno_ret EBADF) [] []) demo_model ≠ CheckOk m' evs := by
  intro h
  cases h

/-- QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tcsets_any_effect_unmodeled (eff : SyscallEffect) :
    check_ioctl 7 TCSETS eff demo_model = CheckUnmodeled := rfl

/-- Offer the named EBADF answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tcsets_ebadf_unmodeled :
    check_ioctl 7 TCSETS (mkEffect (errno_ret EBADF) [] []) demo_model = CheckUnmodeled := rfl

/-- Offer the named EFAULT answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tcsets_efault_unmodeled :
    check_ioctl 7 TCSETS (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := rfl

/-- The old EBADF acceptance is no longer sound across supported implementations.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tcsets_ebadf_not_ok (m' : Model) (evs : List event) :
    check_ioctl 7 TCSETS (mkEffect (errno_ret EBADF) [] []) demo_model ≠ CheckOk m' evs := by
  intro h
  cases h

/-- QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tcsets_any_effect_unmodeled (eff : SyscallEffect) :
    check_ioctl 1 TCSETS eff demo_model = CheckUnmodeled := rfl

/-- Offer the named ENOTTY answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tcsets_enotty_unmodeled :
    check_ioctl 1 TCSETS (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckUnmodeled := rfl

/-- Offer the named EFAULT answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tcsets_efault_unmodeled :
    check_ioctl 1 TCSETS (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := rfl

/-- QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocswinsz_any_effect_unmodeled (eff : SyscallEffect) :
    check_ioctl 7 TIOCSWINSZ eff demo_model = CheckUnmodeled := rfl

/-- Offer the named EBADF answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocswinsz_ebadf_unmodeled :
    check_ioctl 7 TIOCSWINSZ (mkEffect (errno_ret EBADF) [] []) demo_model = CheckUnmodeled := rfl

/-- Offer the named EFAULT answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocswinsz_efault_unmodeled :
    check_ioctl 7 TIOCSWINSZ (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := rfl

/-- The old EBADF acceptance is no longer sound across supported implementations.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocswinsz_ebadf_not_ok (m' : Model) (evs : List event) :
    check_ioctl 7 TIOCSWINSZ (mkEffect (errno_ret EBADF) [] []) demo_model ≠ CheckOk m' evs := by
  intro h
  cases h

/-- QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocswinsz_any_effect_unmodeled (eff : SyscallEffect) :
    check_ioctl 1 TIOCSWINSZ eff demo_model = CheckUnmodeled := rfl

/-- Offer the named ENOTTY answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocswinsz_enotty_unmodeled :
    check_ioctl 1 TIOCSWINSZ (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckUnmodeled := rfl

/-- Offer the named EFAULT answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocswinsz_efault_unmodeled :
    check_ioctl 1 TIOCSWINSZ (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := rfl

/-- QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocsptlck_any_effect_unmodeled (eff : SyscallEffect) :
    check_ioctl 7 TIOCSPTLCK eff demo_model = CheckUnmodeled := rfl

/-- Offer the named EBADF answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocsptlck_ebadf_unmodeled :
    check_ioctl 7 TIOCSPTLCK (mkEffect (errno_ret EBADF) [] []) demo_model = CheckUnmodeled := rfl

/-- Offer the named EFAULT answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocsptlck_efault_unmodeled :
    check_ioctl 7 TIOCSPTLCK (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := rfl

/-- The old EBADF acceptance is no longer sound across supported implementations.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocsptlck_ebadf_not_ok (m' : Model) (evs : List event) :
    check_ioctl 7 TIOCSPTLCK (mkEffect (errno_ret EBADF) [] []) demo_model ≠ CheckOk m' evs := by
  intro h
  cases h

/-- QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocsptlck_any_effect_unmodeled (eff : SyscallEffect) :
    check_ioctl 1 TIOCSPTLCK eff demo_model = CheckUnmodeled := rfl

/-- Offer the named ENOTTY answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocsptlck_enotty_unmodeled :
    check_ioctl 1 TIOCSPTLCK (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckUnmodeled := rfl

/-- Offer the named EFAULT answer from the implementation disagreement.
QEMU v11.1.1 linux-user/syscall.c do_ioctl checks the request and
locks IOC_W input before safe_ioctl; see the source argument on
Sys.Fs.Ioctl.ioctl_fd_first_request. Linux fs/ioctl.c ioctl resolves the fd first.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem open_fd_tiocsptlck_efault_unmodeled :
    check_ioctl 1 TIOCSPTLCK (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := rfl

/-- The gate retains the fd-first TIOCGWINSZ case, including wrong-errno rejection.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem closed_fd_tiocgwinsz_ebadf_accepted :
    check_ioctl 7 TIOCGWINSZ (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_ioctl 7 TIOCGWINSZ (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_ioctl 7 TIOCGWINSZ (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

section V_Fs_Ioctl

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## V-Fs-Ioctl — ioctl over the real table

WHAT IS STATED HERE.  The checker-level twins, the probe's recorded
closed-fd calls, and the register shapes that distinguish this arm's
argument reading, all through `check_syscall` over `checked_table`.

WHAT A PIN HERE ADDS is the registration in `Checks/Arms/Fs/Ioctl.lean`:
the lookup reaches `arm_ioctl`, which narrows a0 and a1 independently
and reads no later register.  The twins alone cannot catch a wrong arm.

POLARITY: `kernel:` names the source of each accepted, refused or
declined answer; `model:` marks the lookup over the table's own contents. -/

/-- The dispatcher lookup for any `ioctl_in` reaches the registered arm.
model: `lookup_ca` over `checked_table` at syscall 29. -/
theorem lookup_ioctl_in (fd req : word) :
    lookup_ca checked_table (bv_unsigned (ioctl_in fd req).in_sysno) = some arm_ioctl :=
  lookup_ca_checked_table_ioctl

/-- Through the dispatcher: the checker-level twin `stdout_tiocgwinsz_enotty_accepted`.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem stdout_tiocgwinsz_enotty_accepted_over_the_real_table :
    check_syscall (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 TIOCGWINSZ) (mkEffect 0 [] []) demo_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- Through the dispatcher: the checker-level twin `stdout_all_eight_enotty_accepted_or_declined`.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; fs/pipe.c:pipe_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl; drivers/tty/tty_jobctrl.c:tty_jobctrl_ioctl; drivers/tty/tty_io.c:tty_ioctl; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem stdout_all_eight_enotty_accepted_or_declined_over_the_real_table :
    check_syscall (ioctl_in 1 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 TCSETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_syscall (ioctl_in 1 TIOCSCTTY) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 TIOCGWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 TIOCSWINSZ) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_syscall (ioctl_in 1 TIOCNOTTY) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 TIOCGPTN) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 TIOCSPTLCK) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Through the dispatcher: the checker-level twin `stdout_fionread_fionbio_declined`.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; fs/pipe.c:pipe_ioctl@v6.18.46 -/
theorem stdout_fionread_fionbio_declined_over_the_real_table :
    check_syscall (ioctl_in 1 FIONREAD) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (ioctl_in 1 FIONBIO) (mkEffect 0 [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (ioctl_in 1 FIONREAD) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_syscall (ioctl_in 1 FIONBIO) (mkEffect (errno_ret ENOTTY) [] []) demo_model
        = CheckUnmodeled
    ∧ check_syscall (ioctl_in 1 FIONREAD) (mkEffect 0 [(4096, [0, 0, 0, 0])] []) demo_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Through the dispatcher: the checker-level twin `fd_truncates_to_32_bits`.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (ioctl_in (Z_to_bv 64 (2 ^ 32 + 1)) TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = check_syscall (ioctl_in 1 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
    ∧ check_syscall (ioctl_in (Z_to_bv 64 (2 ^ 32 + 1)) TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (ioctl_in (Z_to_bv 64 (2 ^ 32 + 1)) TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject
    ∧ check_syscall (ioctl_in (Z_to_bv 64 (2 ^ 32 + 3)) TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (ioctl_in (Z_to_bv 64 (-1)) TCGETS) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (ioctl_in (Z_to_bv 64 (-1)) TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Through the dispatcher: the checker-level twin `cmd_truncates_to_32_bits`.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem cmd_truncates_to_32_bits_over_the_real_table :
    check_syscall (ioctl_in 1 (Z_to_bv 64 (2 ^ 32 + 21505))) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 (Z_to_bv 64 (-(2 ^ 32) + 21505))) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (ioctl_in 1 (Z_to_bv 64 (2 ^ 32 + 21505))) (mkEffect 0 [] []) demo_model
      = CheckReject
    ∧ check_syscall (ioctl_in 1 (Z_to_bv 64 (2 ^ 32 + 21531))) (mkEffect 0 [] []) demo_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A recorded ioctl call: fd, request and arg in a0, a1 and a2, modulo
2^64, later registers zero and no mapped memory. -/
def ioctl_call (fd req arg : Int) : SyscallInput :=
  SyscallInput.mkInput 29 [Z_to_bv 64 fd, Z_to_bv 64 req, Z_to_bv 64 arg, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- The recorded Linux EBADF and QEMU's ENOTTY for an unknown request
on a closed fd are both declined through the real table. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

Trace 010 in Linux: the unknown request on closed fd 999 returns -EBADF.  `fd_empty` wins before cmd or arg is read.
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem closed_unknown_over_the_real_table :
    check_syscall (ioctl_call 999 0xdeadbeef 0) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (ioctl_call 999 0xdeadbeef 0) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- Closed-fd TCSETS with a null argument: decline both Linux's EBADF
and QEMU's EFAULT through the real table. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.

Trace 014 in Linux: TCSETS with a null arg on closed fd 999 returns
-EBADF.  `fd_empty` wins before any
terminal handler could copy the termios through arg.
kernel: fs/ioctl.c:ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl,set_termios@v6.18.46 -/
theorem closed_tcsets_null_over_the_real_table :
    check_syscall (ioctl_call 999 21506 0) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (ioctl_call 999 21506 0) (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- Through the dispatcher: the checker-level twin `filew_probe_lies_refused_or_declined`.
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl,set_termios; drivers/tty/pty.c:pty_unix98_ioctl@v6.18.46 -/
theorem filew_probe_lies_refused_or_declined_over_the_real_table :
    check_syscall (ioctl_in 4 TCGETS) (mkEffect 0 [] []) ioctl_kinds_model = CheckReject
    ∧ check_syscall (ioctl_in 4 TIOCSPTLCK) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_syscall (ioctl_in 4 TCSETS) (mkEffect (errno_ret EFAULT) [] []) ioctl_kinds_model
      = CheckUnmodeled
    ∧ check_syscall (ioctl_in 4 FIONBIO) (mkEffect 0 [] []) ioctl_kinds_model = CheckUnmodeled
    ∧ check_syscall (ioctl_in 3 TCSETS) (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The first conjunct catches swapped argument registers: stdout TCGETS
accepts ENOTTY, whereas the swapped call has unknown request 1 and declines
for either offered errno. The request gate declines before fd lookup because QEMU v11.1.1
linux-user/syscall.c do_ioctl can answer before safe_ioctl; the full source
argument is on Sys.Fs.Ioctl.ioctl_fd_first_request.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem fd_is_a0_cmd_is_a1_over_the_real_table :
    check_syscall (ioctl_in 1 TCGETS) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (ioctl_in TCGETS 1) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (ioctl_in TCGETS 1) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- The zero-tail conjunct kills an arm taking cmd from a2..a5;
the nonzero-tail conjunct kills an arm requiring those registers to be
zero or using any of them as fd or cmd.  On this answering path nothing
reads through arg, so both calls have the same return-only answer.
kernel: fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem registers_after_a1_unread_over_the_real_table :
    check_syscall (SyscallInput.mkInput 29 [1, TCGETS, 0, 0, 0, 0]
      (fun _ => none) (fun _ => none)) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (SyscallInput.mkInput 29 [1, TCGETS, 999, 998, 997, 996]
      (fun _ => none) (fun _ => none)) (mkEffect (errno_ret ENOTTY) [] []) demo_model
      = CheckOk demo_model [] :=
  ⟨rfl, rfl⟩

/-- `testing/syscall-check/traces/ioctl_spec/001.jsonl`, seq 1..4, with
fd 3 open: `ioctl_kinds_model` has a read-only file there, while the
probe has a write-only file.  Every open file kind answers these requests
-ENOTTY, as pinned by `enotty_on_every_open_kind_or_declined`.
An arm handing a0 on whole sees no fd at 2^32+3 or 0xFFFFFFFF00000003
and would accept -EBADF; an arm handing a1 on whole sees 2^32+0x5413,
not a terminal-only request, and would decline.
The request values are TCGETS 0x5401 = 21505, TIOCGWINSZ 0x5413 = 21523,
and FIONREAD 0x541B = 21531 (include/uapi/asm-generic/ioctls.h:20,38,46,
Linux v6.18.46).
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/ioctl.c:ioctl,vfs_ioctl; drivers/tty/tty_ioctl.c:tty_mode_ioctl@v6.18.46 -/
theorem trace_001_open_fd_over_the_real_table :
    check_syscall (ioctl_call 3 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model = CheckOk ioctl_kinds_model []
    ∧ check_syscall (ioctl_call 3 21523 0)
      (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject
    ∧ check_syscall (ioctl_call 4294967299 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model = CheckOk ioctl_kinds_model []
    ∧ check_syscall (ioctl_call 4294967299 21523 0)
      (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject
    ∧ check_syscall (ioctl_call 18446744069414584323 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model = CheckOk ioctl_kinds_model []
    ∧ check_syscall (ioctl_call 18446744069414584323 21523 0)
      (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject
    ∧ check_syscall (ioctl_call 3 4294988819 0)
      (mkEffect (errno_ret ENOTTY) [] []) ioctl_kinds_model = CheckOk ioctl_kinds_model []
    ∧ check_syscall (ioctl_call 3 4294988819 0)
      (mkEffect (errno_ret EBADF) [] []) ioctl_kinds_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `testing/syscall-check/traces/ioctl_spec/001.jsonl`, seq 6..12, and `009.jsonl`, seq 0, on
`demo_model` where fd 3 is closed, as after the probe's close at seq 5.
`fd_empty` answers before cmd is read (fs/ioctl.c:588-589, Linux v6.18.46),
but FIONREAD on 999 (009, seq 0) now declines at the fd-first gate, even
with that real Linux answer offered.
2^31+1 is not folded to stdout, which a 31-bit mask would do: stdout is
open on `demo_model`, so that arm would accept -ENOTTY and refuse -EBADF.
The request values are TCGETS 0x5401 = 21505, TIOCGWINSZ 0x5413 = 21523,
and FIONREAD 0x541B = 21531 (include/uapi/asm-generic/ioctls.h:20,38,46,
Linux v6.18.46).
kernel: fs/ioctl.c:ioctl,do_vfs_ioctl@v6.18.46 -/
theorem trace_001_closed_fd_over_the_real_table :
    check_syscall (ioctl_call 3 21523 0)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (ioctl_call 3 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_syscall (ioctl_call 4294967299 21523 0)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (ioctl_call 4294967299 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_syscall (ioctl_call 999 21523 0)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (ioctl_call 999 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_syscall (ioctl_call 999 21505 0)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (ioctl_call 999 21505 0)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_syscall (ioctl_call 18446744073709551615 21523 0)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (ioctl_call 18446744073709551615 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_syscall (ioctl_call 4294968295 21523 0)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (ioctl_call 4294968295 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_syscall (ioctl_call 2147483649 21523 0)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (ioctl_call 2147483649 21523 0)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckReject
    ∧ check_syscall (ioctl_call 999 21531 73728)
      (mkEffect (errno_ret EBADF) [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (ioctl_call 999 21531 73728)
      (mkEffect (errno_ret ENOTTY) [] []) demo_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end V_Fs_Ioctl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Ioctl
