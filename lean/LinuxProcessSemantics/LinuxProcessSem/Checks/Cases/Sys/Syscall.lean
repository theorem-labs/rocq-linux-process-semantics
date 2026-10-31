import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Sys.Syscall — the calling convention, read off against Linux

Pins over `Sys.Syscall`'s helpers.  No Rocq file sits at this file's
mirror path: the Rocq tree has no case file for `Sys/Syscall.v`, and
exercises its helpers through the arms that call them —
`fcntl_fd32_on_a_live_fd` in `Checks/Cases/Fs/Fcntl.v` is one of the
cases that separate `fd32` from the identity — and through the
`record_copyins` inversion lemmas of `Checks/Sys/Prelude.v`, whose twins
sit in `CopyinPins` below.  These are the Lean tree's
tests for
what `Sys/Syscall.lean` ports, placed where every pin in this tree lives
(`Checks/Cases/<mirror path>`) so that `tools/check_lean_pins.py` reads
them and the trusted file holds only definitions and their Rocq-twin
lemmas.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ,
and every claim in it is a claim about what the kernel does, with the
citation beside it — as the `kernel:` line each narrowing and errno pin
carries; the ledger pins and the model-vs-model identities
(`sint32_eq_nfds_signed_nfds32`, the `errno_from` closed forms), which
state the model's own bookkeeping, carry a `model:` line instead
(`tools/check_lean_pin_evidence.py`).

Each definition under test encodes one fact about how the kernel reads a
register or accounts a read.  Each pin states that fact on a concrete
value and refutes the concrete mistake the definition exists to avoid, so
a port that quietly re-widened a narrowing, re-read a count with the
wrong sign, or dropped a ledger entry fails here rather than in a probe.
The narrowing pins are stated against what `SYSCALL_DEFINE`'s `int` /
`unsigned int` casts do to the register; the ledger and errno pins are
stated on the monad, against what a ported arm would observe.  A negative
pin that is the corollary of the positive one above it is DERIVED from
it, by rewriting with the equality and deciding the rest, so the two
cannot drift apart. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Syscall

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

section NarrowingPins

/-- `write(2^32 + 1, buf, n)` really writes to STDOUT: `fd32` is the
`unsigned int fd` cast of `SYSCALL_DEFINE3(write, unsigned int, fd, ...)`
(fs/read_write.c:746, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/read_write.c:write@v6.18.46 -/
theorem fd32_high_half_is_stdout : fd32 (Z_to_bv 64 (2 ^ 32 + 1)) = Z_to_bv 64 1 := by decide

/-- `close(2^32)` really closes stdin (`SYSCALL_DEFINE1(close, unsigned
int, fd)`, fs/open.c).
kernel: fs/open.c:close@v6.18.46 -/
theorem fd32_two_pow_32_is_stdin : fd32 (Z_to_bv 64 (2 ^ 32)) = Z_to_bv 64 0 := by decide

/-- A register with only bit 63 set is fd 0 to the kernel.
kernel: fs/read_write.c:write@v6.18.46 -/
theorem fd32_bit63_is_stdin : fd32 (Z_to_bv 64 (2 ^ 63)) = Z_to_bv 64 0 := by decide

/-- A low half of all ones stays `2^32 - 1`: the model zero-extends, and
that value matches no fd the table can hold, so a call that resolves its
fd through the table — `ksys_write`'s `CLASS(fd_pos, f)(fd)` with
`ret = -EBADF` for an empty lookup (fs/read_write.c:727-744, Linux
v6.18.46, commit 1f99e9ab748f) — answers -EBADF exactly as Linux does for
`fd = -1`.  A DIRFD argument is different and this pin says nothing about
it: `path_init` (fs/namei.c:2582-2607, v6.18.46) takes the root for an
absolute name before it ever reads `nd->dfd`, so `openat(-1,
"/etc/passwd", …)` succeeds on Linux; that is the arm's business, not the
narrowing's.
kernel: fs/read_write.c:ksys_write; fs/namei.c:path_init@v6.18.46 -/
theorem fd32_all_ones_low_half_is_kept :
    fd32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) := by decide

/-- The mistake `fd32`'s Rocq argument rules out: sign-extending the
`int` fd back to 64 bits, which would carry `-1` through as the all-ones
register.
kernel: fs/read_write.c:write@v6.18.46 -/
theorem fd32_does_not_sign_extend :
    fd32 (Z_to_bv 64 (2 ^ 32 - 1)) ≠ Z_to_bv 64 (-1) := by
  rw [fd32_all_ones_low_half_is_kept]
  decide

/-- The other mistake: a full-register compare, which reports -EBADF for
`2^32`, an fd Linux closes as stdin.
kernel: fs/open.c:close@v6.18.46 -/
theorem fd32_is_not_the_full_register :
    fd32 (Z_to_bv 64 (2 ^ 32)) ≠ Z_to_bv 64 (2 ^ 32) := by
  rw [fd32_two_pow_32_is_stdin]
  decide

/-! The other `abi_low32` readers.  Each is the same `unsigned int` /
`int` cast on another register, so each is pinned the way `fd32` is: with
garbage in the high half of the register the kernel reads the low half,
and NOT the full register — the mistake a port makes by dropping the
cast.  Where the kernel names the low half (`SEEK_END`, `F_GETFD`, …)
the pin reads as the call it stands for; `uid32` and `pid32` use a plain
id.  Each pin is the cast alone — what an arm does with the value is the
arm's own pin — and the probe that drives the shape against the pinned
kernel is named beside it where one exists in
`testing/syscall-check/tests/`; shutdown's `how`, pipe2's `flags` and a
`write` count of 2^32 have none at this head.

The sign half differs between the two C types.  For the three `unsigned
int` readers (`whence32`, `cmd32`, `uid32`) a low half of all ones is
4294967295 to the kernel and sign-extending it to -1 is a false claim
about Linux, so each gets a `*_does_not_sign_extend` negative.  For an
`int` reader the low half of all ones IS -1 to the kernel, and how the
model spells that -1 — zero-extended, `2^32 - 1` — is an encoding the
arms are written against: `Sys/Kernel/Exit.lean`'s `wait4_spec` tests the
`pid32`-narrowed a0 against `WAIT_ANY32 = 2^32 - 1`, so `pid32` gets the
negative too.  The other six `int` readers reach, at this head, only
equality and mask tests against small non-negative constants, on which
the two encodings agree; the first arm to read one of their signs owes
the negative. -/

/-- `lseek(fd, 0, 2^32 + SEEK_END)` is a seek from the end: `whence` is
`unsigned int` (`SYSCALL_DEFINE3(lseek, unsigned int, fd, off_t, offset,
unsigned int, whence)`, fs/read_write.c:410, Linux v6.18.46, commit
1f99e9ab748f), and `SEEK_END` is 2 (include/uapi/linux/fs.h:54).
Probed: `testing/syscall-check/tests/lseek_probe.c`, whose default
`conform` case seeks with `2^32 | SEEK_END`.
kernel: fs/read_write.c:lseek; include/uapi/linux/fs.h:SEEK_END@v6.18.46 -/
theorem whence32_is_the_unsigned_int_cast :
    whence32 (Z_to_bv 64 (2 ^ 32 + 2)) = Z_to_bv 64 2 ∧
    whence32 (Z_to_bv 64 (2 ^ 32 + 2)) ≠ Z_to_bv 64 (2 ^ 32 + 2) :=
  have h : whence32 (Z_to_bv 64 (2 ^ 32 + 2)) = Z_to_bv 64 2 := by decide
  ⟨h, by rw [h]; decide⟩

/-- The other mistake, sign-extending the low half: `lseek(fd, 0,
0xFFFFFFFF)` on a live fd is whence 4294967295, past `SEEK_MAX`
(`SEEK_HOLE`, 4: include/uapi/linux/fs.h:56-57) and so `-EINVAL`
(`ksys_lseek`, fs/read_write.c:400-401, Linux v6.18.46; an empty fd is
`-EBADF` first, :397-398), not whence `-1`.  Linux answers `-EINVAL` to
either spelling of that low half, so what this negative fixes is the
model's zero-extended encoding of an `unsigned int`, the one the arms'
constants are written against.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem whence32_does_not_sign_extend :
    whence32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) ∧
    whence32 (Z_to_bv 64 (2 ^ 32 - 1)) ≠ Z_to_bv 64 (-1) :=
  have h : whence32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) := by decide
  ⟨h, by rw [h]; decide⟩

/-- `fcntl(fd, 2^32 + F_GETFD)` is `F_GETFD`: `cmd` is `unsigned int`
(`SYSCALL_DEFINE3(fcntl, unsigned int, fd, unsigned int, cmd, ...)`,
fs/fcntl.c:574, Linux v6.18.46), and `F_GETFD` is 1
(include/uapi/asm-generic/fcntl.h:99).  Probed:
`testing/syscall-check/tests/fcntl_spec.c`, whose `trunc` case passes
fd and cmd with high halves on a live fd and whose `reject --mutate
fcntl:ret=-EBADF` refuses a kernel that compared the whole register.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem cmd32_is_the_unsigned_int_cast :
    cmd32 (Z_to_bv 64 (2 ^ 32 + 1)) = Z_to_bv 64 1 ∧
    cmd32 (Z_to_bv 64 (2 ^ 32 + 1)) ≠ Z_to_bv 64 (2 ^ 32 + 1) :=
  have h : cmd32 (Z_to_bv 64 (2 ^ 32 + 1)) = Z_to_bv 64 1 := by decide
  ⟨h, by rw [h]; decide⟩

/-- Not sign-extended either: `fcntl(fd, 0xFFFFFFFF)` on a live ordinary
fd is cmd 4294967295, which falls to `do_fcntl`'s `default:` and returns
the `-EINVAL` the function starts with (fs/fcntl.c:450, :553-556, Linux
v6.18.46), not cmd `-1`.  `SYSCALL_DEFINE3(fcntl)` turns two shapes away
before that with `-EBADF`: an empty fd (fs/fcntl.c:579-580, Linux
v6.18.46) and an fd opened `O_PATH` whose cmd `check_fcntl_cmd`
(fs/fcntl.c:559-572, Linux v6.18.46) refuses, the test at
fs/fcntl.c:582-585 — `Sys/Fs/Fcntl.lean` carries the argument for why
the second never meets a modeled fd; and the LSM hook called at
fs/fcntl.c:587-589 (Linux v6.18.46) may answer its own errno before the
command is dispatched, a policy outside this model.  As for `whence32`, Linux gives the same
`-EINVAL` to either spelling of the low half; the negative fixes the
model's encoding.
kernel: fs/fcntl.c:fcntl,do_fcntl,check_fcntl_cmd@v6.18.46 -/
theorem cmd32_does_not_sign_extend :
    cmd32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) ∧
    cmd32 (Z_to_bv 64 (2 ^ 32 - 1)) ≠ Z_to_bv 64 (-1) :=
  have h : cmd32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) := by decide
  ⟨h, by rw [h]; decide⟩

/-- `clock_gettime(2^32 + CLOCK_MONOTONIC, ts)` reads the monotonic
clock: `clockid_t` is `__kernel_clockid_t`, an `int`
(include/linux/types.h:32, include/uapi/asm-generic/posix_types.h:96),
reaching `SYSCALL_DEFINE2(clock_gettime, const clockid_t, which_clock, ...)`
(kernel/time/posix-timers.c:1136, Linux v6.18.46), and `CLOCK_MONOTONIC`
is 1 (include/uapi/linux/time.h:50).  Probed:
`testing/syscall-check/tests/clock_gettime_spec.c`, whose `wide` case
passes `2^32 + 1`.
kernel: kernel/time/posix-timers.c:clock_gettime; include/uapi/linux/time.h:CLOCK_MONOTONIC@v6.18.46 -/
theorem clockid32_is_the_int_cast :
    clockid32 (Z_to_bv 64 (2 ^ 32 + 1)) = Z_to_bv 64 1 ∧
    clockid32 (Z_to_bv 64 (2 ^ 32 + 1)) ≠ Z_to_bv 64 (2 ^ 32 + 1) :=
  have h : clockid32 (Z_to_bv 64 (2 ^ 32 + 1)) = Z_to_bv 64 1 := by decide
  ⟨h, by rw [h]; decide⟩

/-- `shutdown(fd, 2^32 + SHUT_RDWR)` shuts both directions: `how` is
`int` (`SYSCALL_DEFINE2(shutdown, int, fd, int, how)`, net/socket.c:2490,
Linux v6.18.46), and `SHUT_RDWR` is the third enumerator, 2
(include/linux/net.h:92-96).  No probe drives shutdown's `how` with a
high half at this head.
kernel: net/socket.c:shutdown@v6.18.46 -/
theorem int32_is_the_int_cast :
    int32 (Z_to_bv 64 (2 ^ 32 + 2)) = Z_to_bv 64 2 ∧
    int32 (Z_to_bv 64 (2 ^ 32 + 2)) ≠ Z_to_bv 64 (2 ^ 32 + 2) :=
  have h : int32 (Z_to_bv 64 (2 ^ 32 + 2)) = Z_to_bv 64 2 := by decide
  ⟨h, by rw [h]; decide⟩

/-- `setuid(2^32 + 1000)` sets uid 1000: `uid_t` is `__kernel_uid32_t`,
an `unsigned int` (include/linux/types.h:37,
include/uapi/asm-generic/posix_types.h:49), reaching
`SYSCALL_DEFINE1(setuid, uid_t, uid)` (kernel/sys.c:698, Linux v6.18.46).
Probed: `testing/syscall-check/tests/creds_trunc.c`, whose `reject
--mutate setuid#1:ret=-EINVAL` refuses a kernel that read the high
half.
kernel: kernel/sys.c:setuid@v6.18.46 -/
theorem uid32_is_the_unsigned_int_cast :
    uid32 (Z_to_bv 64 (2 ^ 32 + 1000)) = Z_to_bv 64 1000 ∧
    uid32 (Z_to_bv 64 (2 ^ 32 + 1000)) ≠ Z_to_bv 64 (2 ^ 32 + 1000) :=
  have h : uid32 (Z_to_bv 64 (2 ^ 32 + 1000)) = Z_to_bv 64 1000 := by decide
  ⟨h, by rw [h]; decide⟩

/-- Not sign-extended either: `setuid(0xFFFFFFFF)` is uid 4294967295,
the `uid_t` `-1` that `make_kuid` maps to `INVALID_UID` and
`__sys_setuid` refuses with `-EINVAL` (kernel/sys.c:659-661, Linux
v6.18.46).  That holds with and without `CONFIG_USER_NS`: with it,
`make_kuid` (kernel/user_namespace.c:422-426, Linux v6.18.46) reaches
`map_id_range_down_base` (kernel/user_namespace.c:299-316, Linux
v6.18.46) through `map_id_down` (kernel/user_namespace.c:338-341, Linux
v6.18.46) and `map_id_range_down` (kernel/user_namespace.c:318-336,
Linux v6.18.46), over `init_user_ns`'s
one extent `{0, 0, 4294967295U}` (kernel/user.c:38-46, Linux v6.18.46),
whose last id is 4294967294, so 4294967295 matches no extent and
`map_id_range_down` answers `(u32) -1` (kernel/user_namespace.c:333);
without it, `make_kuid` is `KUIDT_INIT(uid)` (include/linux/uidgid.h:139-142,
Linux v6.18.46).  Both then fail `uid_valid`, which tests
`__kuid_val(uid) != (uid_t) -1` (include/linux/uidgid.h:103-106, Linux
v6.18.46) — the value `INVALID_UID = KUIDT_INIT(-1)` spells
(include/linux/uidgid.h:50).
The model reads the 32-bit value, not a 64-bit `-1`, and an
arm can tell: `Uapi.ID_MINUS_ONE` is 4294967295.  Probed:
`testing/syscall-check/tests/creds_trunc.c`, whose `reject --mutate
setuid#2:ret=0` refuses a kernel that accepted the all-ones id.
kernel: kernel/sys.c:__sys_setuid; kernel/user_namespace.c:make_kuid,map_id_down,map_id_range_down,map_id_range_down_base; include/linux/uidgid.h:make_kuid,uid_valid@v6.18.46 -/
theorem uid32_does_not_sign_extend :
    uid32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) ∧
    uid32 (Z_to_bv 64 (2 ^ 32 - 1)) ≠ Z_to_bv 64 (-1) :=
  have h : uid32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) := by decide
  ⟨h, by rw [h]; decide⟩

/-- `dup3(old, new, 2^32 + O_CLOEXEC)` asks for close-on-exec: `flags`
is `int` (`SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int,
newfd, int, flags)`, fs/file.c:1433, Linux v6.18.46), and `O_CLOEXEC` is
02000000 (include/uapi/asm-generic/fcntl.h:62).  Probed:
`testing/syscall-check/tests/dup_spec.c`, whose `d3-flags-hi` case calls
`dup3(2, 1, 2^32)` and whose `reject --mutate dup3:ret=-EINVAL` refuses
a kernel that tested the flags on 64 bits.
kernel: fs/file.c:dup3; include/uapi/asm-generic/fcntl.h:O_CLOEXEC@v6.18.46 -/
theorem flag32_is_the_int_cast :
    flag32 (Z_to_bv 64 (2 ^ 32 + 524288)) = Z_to_bv 64 524288 ∧
    flag32 (Z_to_bv 64 (2 ^ 32 + 524288)) ≠ Z_to_bv 64 (2 ^ 32 + 524288) :=
  have h : flag32 (Z_to_bv 64 (2 ^ 32 + 524288)) = Z_to_bv 64 524288 := by decide
  ⟨h, by rw [h]; decide⟩

/-- `rt_sigprocmask(2^32 + SIG_SETMASK, set, old, 8)` replaces the mask:
`how` is `int` (`SYSCALL_DEFINE4(rt_sigprocmask, int, how, ...)`,
kernel/signal.c:3327, Linux v6.18.46), and `SIG_SETMASK` is 2
(include/uapi/asm-generic/signal-defs.h:78).  Probed:
`testing/syscall-check/tests/rt_sigprocmask_spec.c`, whose `set ok
0x100000001 …` cases pass `(1 << 32) | SIG_UNBLOCK` and refuse `-EINVAL`
for it.
kernel: kernel/signal.c:rt_sigprocmask; include/uapi/asm-generic/signal-defs.h:SIG_SETMASK@v6.18.46 -/
theorem how32_is_the_int_cast :
    how32 (Z_to_bv 64 (2 ^ 32 + 2)) = Z_to_bv 64 2 ∧
    how32 (Z_to_bv 64 (2 ^ 32 + 2)) ≠ Z_to_bv 64 (2 ^ 32 + 2) :=
  have h : how32 (Z_to_bv 64 (2 ^ 32 + 2)) = Z_to_bv 64 2 := by decide
  ⟨h, by rw [h]; decide⟩

/-- `wait4(2^32 + 7, status, 0, ru)` waits for pid 7: `pid_t` is
`__kernel_pid_t`, an `int` (include/linux/types.h:27,
include/uapi/asm-generic/posix_types.h:28), reaching
`SYSCALL_DEFINE4(wait4, pid_t, upid, ...)` (kernel/exit.c:1907, Linux
v6.18.46).  Probed: `testing/syscall-check/tests/wait4_spec.c`, whose
`trunc` case calls `wait4(2^33 - 1, &status, 2^32 + 1, NULL)`.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem pid32_is_the_int_cast :
    pid32 (Z_to_bv 64 (2 ^ 32 + 7)) = Z_to_bv 64 7 ∧
    pid32 (Z_to_bv 64 (2 ^ 32 + 7)) ≠ Z_to_bv 64 (2 ^ 32 + 7) :=
  have h : pid32 (Z_to_bv 64 (2 ^ 32 + 7)) = Z_to_bv 64 7 := by decide
  ⟨h, by rw [h]; decide⟩

/-- `pid32`'s sign half, the one `int` reader whose encoding an arm reads:
`wait4(-1, …)` waits for any child (`kernel_wait4`'s `if (upid == -1)`,
kernel/exit.c:1864-1865, Linux v6.18.46), and `Sys/Kernel/Exit.lean`'s
`wait4_spec` recognises that call by testing the `pid32`-narrowed
register against `WAIT_ANY32 = 2^32 - 1`.  A port that sign-extended the
low half, or masked it to 31 bits, would still send `2^32 + 7` to 7 and
close the pin above, while `wait4(-1, …)` went `unmodeled` where Linux
and the arm answer `-ECHILD`.  So the all-ones low half is kept as
`2^32 - 1`, not carried through as the all-ones register.  The probe
above passes exactly that low half, under a set bit 32.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem pid32_does_not_sign_extend :
    pid32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) ∧
    pid32 (Z_to_bv 64 (2 ^ 32 - 1)) ≠ Z_to_bv 64 (-1) :=
  have h : pid32 (Z_to_bv 64 (2 ^ 32 - 1)) = Z_to_bv 64 (2 ^ 32 - 1) := by decide
  ⟨h, by rw [h]; decide⟩

/-- `wait4(pid, status, 2^32 + WNOHANG, ru)` does not block: `options`
is `int` in the same prototype (kernel/exit.c:1907-1908, Linux v6.18.46),
and `WNOHANG` is 1 (include/uapi/linux/wait.h:5).  Probed: the same
`trunc` case of `testing/syscall-check/tests/wait4_spec.c`, whose
`options` is `2^32 + 1`.
kernel: kernel/exit.c:wait4; include/uapi/linux/wait.h:WNOHANG@v6.18.46 -/
theorem waitopts32_is_the_int_cast :
    waitopts32 (Z_to_bv 64 (2 ^ 32 + 1)) = Z_to_bv 64 1 ∧
    waitopts32 (Z_to_bv 64 (2 ^ 32 + 1)) ≠ Z_to_bv 64 (2 ^ 32 + 1) :=
  have h : waitopts32 (Z_to_bv 64 (2 ^ 32 + 1)) = Z_to_bv 64 1 := by decide
  ⟨h, by rw [h]; decide⟩

/-- `pipe2(fds, 2^32 + O_NONBLOCK)` makes both ends non-blocking:
`flags` is `int` (`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int,
flags)`, fs/pipe.c:1054, Linux v6.18.46), and `O_NONBLOCK` is 00004000
(include/uapi/asm-generic/fcntl.h:38).  No probe drives pipe2's `flags`
with a high half at this head.
kernel: fs/pipe.c:pipe2; include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
theorem pipe_flags32_is_the_int_cast :
    pipe_flags32 (Z_to_bv 64 (2 ^ 32 + 2048)) = Z_to_bv 64 2048 ∧
    pipe_flags32 (Z_to_bv 64 (2 ^ 32 + 2048)) ≠ Z_to_bv 64 (2 ^ 32 + 2048) :=
  have h : pipe_flags32 (Z_to_bv 64 (2 ^ 32 + 2048)) = Z_to_bv 64 2048 := by decide
  ⟨h, by rw [h]; decide⟩

/-- `w_is0` tests the WHOLE register, the shape of a `size_t` argument —
`write`'s `count` is `size_t` (`SYSCALL_DEFINE3(write, unsigned int, fd,
const char __user *, buf, size_t, count)`, fs/read_write.c:746, Linux
v6.18.46), 64 bits wide on riscv64 — so a count of `2^32` is not zero to
it.  The negatives are the two mistakes: a low-half test, which would
call `2^32` zero, and a test against the wrong constant.  No probe
drives `write` with a count of 2^32 at this head.
kernel: fs/read_write.c:write@v6.18.46 -/
theorem w_is0_is_a_full_register_test :
    w_is0 (Z_to_bv 64 0) = true ∧
    w_is0 (Z_to_bv 64 (2 ^ 32)) = false ∧
    w_is0 (Z_to_bv 64 1) = false ∧
    w_is0 (Z_to_bv 64 (2 ^ 64 - 1)) = false := by decide

end NarrowingPins

section SignedReadPins

/-- `socket(2^32 + AF_INET, ...)`: `int family` is 2, so garbage in the
high half of a0 does not make `__sock_create`'s `family < 0` test fire
(net/socket.c:1545, Linux v6.18.46, commit 1f99e9ab748f; net/socket.c:1515
at v6.12, the version `Sys/Net/Socket.v` reads).
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem sint32_drops_the_high_half : sint32 (Z_to_bv 64 (2 ^ 32 + 2)) = 2 := by decide

/-- A low half of all ones is `family = -1`, which `__sock_create`'s
`family < 0 || family >= NPROTO` test (net/socket.c:1545 at v6.18.46,
:1515 at v6.12) rejects with -EAFNOSUPPORT.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem sint32_all_ones_is_minus_one : sint32 (Z_to_bv 64 (2 ^ 32 - 1)) = -1 := by decide

/-- The all-ones REGISTER reads the same way: its low half is all ones.
kernel: net/socket.c:socket@v6.18.46 -/
theorem sint32_all_ones_register_is_minus_one :
    sint32 (Z_to_bv 64 (2 ^ 64 - 1)) = -1 := by decide

/-- `INT_MAX` is the last non-negative `int`.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem sint32_int_max_is_positive :
    sint32 (Z_to_bv 64 (2 ^ 31 - 1)) = 2 ^ 31 - 1 := by decide

/-- Bit 31 alone is `INT_MIN`, not `2^31`: the sign test fires.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem sint32_bit31_is_int_min : sint32 (Z_to_bv 64 (2 ^ 31)) = -(2 ^ 31) := by decide

/-- A register with only bit 63 set is `family = 0` (AF_UNSPEC): the sign
test does NOT fire, whatever the high half looks like.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem sint32_bit63_is_zero : sint32 (Z_to_bv 64 (2 ^ 63)) = 0 := by decide

/-- The mistake: reading the low half unsigned, which turns `-1` into a
huge positive family that the sign test would pass.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem sint32_is_not_the_unsigned_low_half :
    sint32 (Z_to_bv 64 (2 ^ 32 - 1)) ≠ 2 ^ 32 - 1 := by
  rw [sint32_all_ones_is_minus_one]
  decide

/-- The other mistake: comparing the full register, which invents a
failure for a high half the kernel never sees.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem sint32_is_not_the_full_register :
    sint32 (Z_to_bv 64 (2 ^ 32 + 2)) ≠ 2 ^ 32 + 2 := by
  rw [sint32_drops_the_high_half]
  decide

/-- A MODEL-CONSISTENCY lemma, not a kernel pin: its right-hand side is
another definition of this tree, so it fixes nothing about Linux and a
port that re-read BOTH sides unsigned would still close it.  What it
does fix is that `sint32` and `nfds_signed ∘ nfds32` are one reading
spelled twice — each is the `int` parameter cast of a `SYSCALL_DEFINE`,
applied to socket's `family` (`SYSCALL_DEFINE3(socket, int, family, ...)`,
net/socket.c:1760, Linux v6.18.46, commit 1f99e9ab748f) and to pselect6's
`n` (`SYSCALL_DEFINE6(pselect6, int, n, ...)`, fs/select.c:793) alike, so
the two definitions cannot disagree on any register.
model: `sint32` and `nfds_signed ∘ nfds32` are one `int` cast spelled twice, an identity of the model's own definitions closed by `rfl`; the kernel half is the concrete pins on either side of it. -/
theorem sint32_eq_nfds_signed_nfds32 (w : word) : sint32 w = nfds_signed (nfds32 w) := rfl

/-- pselect6's `int n` with bit 31 set is negative and fails
`core_sys_select`'s `n < 0` test with -EINVAL (fs/select.c:633, Linux
v6.18.46, commit 1f99e9ab748f; unchanged bar `unlikely()` from v6.1, per
`Sys/Fs/Select.v`).  That test is the LAST gate before the fd sets are
read, not the first: `SYSCALL_DEFINE6(pselect6, …)` (fs/select.c:793-803)
copies the {sigset *, size} pair in through `get_sigset_argpack`
(-EFAULT) before it calls `do_pselect`; `do_pselect` (fs/select.c:728-761)
copies the timespec in through `get_timespec64` (-EFAULT), validates it
in `poll_select_set_timeout` (-EINVAL, fs/select.c:271-276), runs
`set_user_sigmask` (kernel/signal.c:3281-3290 at v6.18.46: 0 for a NULL
mask before anything else, then -EINVAL on a wrong `sigsetsize`, then
-EFAULT copying the mask in), and only then `core_sys_select`.  Three
copy-ins and two earlier -EINVALs therefore sit in front of this one, and
`Sys/Fs/Select.v`'s `pselect6_outcome` lists its arms in exactly that
order.
kernel: fs/select.c:core_sys_select,pselect6,get_sigset_argpack,do_pselect,poll_select_set_timeout; kernel/time/time.c:get_timespec64; kernel/signal.c:set_user_sigmask@v6.18.46 -/
theorem nfds_signed_bit31_is_negative :
    nfds_signed (nfds32 (Z_to_bv 64 (2 ^ 31))) = -(2 ^ 31) := by decide

/-- `INT_MAX` is the last `n` that passes `n < 0`.
kernel: fs/select.c:core_sys_select@v6.18.46 -/
theorem nfds_signed_int_max_is_positive :
    nfds_signed (nfds32 (Z_to_bv 64 (2 ^ 31 - 1))) = 2 ^ 31 - 1 := by decide

/-- pselect6's `int n` is the low half only: `2^32 + 3` is `n = 3`.
kernel: fs/select.c:pselect6@v6.18.46 -/
theorem nfds_signed_drops_the_high_half :
    nfds_signed (nfds32 (Z_to_bv 64 (2 ^ 32 + 3))) = 3 := by decide

/-- A register with only bit 63 set is `n = 0`.
kernel: fs/select.c:pselect6@v6.18.46 -/
theorem nfds_signed_bit63_is_zero : nfds_signed (nfds32 (Z_to_bv 64 (2 ^ 63))) = 0 := by decide

/-- The all-ones register is `n = -1`.
kernel: fs/select.c:pselect6@v6.18.46 -/
theorem nfds_signed_all_ones_register_is_minus_one :
    nfds_signed (nfds32 (Z_to_bv 64 (2 ^ 64 - 1))) = -1 := by decide

/-- A low half of all ones is `n = -1` to pselect6, the `n < 0` -EINVAL of
`core_sys_select` (fs/select.c:633, v6.18.46), whatever the high half
holds.
kernel: fs/select.c:core_sys_select@v6.18.46 -/
theorem nfds_signed_all_ones_low_half_is_minus_one :
    nfds_signed (nfds32 (Z_to_bv 64 (2 ^ 32 - 1))) = -1 := by decide

/-- The mistake, as that equality's corollary: an unsigned reading of
pselect6's `n`, under which `-1` would be a huge count instead of the
`n < 0` -EINVAL Linux returns.
kernel: fs/select.c:core_sys_select@v6.18.46 -/
theorem nfds_signed_is_not_unsigned :
    nfds_signed (nfds32 (Z_to_bv 64 (2 ^ 32 - 1))) ≠ 2 ^ 32 - 1 := by
  rw [nfds_signed_all_ones_low_half_is_minus_one]
  decide

/-- ppoll's `unsigned int nfds` with bit 31 set is a huge count, not a
negative one: `do_sys_poll` compares it unsigned against
`rlimit(RLIMIT_NOFILE)` (fs/select.c:967-982, Linux v6.18.46, commit
1f99e9ab748f).
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem unfds32_bit31_is_a_huge_count :
    bv_unsigned (unfds32 (Z_to_bv 64 (2 ^ 31))) = 2 ^ 31 := by decide

/-- The all-ones register is the largest `unsigned int` count.
kernel: fs/select.c:ppoll@v6.18.46 -/
theorem unfds32_all_ones_register_is_uint_max :
    bv_unsigned (unfds32 (Z_to_bv 64 (2 ^ 64 - 1))) = 2 ^ 32 - 1 := by decide

/-- A register with only bit 63 set is zero pollfds.
kernel: fs/select.c:ppoll@v6.18.46 -/
theorem unfds32_bit63_is_zero : bv_unsigned (unfds32 (Z_to_bv 64 (2 ^ 63))) = 0 := by decide

/-- ppoll's `nfds` is the low half only: `2^32 + 1` is one pollfd.
kernel: fs/select.c:ppoll@v6.18.46 -/
theorem unfds32_drops_the_high_half :
    bv_unsigned (unfds32 (Z_to_bv 64 (2 ^ 32 + 1))) = 1 := by decide

/-- The mistake: a full-register count, which fails the rlimit test for a
caller Linux serves.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem unfds32_is_not_the_full_register :
    bv_unsigned (unfds32 (Z_to_bv 64 (2 ^ 32 + 1))) ≠ 2 ^ 32 + 1 := by
  rw [unfds32_drops_the_high_half]
  decide

end SignedReadPins

section CopyinPins

/-- Inversion of `record_copyins` on an `Ok`: the inner spec produced the
same model and events, and the outcome's effect is the inner effect with
the wrapper's reads prepended.  What the negative pins below take apart
instead of `Monad.bind`'s existential; the `→` of `record_copyins_ok_iff`.
  K1's `Checks/Sys/Prelude.lean` (#766) carries its own proof of the same
statement; the two are to be reconciled when it lands.
model: the `→` of `Sys.Syscall.record_copyins_ok_iff`; twin of `Checks/Sys/Prelude.v`'s `record_copyins_ok_inv`. -/
theorem record_copyins_ok_inv (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (eff' : SyscallEffect) (m' : Model) (evs : List event) :
    record_copyins reads spec i m (Ok eff' m' evs) →
    ∃ eff, spec i m (Ok eff m' evs) ∧ eff' = with_copyins (reads ++ eff.eff_copyins) eff :=
  (record_copyins_ok_iff reads spec i m eff' m' evs).1

/-- Inversion of `record_copyins` on a decline: only the inner spec can
have declined, since the wrapper's own step is a `pure`.  The `→` of
`record_copyins_unmodeled_iff`.
  K1's `Checks/Sys/Prelude.lean` (#766) carries its own proof of the same
statement; the two are to be reconciled when it lands.
model: the `→` of `Sys.Syscall.record_copyins_unmodeled_iff`; twin of `Checks/Sys/Prelude.v`'s `record_copyins_unmodeled_inv`. -/
theorem record_copyins_unmodeled_inv (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    record_copyins reads spec i m Unmodeled → spec i m Unmodeled :=
  (record_copyins_unmodeled_iff reads spec i m).1

variable (a b r : word) (i : SyscallInput) (m : Model)

/-- A syscall that copied `[(b, 2)]` from user memory before an inner
step that itself copied `[(a, 1)]` is charged for both, in that order.
model: the ledger convention of `Sys.Syscall.record_copyins`, reads prepended; no kernel claim beyond what `State.materialize_model_accesses` charges. -/
theorem record_copyins_charges_the_read :
    record_copyins [(b, 2)] (Monad.pure (with_copyins [(a, 1)] (mkEffect r [] []))) i m
      (Ok (with_copyins [(b, 2), (a, 1)] (mkEffect r [] [])) m []) :=
  record_copyins_ok _ _ i m _ m [] (Monad.pure_ok _ i m)

/-- The mistake: an outcome whose ledger omits the wrapper's read, which
would claim the syscall read less user memory than it did and undercharge
`State.materialize_model_accesses`.
model: refutation of a ledger that omits the wrapper's read; no kernel claim. -/
theorem record_copyins_never_drops_the_read :
    ¬ record_copyins [(b, 2)] (Monad.pure (with_copyins [(a, 1)] (mkEffect r [] []))) i m
        (Ok (with_copyins [(a, 1)] (mkEffect r [] [])) m []) := by
  intro h
  obtain ⟨eff, h1, h2⟩ := record_copyins_ok_inv _ _ i m _ m [] h
  simp only [Monad.pure, outcome.Ok.injEq] at h1
  obtain ⟨rfl, -, -⟩ := h1
  simp only [with_copyins, List.cons_append, List.nil_append,
    SyscallEffect.mkEffectU.injEq, List.cons.injEq, reduceCtorEq, and_false] at h2

/-- The ledger is `reads ++ eff_copyins`, in Rocq's order and no other.  A
port that appended instead would charge the same bytes, but
`State.materialize_model_accesses` folds the ledger in order and
`State.page_insert` prepends, so its `m_vm_materialized` would come out
in another order and its models would stop being equal to the ones the
Rocq checker proofs are stated on.
model: refutation of the appended ledger order; a model-equality convention, not a kernel claim. -/
theorem record_copyins_keeps_rocq_ledger_order :
    ¬ record_copyins [(b, 2)] (Monad.pure (with_copyins [(a, 1)] (mkEffect r [] []))) i m
        (Ok (with_copyins [(a, 1), (b, 2)] (mkEffect r [] [])) m []) := by
  intro h
  obtain ⟨eff, h1, h2⟩ := record_copyins_ok_inv _ _ i m _ m [] h
  simp only [Monad.pure, outcome.Ok.injEq] at h1
  obtain ⟨rfl, -, -⟩ := h1
  simp only [with_copyins, List.cons_append, List.nil_append,
    SyscallEffect.mkEffectU.injEq, List.cons.injEq, Prod.mk.injEq, Nat.reduceEqDiff,
    and_false, false_and] at h2

/-- Recording a read never turns a modeled call into a decline.
model: the wrapper's own step is a `pure`; no kernel claim. -/
theorem record_copyins_never_invents_a_decline :
    ¬ record_copyins [(b, 2)] (Monad.pure (mkEffect r [] [])) i m Unmodeled :=
  fun h => absurd (record_copyins_unmodeled_inv _ _ i m h)
    (by simp only [Monad.pure, reduceCtorEq, not_false_eq_true])

/-- The converse mistake: swallowing an inner decline into an `Ok` with an
empty ledger, which would turn a fail-closed answer into a modeled one.
model: refutation of an `Ok` over a declined inner step; no kernel claim. -/
theorem record_copyins_never_swallows_a_decline (eff : SyscallEffect) (m' : Model)
    (evs : List event) :
    ¬ record_copyins [(b, 2)] Monad.unmodeled i m (Ok eff m' evs) := by
  intro h
  obtain ⟨_, h1, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
  exact absurd h1 (by simp only [Monad.unmodeled, reduceCtorEq, not_false_eq_true])

/-- The inner spec's events pass through the wrapper untouched.
model: the wrapper passes the inner events through; no kernel claim. -/
theorem record_copyins_keeps_events (ev : event) :
    record_copyins [(b, 2)] (fun _ m o => o = Ok (mkEffect r [] []) m [ev]) i m
      (Ok (with_copyins [(b, 2)] (mkEffect r [] [])) m [ev]) :=
  record_copyins_ok_empty _ _ i m _ m [ev] rfl rfl

/-- The mistake: a wrapper that drops the inner spec's events.
model: refutation of a dropped event list; no kernel claim. -/
theorem record_copyins_never_drops_events (ev : event) :
    ¬ record_copyins [(b, 2)] (fun _ m o => o = Ok (mkEffect r [] []) m [ev]) i m
        (Ok (with_copyins [(b, 2)] (mkEffect r [] [])) m []) := by
  intro h
  obtain ⟨_, h1, -⟩ := record_copyins_ok_inv _ _ i m _ m [] h
  simp only [outcome.Ok.injEq, reduceCtorEq, and_false] at h1

/-- A decline stays a decline, whatever was read: the ledger is never
attached to a call the model does not cover, so a `copy_from_user` the
model cannot account for still fails closed.
model: `outcome_copyins` at `Unmodeled`, by definition; no kernel claim. -/
theorem outcome_copyins_keeps_a_decline (reads : List (word × Nat)) :
    outcome_copyins reads Unmodeled = Unmodeled := rfl

/-- The mistake, as that equality's corollary: ledgering a decline as if
it were a modeled `Ok`.
model: the corollary of `outcome_copyins_keeps_a_decline`; no kernel claim. -/
theorem outcome_copyins_never_ledgers_a_decline (reads : List (word × Nat))
    (eff : SyscallEffect) (evs : List event) :
    outcome_copyins reads Unmodeled ≠ Ok eff m evs := by
  rw [outcome_copyins_keeps_a_decline]
  exact nofun

/-- `outcome_copyins` on an `Ok` is `record_copyins`'s ledger rule as a
function: the wrapper's reads go in front of the inner ledger.  A
MODEL-CONSISTENCY pair like the ledger pins above it: nothing in Linux
orders a ledger, and the authority for the order is Rocq's
`Syscall.outcome_copyins` (`Sys/Syscall.v`), which the twin's docstring
explains `State.materialize_model_accesses` depends on.
model: the ledger convention of `Sys.Syscall.outcome_copyins` at `Ok`, reads prepended, the order `record_copyins_keeps_rocq_ledger_order` fixes on the monad; no kernel claim. -/
theorem outcome_copyins_ledgers_an_ok (evs : List event) :
    outcome_copyins [(b, 2)] (Ok (with_copyins [(a, 1)] (mkEffect r [] [])) m evs)
      = Ok (with_copyins [(b, 2), (a, 1)] (mkEffect r [] [])) m evs := rfl

/-- The mistake, as that equality's corollary: the inner ledger in front
of the wrapper's — the order `record_copyins_keeps_rocq_ledger_order`
refuses on the monad, refused here on the function too.
model: refutation of the appended ledger order on `Sys.Syscall.outcome_copyins`; a model-equality convention, not a kernel claim. -/
theorem outcome_copyins_keeps_rocq_ledger_order (evs : List event) :
    outcome_copyins [(b, 2)] (Ok (with_copyins [(a, 1)] (mkEffect r [] [])) m evs)
      ≠ Ok (with_copyins [(a, 1), (b, 2)] (mkEffect r [] [])) m evs := by
  rw [outcome_copyins_ledgers_an_ok]
  intro h
  simp only [outcome.Ok.injEq, with_copyins, SyscallEffect.mkEffectU.injEq, List.cons.injEq,
    Prod.mk.injEq, Nat.reduceEqDiff, and_false, false_and] at h

end CopyinPins

section ErrnoPins

variable (i : SyscallInput) (m : Model)

/-- `ENOMEM` is an answer an anonymous `mmap` really gives — `do_mmap`
returns it for a length that rounds to zero and for a full map table
(mm/mmap.c:368-378, Linux v6.18.46, commit 1f99e9ab748f) — so a failure
branch drawn from a list naming it may answer -ENOMEM.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem errno_from_admits_a_listed_errno : errno_from [ENOMEM] i m (Ok ENOMEM m []) :=
  Monad.choose_ok _ ENOMEM i m (List.mem_singleton.mpr rfl)

/-- The mistake: drawing an errno outside the list.  -EBADF is a real
`mmap` answer on Linux — `ksys_mmap_pgoff`'s `fget` failing on a
file-backed request (mm/mmap.c:566-577, v6.18.46) — but it belongs to
the path `Sys/Mm/Mmap.v` declines; a branch drawn from a list that does
not name it may not invent it.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem errno_from_never_widens : ¬ errno_from [ENOMEM] i m (Ok EBADF m []) := by
  rintro ⟨x, hx, hx'⟩
  simp only [outcome.Ok.injEq] at hx'
  obtain ⟨rfl, -, -⟩ := hx'
  exact absurd hx (by decide)

/-- An empty injectable set admits no failure at all.
model: `errno_from []` is `choose` over an empty membership; no kernel claim. -/
theorem errno_from_empty_admits_nothing (e : Int) : ¬ errno_from [] i m (Ok e m []) := by
  rintro ⟨x, hx, -⟩
  cases hx

/-- A draw moves neither the model nor the event list.
model: a `choose` moves neither the model nor the events, by definition; no kernel claim. -/
theorem errno_from_is_pure (m' : Model) (evs : List event) (e : Int) :
    errno_from [ENOMEM] i m (Ok e m' evs) → m' = m ∧ evs = [] := by
  rintro ⟨x, -, hx'⟩
  simp only [outcome.Ok.injEq] at hx'
  obtain ⟨-, rfl, rfl⟩ := hx'
  exact ⟨rfl, rfl⟩

end ErrnoPins

/-! ## Ticket D4: `record_copyins` read by `sys_norm`

`record_copyins_iff`, registered in `sys_simp` by `Checks/Cases/Tactic.lean`,
reads the wrapper continuation first — `∃ o', spec i m o' ∧ o =
outcome_copyins reads o'` — and `outcome_copyins`'s two equations then
attach the ledger to each outcome the inner spec is read to.  That reading
matches the wrapper at a full application only; where a spec BINDS the
wrapper's result, `record_copyins reads spec` is a two-argument child that
the reading cannot see, and the register's `record_copyins.eq_1` (at the
low priority of every unfolding, so the reading wins wherever both match)
opens it for `bind_bind_iff` instead.  The programs below exercise both
routes and are registered `local`; the twins of Rocq's two inversions are
the `.1` of the constructor-shaped iffs and sit in the copy-in section
above. -/

section TicketD4

/-- A syscall that read eight bytes at `buf` and then fails with one of two
errnos. -/
def ledger_demo (buf : word) : Sys SyscallEffect :=
  record_copyins [(buf, 8)] (e <- errno_from [EINVAL, EFAULT] ;; err_ret e)

/-- …and one whose inner step declines. -/
def ledger_decline_demo (buf : word) : Sys SyscallEffect :=
  record_copyins [(buf, 8)] Monad.unmodeled

/-- A syscall whose inner step had already read `[(a, 1)]` and emitted `ev`
when the wrapper charges `[(buf, 8)]`: the two ledgers meet in Rocq's order
and the event passes through. -/
def ledger_order_demo (buf a : word) (ev : event) : Sys SyscallEffect :=
  record_copyins [(buf, 8)]
    (emit [ev] ;; Monad.pure (with_copyins [(a, 1)] (mkEffect 0 [] [])))

/-- …and the wrapper's result BOUND under a further `bind`, the shape the
five-argument reading cannot match. -/
def ledger_bound_demo (buf : word) : Sys SyscallEffect :=
  eff <- record_copyins [(buf, 8)] (ret_only 0) ;; Monad.pure eff

attribute [local sys_simp low]
  ledger_demo.eq_1 ledger_decline_demo.eq_1 ledger_order_demo.eq_1 ledger_bound_demo.eq_1

variable (buf : word) (i : SyscallInput) (m : Model)

/-- Read off: each errno outcome carries the ledger, with the model and the
events untouched.
model: `Sys.Syscall.record_copyins_iff` through `sys_norm`, the reading `Checks/Cases/Tactic.lean` registers; no kernel claim. -/
theorem ledger_demo_iff (o : outcome SyscallEffect) :
    ledger_demo buf i m o ↔
      (o = Ok (with_copyins [(buf, 8)] (mkEffect (errno_ret EINVAL) [] [])) m [] ∨
       o = Ok (with_copyins [(buf, 8)] (mkEffect (errno_ret EFAULT) [] [])) m []) := by
  sys_norm

/-- The mistake: an outcome with the ledger dropped, refuted whatever
model and events it claims.
model: refutation of a forged outcome by `sys_refute`; no kernel claim. -/
theorem ledger_demo_never_drops_the_read (m' : Model) (evs : List event) :
    ¬ ledger_demo buf i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The wrapper never declines on its own.
model: `sys_refute` on the `Unmodeled` arm of `Sys.Syscall.record_copyins_iff`; no kernel claim. -/
theorem ledger_demo_never_unmodeled : ¬ ledger_demo buf i m Unmodeled := by
  sys_refute

/-- …and a declined inner step stays declined, whatever was read.
model: `Sys.Syscall.record_copyins_iff` at `outcome_copyins reads Unmodeled`; no kernel claim. -/
theorem ledger_decline_demo_iff (o : outcome SyscallEffect) :
    ledger_decline_demo buf i m o ↔ o = Unmodeled := by
  sys_norm

/-- Read off through `sys_norm`: the wrapper's read FIRST, then the inner
step's, and the inner event kept.
model: `Sys.Syscall.record_copyins_iff` through `sys_norm` on an inner step with its own ledger and event; no kernel claim. -/
theorem ledger_order_demo_iff (a : word) (ev : event) (o : outcome SyscallEffect) :
    ledger_order_demo buf a ev i m o ↔
      o = Ok (with_copyins [(buf, 8), (a, 1)] (mkEffect 0 [] [])) m [ev] := by
  sys_norm

/-- The mistake: the appended order, refuted on the ledger whatever model and
events it claims — the two entries differ in their lengths, so no choice of
addresses makes the swapped list the right one.
model: refutation of the appended ledger order through `sys_refute`; a model-equality convention, not a kernel claim. -/
theorem ledger_order_demo_keeps_rocq_order (a : word) (ev : event) (m' : Model)
    (evs : List event) :
    ¬ ledger_order_demo buf a ev i m
        (Ok (with_copyins [(a, 1), (buf, 8)] (mkEffect 0 [] [])) m' evs) := by
  sys_refute

/-- The other mistake: a wrapper that drops the inner step's event.
model: refutation of a dropped event list through `sys_refute`; no kernel claim. -/
theorem ledger_order_demo_keeps_events (a : word) (ev : event) (m' : Model) :
    ¬ ledger_order_demo buf a ev i m
        (Ok (with_copyins [(buf, 8), (a, 1)] (mkEffect 0 [] [])) m' []) := by
  sys_refute

/-- The bound shape reads to the same ledger: `record_copyins.eq_1` opens the
wrapper under the outer `bind`, `bind_bind_iff` reassociates, and the two
`pure`s are read.  Without that unfolding in the register this statement is
left at the wrapper and does not close.
model: `Sys.Syscall.record_copyins`'s unfolding through `sys_norm`, the low-priority route `Checks/Cases/Tactic.lean` registers; no kernel claim. -/
theorem ledger_bound_demo_iff (o : outcome SyscallEffect) :
    ledger_bound_demo buf i m o ↔ o = Ok (with_copyins [(buf, 8)] (mkEffect 0 [] [])) m [] := by
  sys_norm

end TicketD4

section ReturnPins

variable (r : word) (i : SyscallInput) (m : Model)

/-- `ret_only r` answers `r` in a0 and does nothing else: no write, no
zeroing, no ledger, the model and the event list untouched.  It is the
shape of every arm that returns without touching user memory, and it is
a `pure`, so this is the one outcome it has.  The kernel half of that
shape is the trap path: `do_trap_ecall_u` saves a0 to `orig_a0` and
presets a0 to `-ENOSYS` for every ecall (arch/riscv/kernel/traps.c:333-334,
Linux v6.18.46), and for an in-range number, the test at
arch/riscv/kernel/traps.c:342-345 (Linux v6.18.46), hands the frame to
`syscall_handler`, whose only register write is `regs->a0 = fn(regs)`
(arch/riscv/include/asm/syscall.h:112, Linux v6.18.46) — a handler that touches no user memory changes a0 and
nothing else.  The lemma itself is a MODEL-CONSISTENCY fact, a `pure`
unfolded; what it buys is the negative below.
kernel: arch/riscv/kernel/traps.c:do_trap_ecall_u; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem ret_only_answers_the_register : ret_only r i m (Ok (mkEffect r [] []) m []) :=
  Monad.pure_ok _ i m

/-- The mistake a fail-closed port makes silently: declining where the
arm answers.  `ret_only` has no `Unmodeled` outcome — a handler in
`sys_call_table` returns a `long` and `syscall_handler` stores it, there
is no third case — so an arm built on it that declines does so in its
own guard, never here.  The mutation tester's `outcome-unmodeled`
mutant of `ret_only` falsifies this pin; the tester's report names
whichever module breaks first, `Checks/Cases/Tactic.lean`'s
`errno_demo_iff` since #793, so it does not name this file.
kernel: arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem ret_only_never_declines : ¬ ret_only r i m Unmodeled := by
  simp only [ret_only, Monad.pure, reduceCtorEq, not_false_eq_true]

/-- The a0 word for `-EBADF`, stated once so that both `EBADF` pins below
are derived from it: `errno_ret e` is `Z_to_bv 64 (-e)` and `EBADF` is 9
(include/uapi/asm-generic/errno-base.h:13, Linux v6.18.46).
kernel: include/uapi/asm-generic/errno-base.h:EBADF@v6.18.46 -/
theorem errno_ret_EBADF_in_a0 : errno_ret EBADF = Z_to_bv 64 (2 ^ 64 - 9) := by decide

/-- The same for `-EINVAL`: `EINVAL` is 22 (include/uapi/asm-generic/errno-base.h:26,
Linux v6.18.46).
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem errno_ret_EINVAL_in_a0 : errno_ret EINVAL = Z_to_bv 64 (2 ^ 64 - 22) := by decide

/-- A failing syscall lands its errno in a0 NEGATED, as the 64-bit two's
complement of the `long` the handler returned: `syscall_handler` writes
`regs->a0 = fn(regs)` (arch/riscv/include/asm/syscall.h:112, Linux
v6.18.46, commit 1f99e9ab748f) with no sign manipulation, so -EBADF is
`0xFFFFFFFFFFFFFFF7`, inside the `[-MAX_ERRNO, -1]` band (`MAX_ERRNO`
4095, include/linux/err.h:18).  The kernel itself reads that band as an
error through `IS_ERR_VALUE` (include/linux/err.h:28, Linux v6.18.46),
which `syscall_get_error` applies to a0 (arch/riscv/include/asm/syscall.h:46-52,
Linux v6.18.46); that a libc — musl, glibc — turns the same band into `errno` and a `-1`
return is the libc's convention and outside this model.
kernel: arch/riscv/include/asm/syscall.h:syscall_handler,syscall_get_error; include/linux/err.h:IS_ERR_VALUE; include/uapi/asm-generic/errno-base.h:EBADF@v6.18.46 -/
theorem err_ret_is_minus_errno_in_a0 :
    err_ret EBADF i m (Ok (mkEffect (Z_to_bv 64 (2 ^ 64 - 9)) [] []) m []) := by
  unfold err_ret ret_only
  rw [errno_ret_EBADF_in_a0]
  exact Monad.pure_ok _ i m

/-- The mistake, as that equality's corollary: the errno returned POSITIVE,
which a caller would take for a successful return of 9.
kernel: arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem err_ret_is_not_the_positive_errno :
    ¬ err_ret EBADF i m (Ok (mkEffect (Z_to_bv 64 9) [] []) m []) := by
  intro h
  simp only [err_ret, ret_only, Monad.pure, outcome.Ok.injEq, mkEffect,
    SyscallEffect.mkEffectU.injEq, and_true] at h
  rw [errno_ret_EBADF_in_a0] at h
  exact absurd h (by decide)

/-- `err_ret` negates ITS argument: a handler that returned `-EINVAL`
lands `0xFFFFFFFFFFFFFFEA` in a0 by the same `regs->a0 = fn(regs)`.
kernel: arch/riscv/include/asm/syscall.h:syscall_handler; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem err_ret_uses_its_errno :
    err_ret EINVAL i m (Ok (mkEffect (Z_to_bv 64 (2 ^ 64 - 22)) [] []) m []) := by
  unfold err_ret ret_only
  rw [errno_ret_EINVAL_in_a0]
  exact Monad.pure_ok _ i m

/-- The mistake, as that equality's corollary: one fixed errno for every
failure.  A port `err_ret e := ret_only (errno_ret EBADF)` closes both
`EBADF` pins above and is refused here — no kernel answers `-EBADF` to a
call whose handler returned `-EINVAL`.
kernel: arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem err_ret_is_not_a_fixed_errno :
    ¬ err_ret EINVAL i m (Ok (mkEffect (Z_to_bv 64 (2 ^ 64 - 9)) [] []) m []) := by
  intro h
  simp only [err_ret, ret_only, Monad.pure, outcome.Ok.injEq, mkEffect,
    SyscallEffect.mkEffectU.injEq, and_true] at h
  rw [errno_ret_EINVAL_in_a0] at h
  exact absurd h (by decide)

end ReturnPins

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Syscall
