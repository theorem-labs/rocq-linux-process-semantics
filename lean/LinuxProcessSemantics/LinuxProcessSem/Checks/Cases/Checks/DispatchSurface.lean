import LinuxProcessSemantics.LinuxProcessSem.Checks.DispatchSurface
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Namei

/-! # Checks.Cases.Checks.DispatchSurface — the surface, exercised on the tables

Pins over `Checks.DispatchSurface`, the twin of
`theories/LinuxProcessSem/Checks/DispatchSurface.v`.  Rocq has no check
file for it; what the Lean twin adds that Rocq does not have is the SHAPE
its direction 2 had to take over a partial checked table — the answering
check stated over the checked numbers, and the surface theorems under the
agreement hypothesis `Checks/Progress.lean` carries — and the two places
where a value had to be spelled because the Lean tree lacks the constant.
So this file does four things: it pins the probe fixtures where they carry
a kernel value, so that the value is held by something the checkers read;
it runs the answering check on the fixture tables of
`Checks/Cases/Checks/Sys/Dispatch.lean`, passing where every arm answers
and failing where one declines, so that the check is shown to be able to
fail whatever `checked_table` holds; it runs direction 2 through the same
fixture, so that its proof path is exercised before the first checked arm
lands; and it pins direction 1 at a number no table carries and at one the
spec table does.  The agreement hypothesis itself is pinned where it is
defined, in `Checks/Cases/Checks/ExecutableSpecs.lean`, and is not
re-pinned here.

Not part of the trusted specification: this file is QA on the
definitions, written to be READ.  Each decision gets an accepting and a
rejecting instance; where a kernel value is in play the pin is stated
against the kernel and cites it, and where the claim is the twin's own —
a fixture table's run, a model flag, the shape of the check — the pin
says so with a `model:` line.  The numbers are cited from the generic
table, `include/uapi/asm-generic/unistd.h`; riscv64 takes the same numbers
from the `asm/unistd_64.h` generated out of `scripts/syscall.tbl`.

The probe rows are pinned register by register because nothing else holds
them today: Rocq's `modeled_sysnos_probes_answer` evaluates every row
through its arm at build time, and the Lean check runs over the checked
numbers, which are none until the Track C tickets land.  A wrong row would
otherwise surface as `false = true` in `checked_sysnos_probes_answer` in
the ticket that registers that arm, debited to an author who did not write
the row; and where a wrong register still ANSWERS — Rocq's own case is
`futex`'s address, where the default `AT_FDCWD` would answer `-EFAULT` on
the gate instead of 0 on the operation, and `tgkill`'s group id, where any
positive id but the tid answers `-ESRCH` and a non-positive one answers
`-EINVAL` on the argument gate — it would never surface at all, because
the check asks only whether the arm answers. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.DispatchSurface

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.DispatchSurface
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Progress (exit_input)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork (clone3_fork_args_b)

/-! ## The probe memory

`clone3` reads its arguments through a pointer, and the arm admits one
struct: every field zero but `exit_signal`, which is `SIGCHLD`.  The probe
memory is all-NUL except that one byte, and where the byte sits is the
kernel's layout of the struct. -/

/-- THE PIN: the byte that makes the struct fork-shaped is at offset 32 —
`exit_signal` is the fifth `__aligned_u64` of `struct clone_args`
(`include/uapi/linux/sched.h`, Linux v6.18.46, commit 1f99e9ab748f), after
`flags`, `pidfd`, `child_tid` and `parent_tid` — and it holds `SIGCHLD`.
The kernel's own check on the field, in `copy_clone_args_from_user`, is
that no bit above `CSIGNAL` is set and that `valid_signal` holds; that the
arm admits exactly `SIGCHLD` there and nothing else is the model's fork
shape, `Kernel.Fork.clone3_fork_args_b`, and this pin holds the byte the
probe hands it.
kernel: kernel/fork.c:copy_clone_args_from_user; include/uapi/asm-generic/signal.h:SIGCHLD@v6.18.46 -/
theorem probe_mem_holds_sigchld_at_exit_signal :
    probe_mem (clone3_probe_uargs + Z_to_bv 64 32) = some (Z_to_bv 8 17) := by decide

/-- The struct's first field, `flags`, reads zero.  `copy_clone_args_from_user`
copies the word in whole (`.flags = args.flags`); the one test it runs on
the word itself is `CLONE_INTO_CGROUP` against `cgroup` and `usize`
(`kernel/fork.c:2798-2800`, Linux v6.18.46), which a zero word passes, and
the flag allowlist is `clone3_args_valid`'s, run after the copy.  A zero
word is the model's fork shape (`Kernel.Fork.clone3_fork_args_b`), not a
kernel requirement, and the pin holds the byte the probe hands it.
kernel: kernel/fork.c:copy_clone_args_from_user,clone3_args_valid@v6.18.46 -/
theorem probe_mem_is_nul_at_flags : probe_mem clone3_probe_uargs = some (Z_to_bv 8 0) := by decide

/-- The signal's upper bytes read zero too — 17 fits the low byte, and
`copy_clone_args_from_user` refuses any bit of `exit_signal` above
`CSIGNAL`, the low byte — and so does everything past the struct.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem probe_mem_is_nul_past_the_signal_byte :
    probe_mem (clone3_probe_uargs + Z_to_bv 64 33) = some (Z_to_bv 8 0)
      ∧ probe_mem (clone3_probe_uargs + Z_to_bv 64 88) = some (Z_to_bv 8 0) := by decide

/-- …and so does the byte before it, the top byte of `parent_tid`: the
exception is one byte wide.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem probe_mem_is_nul_before_the_signal_byte :
    probe_mem (clone3_probe_uargs + Z_to_bv 64 31) = some (Z_to_bv 8 0) := by decide

/-- Every address is readable: the probes that hand the kernel a pointer
(`prlimit64`'s `old_rlim`, `socketpair`'s `usockvec`, `clock_gettime`'s
`tp`, `clone3`'s 88-byte copy-in) rely on the fault gate passing.
model: `probe_mem`'s `some` at every address; no kernel behaviour is claimed -/
theorem probe_mem_is_readable_everywhere (a : word) : (probe_mem a).isSome = true := rfl

/-- THE BYTES THROUGH THE ARM'S OWN GATE.  The four pins above hold one
byte each; what they exist for is that `clone3_spec`'s predicate accepts
the 88 bytes it reads at `clone3_probe_uargs`, which settles the byte
order too — 17 at offset 32 is the LOW byte of `exit_signal`, so the word
is exactly `SIGCHLD` only because offsets 33 to 39 are zero.  Rocq needs
no such pin because its build evaluates the whole struct through the arm;
the Lean check does not until `clone3`'s arm is registered.
kernel: kernel/fork.c:copy_clone_args_from_user; include/uapi/linux/sched.h:CLONE_ARGS_SIZE_VER2@v6.18.46 -/
theorem the_clone3_probe_is_fork_shaped :
    (read_bytes_map probe_mem clone3_probe_uargs (Z_to_bv 64 88)).map clone3_fork_args_b
      = some true := by decide

/-- Rejected: the all-NUL struct — the constant memory `probe_mem` would be
without its one exception — is not fork-shaped, since `exit_signal` reads 0
where the arm wants `SIGCHLD`.
kernel: kernel/fork.c:copy_clone_args_from_user; include/uapi/asm-generic/signal.h:SIGCHLD@v6.18.46 -/
theorem an_all_nul_struct_is_not_fork_shaped :
    (read_bytes_map (fun _ => some (Z_to_bv 8 0)) clone3_probe_uargs (Z_to_bv 64 88)).map
      clone3_fork_args_b = some false := by decide

/-- Where the struct sits: far from 0 and from `AT_FDCWD`, the two
addresses every other probe uses — Rocq's own reason — so that the one
non-NUL byte is inside no other probe's read.  `0x10000` is above the
first and below the second; the pin is the distance, not the order.
model: `clone3_probe_uargs`'s value against the addresses the other rows carry; no kernel behaviour is claimed -/
theorem the_struct_sits_apart_from_the_other_probes_addresses :
    clone3_probe_uargs = Z_to_bv 64 0x10000 ∧ (probe_args 435).getD 0 (Z_to_bv 64 0) = clone3_probe_uargs
      := by decide

/-! ## The probe arguments

Two entries spell a value the Lean tree has no constant for, and this is
where the value is held: `MSG_NOSIGNAL` is `0x4000`, and `send_flags_modeled`
in Rocq compares against it exactly, so a wrong numeral would make both
probes decline.  The flag sits in a DIFFERENT REGISTER for the two calls,
which is the mistake the third pin rejects. -/

/-- `sendto(fd, buff, len, flags, addr, addr_len)`: the flag word is the
fourth argument, and the probe's is `MSG_NOSIGNAL`.
kernel: net/socket.c:sendto; include/linux/socket.h:MSG_NOSIGNAL@v6.18.46 -/
theorem sendto_probe_carries_msg_nosignal_in_a3 :
    (probe_args 206).getD 3 (Z_to_bv 64 0) = Z_to_bv 64 16384 := by decide

/-- `sendmsg(fd, msg, flags)`: the flag word is the third argument.
kernel: net/socket.c:sendmsg; include/linux/socket.h:MSG_NOSIGNAL@v6.18.46 -/
theorem sendmsg_probe_carries_msg_nosignal_in_a2 :
    (probe_args 211).getD 2 (Z_to_bv 64 0) = Z_to_bv 64 16384 := by decide

/-- Rejected: `sendto`'s third argument is `len`, not the flag word; the
probe leaves it zero.  A probe carrying the flag in `sendmsg`'s register
would hand `sendto` a zero flag word, which the arm declines.
kernel: net/socket.c:sendto@v6.18.46 -/
theorem sendto_probe_a2_is_the_zero_length :
    (probe_args 206).getD 2 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `tkill`'s probe sends `SIGABRT`, 6, the one signal any arm sends.  The
literal is the pin: stated through the constant the statement would hold
under any value of it.
kernel: include/uapi/asm-generic/signal.h:SIGABRT@v6.18.46 -/
theorem tkill_probe_sends_sigabrt :
    (probe_args 130).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 6 := by decide

/-- `tgkill`'s carries the signal one register later, after the two tids.
kernel: include/uapi/asm-generic/signal.h:SIGABRT@v6.18.46 -/
theorem tgkill_probe_sends_sigabrt_in_a2 :
    (probe_args 131).getD 2 (Z_to_bv 64 0) = Z_to_bv 64 6 := by decide

/-- `clone3`'s probe passes the size of the third published struct, 88
bytes, the one size the arm admits.
kernel: include/uapi/linux/sched.h:CLONE_ARGS_SIZE_VER2@v6.18.46 -/
theorem clone3_probe_passes_the_full_struct_size :
    (probe_args 435).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 88 := by decide

/-- The default row: `a0` is -100, `AT_FDCWD` (`include/uapi/linux/fcntl.h`,
Linux v6.18.46), the dirfd the path arms model and an fd no table holds —
the fd lookup is on an `unsigned int` (`__fget_light`) masked against
the table's size (`files_lookup_fd_raw`), so the value resolves in no
table.  17 is `getcwd`, which has no row of its own.  The constant is cited by its number rather than by name because the
Lean `AT_FDCWD` is a word, which the evidence checker cannot compare to
the header's literal.
kernel: include/uapi/asm-generic/unistd.h:__NR_getcwd; fs/file.c:__fget_light; include/linux/fdtable.h:files_lookup_fd_raw@v6.18.46 -/
theorem the_default_probe_hands_at_fdcwd_in_a0 :
    (probe_args 17).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 (-100) := by decide

/-- Raw DEL bypasses event copying and reaches the closed epfd in both halves.
model: the concrete answering witness for syscall 21 in checked_table -/
theorem epoll_ctl_del_probe_has_an_answer : probe_answers 21 = true := rfl

/-- The previous fixture defined bytes at NULL: Linux copied them before
returning EBADF, but QEMU's explicit NULL check answered EFAULT.
model: the previous surface fixture now has an Unmodeled witness -/
theorem epoll_ctl_old_null_event_probe_is_unmodeled :
    table_witness checked_table
      (SyscallInput.mkInput (Z_to_bv 64 21)
        [Z_to_bv 64 (-100), 0, 0, 0, 0, 0] probe_mem probe_mem)
      probe_model = Unmodeled := rfl

/-- The epoll surface witness has a nonnull mask with size zero and count
zero. Linux rejects the mask size; QEMU rejects the count with the same errno.
model: the concrete answering witness for syscall 22 in checked_table; no kernel behaviour is claimed -/
theorem epoll_pwait_probe_has_an_answer : probe_answers 22 = true := rfl

/-- Keep the invalid mask size and count that the answering probe needs.
model: the concrete registers of the epoll surface fixture -/
theorem epoll_pwait_probe_uses_bad_mask_size_and_zero_count :
    probe_args 22 = [Z_to_bv 64 (-100), 0, 0, 0, 1, 0] := rfl

/-- Lean declines the previous closed-descriptor/count-one fixture, so it
cannot witness an answering input on the narrowed surface.
model: the previous surface fixture now has an Unmodeled witness -/
theorem epoll_pwait_old_count_one_probe_is_unmodeled :
    table_witness checked_table
      (SyscallInput.mkInput (Z_to_bv 64 22)
        [Z_to_bv 64 (-100), 0, 1, 0, 0, 0] probe_mem probe_mem)
      probe_model = Unmodeled := rfl

/-- Restoring the old all-zero trailing registers makes this closed-epfd
fixture decline at maxevents zero, so it cannot witness that 22 has an
answering input for checked_sysnos_probes_answer.
model: the former probe_args default at syscall 22 is an Unmodeled witness; no kernel behaviour is claimed -/
theorem epoll_pwait_old_zero_count_probe_is_unmodeled :
    table_witness checked_table
      (SyscallInput.mkInput (Z_to_bv 64 22)
        [Z_to_bv 64 (-100), 0, 0, 0, 0, 0] probe_mem probe_mem)
      probe_model = Unmodeled := rfl

/-! ### Every other row, register by register

The header says why these are here.  Each names the register the kernel
reads the value from and, where the row leaves a register zero on
purpose, pins that too, so that a value moved one register over fails. -/

/-- The ioctl probe keeps the closed fd and selects a fd-first request.
Linux resolves the fd first; QEMU's entry for TIOCGWINSZ also reaches
safe_ioctl before copying to the guest (the source argument is on
Sys.Fs.Ioctl.ioctl_fd_first_request).
kernel: fs/ioctl.c:ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem ioctl_probe_carries_tiocgwinsz_in_a1 :
    (probe_args 29).getD 0 0 = Z_to_bv 64 (-100)
      ∧ (probe_args 29).getD 1 0 = Z_to_bv 64 21523 := by decide

/-- The probe reaches the closed-fd EBADF answer through the real table.
kernel: fs/ioctl.c:ioctl; drivers/tty/tty_io.c:tty_ioctl@v6.18.46 -/
theorem ioctl_probe_witness_answers_ebadf :
    table_witness checked_table (probe_input 29) probe_model
      = Ok (mkEffect (errno_ret EBADF) [] []) probe_model [] := rfl

/-- The old request-zero fixture declines: a closed fd alone no longer
makes an ioctl probe answer. QEMU do_ioctl can return ENOTTY before fd
lookup, unlike Linux fs/ioctl.c ioctl; the fd-first gate records that gap.
kernel: fs/ioctl.c:ioctl@v6.18.46 -/
theorem ioctl_default_request_witness_declines :
    table_witness checked_table
      (SyscallInput.mkInput 29 [Z_to_bv 64 (-100), 0, 0, 0, 0, 0] probe_mem probe_mem)
      probe_model = Unmodeled := rfl

/-- `eventfd2(count, flags)`: `O_LARGEFILE` in the flag word, outside
`EFD_FLAGS_SET`, which `do_eventfd` refuses with `-EINVAL` — an answer on
the flag gate, before any fd is allocated; the count is zero.
kernel: fs/eventfd.c:do_eventfd; include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
theorem eventfd2_probe_carries_o_largefile_in_a1 :
    (probe_args 19).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 32768
      ∧ (probe_args 19).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `mmap(addr, len, prot, flags, fd, off)`: a private anonymous mapping of
length zero.  `ksys_mmap_pgoff` tests nothing of a non-hugetlb length; it
is `do_mmap`, reached through `vm_mmap_pgoff`, that refuses a zero length
with `-EINVAL` before any placement.  The flag word is
`MAP_PRIVATE | MAP_ANONYMOUS`, 34, because the arm answers a zero length
only for an anonymous mapping and declines the default word.
kernel: mm/mmap.c:ksys_mmap_pgoff,do_mmap; include/uapi/linux/mman.h:MAP_PRIVATE; include/uapi/asm-generic/mman-common.h:MAP_ANONYMOUS@v6.18.46 -/
theorem mmap_probe_is_anonymous_private_and_empty :
    (probe_args 222).getD 3 (Z_to_bv 64 0) = Z_to_bv 64 34
      ∧ (probe_args 222).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- The mremap probe grows a tracked page because the former
misaligned/zero-size probe now declines (#1426).
kernel: mm/mremap.c:expand_vma@v6.18.46 -/
theorem mremap_probe_may_move :
    probe_args 216 = [65536, 4096, 8192, 1, 0, 0] := by decide

/-- `prlimit64(pid, resource, new_rlim, old_rlim)`: the caller's own
`RLIMIT_CORE`, read into a writable page; the Lean `spec_table` carries no
arm for 261 yet, so the row is held here alone until it does.
kernel: kernel/sys.c:prlimit64; include/uapi/asm-generic/resource.h:RLIMIT_CORE@v6.18.46 -/
theorem prlimit64_probe_reads_rlimit_core_of_itself :
    (probe_args 261).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 0
      ∧ (probe_args 261).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 4
      ∧ (probe_args 261).getD 2 (Z_to_bv 64 0) = Z_to_bv 64 0
      ∧ (probe_args 261).getD 3 (Z_to_bv 64 0) = Z_to_bv 64 4096 := by decide

/-- `socketpair(family, type, protocol, usockvec)`: an `AF_INET` stream
pair.  `__sys_socketpair` reserves two descriptors, stores both numbers
into `usockvec`, creates the two sockets, and only then asks the family's
pair operation — the INET stream ops table (`net/ipv4/af_inet.c`) has
`sock_no_socketpair` there, `-EOPNOTSUPP` — after which both numbers are
released.  So the answer is
an errno WITH the store already made, which is why the row's `a3` stays 0
and `probe_mem` is writable there; the arm mirrors the same order.
`SOCK_STREAM` is 1 (`include/linux/net.h`, an enumerator, so it is not
cited as a macro).
kernel: net/socket.c:__sys_socketpair; net/core/sock.c:sock_no_socketpair; include/linux/socket.h:AF_INET@v6.18.46 -/
theorem socketpair_probe_asks_for_an_inet_stream :
    (probe_args 199).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 2
      ∧ (probe_args 199).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 1 := by decide

/-- `clock_gettime(which_clock, tp)`: `CLOCK_REALTIME`, 0, the clock every
configuration has; Rocq chose it over `CLOCK_MONOTONIC` so that the probe
does not depend on the clock-envelope gate.  The row differs from the
default only in this register, which is why it is pinned as zero.
kernel: kernel/time/posix-timers.c:clock_gettime; include/uapi/linux/time.h:CLOCK_REALTIME@v6.18.46 -/
theorem clock_gettime_probe_names_realtime :
    (probe_args 113).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `futex(uaddr, op, val, …)`: `FUTEX_WAKE | FUTEX_PRIVATE_FLAG`, 129, at
address 0 — a wake of nobody, which answers 0 with no wait.  The
check-blind row: a wake at `AT_FDCWD` would still answer, with `-EFAULT`.
kernel: kernel/futex/syscalls.c:do_futex; include/uapi/linux/futex.h:FUTEX_WAKE,FUTEX_PRIVATE_FLAG@v6.18.46 -/
theorem futex_probe_wakes_privately_at_zero :
    (probe_args 98).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 129
      ∧ (probe_args 98).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `prctl(option, arg2, …)`: `PR_CAPBSET_READ` of capability 0; the Lean
`spec_table` carries no arm for 167 yet.
kernel: kernel/sys.c:prctl; include/uapi/linux/prctl.h:PR_CAPBSET_READ@v6.18.46 -/
theorem prctl_probe_reads_capability_zero_of_the_bounding_set :
    (probe_args 167).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 23
      ∧ (probe_args 167).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `clone(flags, newsp, …)`: `SIGCHLD` alone in the flag word, the one
shape the legacy arm admits.
kernel: kernel/fork.c:clone; include/uapi/asm-generic/signal.h:SIGCHLD@v6.18.46 -/
theorem clone_probe_carries_sigchld_in_a0 :
    (probe_args 220).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 17
      ∧ (probe_args 220).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `wait4(upid, stat_addr, options, ru)`: `-1` as `kernel_wait4` sees it,
the low 32 bits of a sign-extended `-1`, and `WNOHANG` — the one pair of
words the arm answers; every other `upid` or option word declines.  The
answer is the `-ECHILD` `__do_wait` seeds and returns to a caller with no
children, with or without `WNOHANG`: the flag decides only whether a
caller WITH children blocks, so it is the arm's choice, not the errno's.
kernel: kernel/exit.c:kernel_wait4,__do_wait; include/uapi/linux/wait.h:WNOHANG@v6.18.46 -/
theorem wait4_probe_asks_any_child_without_hanging :
    (probe_args 260).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 4294967295
      ∧ (probe_args 260).getD 2 (Z_to_bv 64 0) = Z_to_bv 64 1
      ∧ (probe_args 260).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `sigaltstack(uss, uoss)`: two NULLs, which read nothing and write
nothing.  The row exists so that the default's `AT_FDCWD` is NOT handed as
`uss` — that address is a `stack_t` the arm declines — so its whole point
is the zero in `a0`.
kernel: kernel/signal.c:sigaltstack,do_sigaltstack@v6.18.46 -/
theorem sigaltstack_probe_passes_two_nulls :
    (probe_args 132).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 0
      ∧ (probe_args 132).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `ppoll(ufds, nfds, tsp, sigmask, sigsetsize)`: no fds and a non-NULL
`tsp` — with `nfds = 0` and a NULL timeout `do_sys_poll` would never
return, so the timeout pointer is the strongest kernel claim in the table
and the register it sits in is the pin.
kernel: fs/select.c:ppoll,do_sys_poll@v6.18.46 -/
theorem ppoll_probe_passes_a_timeout :
    (probe_args 73).getD 2 (Z_to_bv 64 0) = Z_to_bv 64 (-100)
      ∧ (probe_args 73).getD 1 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `ppoll`'s `ufds` is NULL: the Lean `ppoll_core` declines `nfds = 0`
with a `ufds` above `TASK_SIZE`, where Linux answers -EFAULT through
`access_ok` in `do_sys_poll` (bugs/ppoll-nfds-zero-answers-a-kernel-space-ufds.md),
and NULL passes `__access_ok` at size 0, so the probe is answered.
kernel: fs/select.c:do_sys_poll; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem ppoll_probe_passes_a_null_ufds :
    (probe_args 73).getD 0 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

/-- `tgkill(tgid, tid, sig)`: both ids are the probe's own tid, and the
model the probe runs against records that tid.  `tgkill` refuses a
non-positive `tgid` or `pid` with `-EINVAL` before anything else, and the
arm's `pid_positive` gate mirrors that test; past it the two registers are
not alike in the arm: a positive `tid` (`a1`) the model does not hold
DECLINES, which the check catches, while a positive group id (`a0`) other
than the tid answers the `-ESRCH` `do_send_specific` leaves seeded, and a
non-positive value in either register answers `-EINVAL` — both answers the
check accepts.  So `a0`'s agreement with the model's tid is the pin, and
`a1`'s is stated beside it so the row reads as one.
kernel: kernel/signal.c:tgkill,do_send_specific@v6.18.46 -/
theorem tgkill_probe_names_its_own_thread_group :
    (probe_args 131).getD 0 (Z_to_bv 64 0) = probe_tid
      ∧ (probe_args 131).getD 1 (Z_to_bv 64 0) = probe_tid
      ∧ m_tid (probe_model_for 131) = some probe_tid := by decide

/-- The tid is not zero: `tkill(0, sig)` is refused on the argument check
before any delivery, and the abort probes exist to measure the delivery.
Rocq's stated reason for the row is the default `AT_FDCWD`, negative and
refused by the same gate; zero is the other value that gate refuses, and
the one a fixture tid could plausibly take.
kernel: kernel/signal.c:tkill@v6.18.46 -/
theorem the_probe_tid_is_nonzero : probe_tid ≠ Z_to_bv 64 0 := by decide

/-- The probe input hands the dispatcher the row, and the probe memory as
both views.
model: `probe_input`'s three fields against the fixtures they are built from; no kernel behaviour is claimed -/
theorem the_probe_carries_its_row_and_memory (n : Int) :
    (probe_input n).in_args = probe_args n
      ∧ (probe_input n).in_mem = probe_mem ∧ (probe_input n).in_wmem = probe_mem :=
  ⟨rfl, rfl, rfl⟩

/-! ## The probe model

One model for every number but two: `tkill` and `tgkill` answer only
under the task's declaration of the abort path and only for the caller's
own tid, so their probe runs against the model that declares it. -/

/-- The abort probe declares the abort path, at both numbers…
model: `probe_model_for`'s declaration flag at the two numbers it singles out; no kernel behaviour is claimed -/
theorem the_abort_probe_declares_the_abort_path :
    m_abort_terminal (probe_model_for 130) = true
      ∧ m_abort_terminal (probe_model_for 131) = true := by decide

/-- …and pins the tid the probe arguments target.
model: `probe_model_for`'s tid at `tkill`'s number, against the tid `probe_args` hands it; no kernel behaviour is claimed -/
theorem the_abort_probe_pins_the_tid :
    m_tid (probe_model_for 130) = some probe_tid
      ∧ (probe_args 130).getD 0 (Z_to_bv 64 0) = probe_tid := by decide

/-- Rejected: every other number's probe declares nothing and pins no tid,
so a probe of `exit` runs where a `tkill` would decline.
model: `probe_model_for` at a number it does not single out; no kernel behaviour is claimed -/
theorem the_plain_probe_declares_nothing :
    m_abort_terminal (probe_model_for 93) = false ∧ m_tid (probe_model_for 93) = none := by decide

/-- Rejected at the two neighbours: the exception is exactly the two
numbers, not a range around them.
model: `probe_model_for` at the numbers beside the two it singles out; no kernel behaviour is claimed -/
theorem the_abort_exception_is_exactly_two_numbers :
    m_abort_terminal (probe_model_for 129) = false
      ∧ m_abort_terminal (probe_model_for 132) = false := by decide

/-- `probe_answers_in` reads the probe's own model: at `tkill`'s number it
is the abort model that is handed to the witness, whatever table is asked.
model: `probe_answers_in` unfolded at 130 against `probe_model_abort`; no kernel behaviour is claimed -/
theorem probe_answers_in_reads_the_probes_model (t : List CheckedArm) :
    probe_answers_in t 130
      = (match table_witness t (probe_input 130) probe_model_abort with
         | Ok _ _ _ => true
         | Unmodeled => false) := rfl

/-! ## The probe's answer, read on the fixture tables

`probe_answers_in t n` is `true` exactly when the arms of `t` give the
probe of `n` an answer.  Run on the fixtures: the one-arm `exit` table,
whose arm answers every input; the declining arm under 93; a number the
table lacks; and the empty table, which is what `checked_table` is until
the first Track C ticket lands. -/

/-- Positive: the `exit` fixture answers its probe.
model: `table_witness` over the one-arm fixture table at 93, whose arm's witness answers on every input; no kernel behaviour is claimed -/
theorem the_exit_fixture_answers_its_probe : probe_answers_in [fixture_arm_exit] 93 = true := by
  decide

/-- Negative: a declining arm fails its probe — this is what turns the
check below into `false = true` for a table that carries one.
model: `table_witness` over the declining fixture arm at 93; no kernel behaviour is claimed -/
theorem a_declining_arm_fails_its_probe :
    probe_answers_in [fixture_arm_unmodeled_at_93] 93 = false := by decide

/-- Negative: a table answers no number it lacks, whatever it holds.
model: `table_witness` over the one-arm fixture table at 94, a number it lacks; no kernel behaviour is claimed -/
theorem a_number_off_the_table_fails_its_probe :
    probe_answers_in [fixture_arm_exit] 94 = false := by decide

/-- Negative: the empty table answers nothing, at any number.
model: `table_witness` over the empty table; no kernel behaviour is claimed -/
theorem the_empty_table_fails_every_probe (n : Int) : probe_answers_in [] n = false := rfl

/-- The tree's own table, without saying what it holds: at a number it has
no arm for, `probe_answers` is `false`.  Stated over the lookup so that it
survives every Track C landing.
model: `probe_answers` at a number `checked_table` lacks; no kernel behaviour is claimed -/
theorem an_unchecked_number_fails_its_probe (n : Int)
    (h : lookup_ca checked_table (bv_unsigned (probe_input n).in_sysno) = none) :
    probe_answers n = false := by
  simp only [probe_answers, probe_answers_in, table_witness, h]

/-! ## THE CHECK, shown able to fail

`checked_sysnos_probes_answer` is `decide` over `checked_table`, and over
the empty table that is `decide` over `[]`.  What the check is FOR is a
checked arm that declines its probe; the fixtures show it failing one,
alone and behind an answering arm, and passing the table whose arms all
answer. -/

/-- Positive: the check passes a table whose every arm answers.
model: the answering check over the one-arm fixture table; no kernel behaviour is claimed -/
theorem the_check_passes_the_exit_fixture :
    ([fixture_arm_exit].map ca_no).all (probe_answers_in [fixture_arm_exit]) = true := by decide

/-- Negative: THE CASE THE CHECK EXISTS FOR — an arm that declines its
probe fails it.
model: the answering check over the declining fixture arm; no kernel behaviour is claimed -/
theorem the_check_fails_a_declining_arm :
    ([fixture_arm_unmodeled_at_93].map ca_no).all
      (probe_answers_in [fixture_arm_unmodeled_at_93]) = false := by decide

/-- Negative: the check is `all`, not a check on the head — a declining
arm BEHIND an answering one is still caught.
model: the answering check over a two-arm fixture table whose second arm declines; no kernel behaviour is claimed -/
theorem the_check_fails_a_declining_arm_behind_an_answering_one :
    ([fixture_arm_exit, fixture_arm_unmodeled_at_94].map ca_no).all
      (probe_answers_in [fixture_arm_exit, fixture_arm_unmodeled_at_94]) = false := by decide

/-- Negative: …and AHEAD of one — the check is not a check on the last arm
either.
model: the answering check over the two-arm fixture table transposed; no kernel behaviour is claimed -/
theorem the_check_fails_a_declining_arm_ahead_of_an_answering_one :
    ([fixture_arm_unmodeled_at_94, fixture_arm_exit].map ca_no).all
      (probe_answers_in [fixture_arm_unmodeled_at_94, fixture_arm_exit]) = false := by decide

/-- WHAT THE RESTATEMENT COSTS AND WHY IT WAS MADE, pinned rather than
said.  Over the empty table the Lean check is vacuous — `all` over no
number is `true` — and Rocq's statement, `all` over every listed number,
is false: the empty table answers none of them.  Both are stated over the
explicit `[]`, so neither turns on which arms `checked_table` holds today.
model: the two `all`s over the empty table; no kernel behaviour is claimed -/
theorem the_check_is_vacuous_over_the_empty_table :
    (([] : List CheckedArm).map ca_no).all (probe_answers_in []) = true := by decide

/-- …and Rocq's statement over the same table is false: the empty table
answers none of the listed numbers, which is why the Lean check could not
be stated Rocq's way.
model: Rocq's `all` over `modeled_sysnos`, evaluated against the empty table; no kernel behaviour is claimed -/
theorem rocqs_statement_fails_over_the_empty_table :
    modeled_sysnos.all (probe_answers_in []) = false := by decide

/-! WHAT HOLDS THE CHECK'S OWN STATEMENT.  Over the empty table every
closed `Bool` equation that holds reduces to `true = true`, so a check
restated over `[]`, over `modeled_sysnos`, through `any` or through a
constant predicate is definitionally the same theorem to everything that
consumes it — `sysnos_dispatched_over` included — until a table is
registered on which the two differ, and for the `[]` and constant
restatements not even then, since both sides still evaluate to `true`.
No theorem in this file can tell them apart; the printed statement can,
so the guard below holds it, the way `Checks/Cases/Checks/Sys/Table.lean`
holds the two table guards' statements. -/

/-- info: LinuxProcessSemantics.LinuxProcessSem.Checks.DispatchSurface.checked_sysnos_probes_answer :
  (List.map ca_no checked_table).all probe_answers = true -/
#guard_msgs in
#check checked_sysnos_probes_answer

/-! ## The register's range -/

/-- Positive: `clone3`'s number fits the register.
kernel: include/uapi/asm-generic/unistd.h:__NR_clone3@v6.18.46 -/
theorem clone3_fits_a_register : sysno_in_range 435 = true := by decide

/-- Positive at both ends: 0, `__NR_io_setup`, and the last value the
register holds are in range — a bound moved inward by one fails here.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_setup@v6.18.46 -/
theorem the_register_ends_are_in_range :
    sysno_in_range 0 = true ∧ sysno_in_range (2 ^ 64 - 1) = true := by decide

/-- Negative: a negative number does not, and neither does the first
number past the register.
model: `sysno_in_range` at the two bounds; no kernel behaviour is claimed -/
theorem the_bounds_are_out_of_range :
    sysno_in_range (-1) = false ∧ sysno_in_range (2 ^ 64) = false := by decide

/-- What the range buys: the probe of a listed number carries that number
through `Z_to_bv` and back.
kernel: include/uapi/asm-generic/unistd.h:__NR_exit@v6.18.46 -/
theorem the_exit_probe_carries_its_number : bv_unsigned (probe_input 93).in_sysno = 93 :=
  probe_input_sysno 93 (by decide)

/-! ## Direction 1: outside the list, the decline

`syscall_spec_declines_outside` needs no table hypothesis.  Pinned at 0,
`__NR_io_setup`, which no table carries; that at a listed number the
dispatcher REFUSES the decline is `Checks/Cases/Checks/Progress.lean`'s
`the_dispatcher_refuses_the_decline_at_exit`, so the pin here is that the
theorem's premise fails there and it says nothing. -/

/-- THE PIN: at `__NR_io_setup` the dispatcher admits the decline.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_setup@v6.18.46 -/
theorem io_setup_probe_unmodeled (m : Model) :
    syscall_spec (SyscallInput.mkInput 0 [] (fun _ => none) (fun _ => none)) m Unmodeled :=
  syscall_spec_declines_outside _ m (by decide)

/-- Rejected: at `exit`'s number the premise fails — the number is listed
— so the theorem admits no decline there.
model: the register's membership at `exit_input`'s number; that the dispatcher answers there is `the_dispatcher_refuses_the_decline_at_exit`'s reading -/
theorem the_premise_fails_at_exit : bv_unsigned exit_input.in_sysno ∈ modeled_sysnos := by decide

/-! ## Direction 2, run on a fixture

`sysnos_dispatched_over` takes a table the dispatcher vouches for and the
answering check over it.  The `exit` fixture satisfies both
(`arms_agree_admits_the_exit_fixture`, `the_check_passes_the_exit_fixture`)
and the theorem produces `exit`'s answer at 93; the declining arm under 93
satisfies neither (`arms_agree_refuses_a_wrong_spec`,
`the_check_fails_a_declining_arm`), and its witness is the decline the
conclusion refuses. -/

/-- THE PIN: over the `exit` fixture, 93 is dispatched to an answer.
kernel: include/uapi/asm-generic/unistd.h:__NR_exit; kernel/exit.c:exit@v6.18.46 -/
theorem the_exit_fixture_dispatches_its_number :
    ∃ i m eff m' evs, bv_unsigned i.in_sysno = 93 ∧ syscall_spec i m (Ok eff m' evs) := by
  obtain ⟨i, m, o, hn, hspec, ho⟩ :=
    sysnos_dispatched_over [fixture_arm_exit] arms_agree_admits_the_exit_fixture
      the_check_passes_the_exit_fixture 93 fixture_arm_exit rfl
  cases o with
  | Ok eff m' evs => exact ⟨i, m, eff, m', evs, hn, hspec⟩
  | Unmodeled => exact absurd rfl ho

/-- Rejected: the declining arm's witness at its probe is the decline,
which is the outcome the conclusion excludes.
model: `table_witness` over the declining fixture arm at its own probe; no kernel behaviour is claimed -/
theorem the_declining_arm_witnesses_the_decline :
    table_witness [fixture_arm_unmodeled_at_93] (probe_input 93) (probe_model_for 93)
      = Unmodeled := rfl

/-- The backward half needs no hypothesis: from `exit`'s answer on
`exit_input`, the number is listed.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem an_answer_lists_its_number (m : Model) : bv_unsigned exit_input.in_sysno ∈ modeled_sysnos :=
  modeled_sysnos_of_dispatched _
    ⟨exit_input, m, _, rfl, exit_dispatch_admits exit_input m (Or.inl rfl), fun h => by cases h⟩


/-! ## `unlinkat` through the dispatcher

`__NR_unlinkat` is 35 (include/uapi/asm-generic/unistd.h:107, Linux v6.18.46).
`SYSCALL_DEFINE3(unlinkat, int, dfd, const char __user *, pathname, int,
flag)` (fs/namei.c:4775, Linux v6.18.46) takes `dfd` and `flag` as `int`, narrowed by
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88, Linux v6.18.46)
through `__SC_CAST` (include/linux/syscalls.h:132, Linux v6.18.46) — so a0 = 2^32 - 100 is
AT_FDCWD to `path_init` (:2590), and a2 = 2^32 is a flag word of 0.  These
are the routing pins of `Checks/Cases/Fs/Namei.lean`, moved here so that
module imports the twin and not `Specs`: each rewrites with the generated
`Checks.Cases.SyscallTable.syscall_at_35` and reads the arm's spec through
`unlinkat_arm`, whose unfolding is registered `local` for these pins. -/

section UnlinkatRouting

open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

attribute [local sys_simp low] LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.Namei.unlinkat_arm.eq_1

/-- Syscall 35 with a0 = AT_FDCWD, a1 the pathname and a2 = 0 reaches the
removal arm.
kernel: include/uapi/asm-generic/unistd.h:__NR_unlinkat; fs/namei.c:unlinkat,path_init,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem unlinkat_is_routed_at_35 (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] (name_at [97]) (fun _ => none))
        unlink_model o
      ↔ (env_failure o 2 unlink_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model []) := by
  rw [Checks.Cases.SyscallTable.syscall_at_35]
  sys_norm

/-- a0 = 2^32 - 100 IS AT_FDCWD once `int dfd` drops the high half.
kernel: include/uapi/asm-generic/unistd.h:__NR_unlinkat; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:unlinkat,path_init,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem unlinkat_dirfd_2_pow_32_minus_100_is_at_fdcwd (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 35 [4294967196, 8192, 0, 0, 0, 0] (name_at [97]) (fun _ => none))
        unlink_model o
      ↔ (env_failure o 2 unlink_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model []) := by
  rw [Checks.Cases.SyscallTable.syscall_at_35]
  sys_norm

/-- a2 = 2^32 is a flag word of 0 to `int flag`: the removal, not -EINVAL.
kernel: include/uapi/asm-generic/unistd.h:__NR_unlinkat; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:unlinkat,path_init,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem unlinkat_flag_truncates_through_the_dispatcher (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 4294967296, 0, 0, 0] (name_at [97]) (fun _ => none))
        unlink_model o
      ↔ (env_failure o 2 unlink_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model []) := by
  rw [Checks.Cases.SyscallTable.syscall_at_35]
  sys_norm

/-- …and a model reading the whole register would answer -EINVAL there.
no-row: the corpus holds no row of this exact call, a flag word wider than 32 bits
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem unlinkat_flag_2_pow_32_einval_rejected_through_the_dispatcher (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 4294967296, 0, 0, 0] (name_at [97]) (fun _ => none))
        unlink_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  rw [Checks.Cases.SyscallTable.syscall_at_35]
  sys_refute

/-- a2 = 2^32 + AT_REMOVEDIR is AT_REMOVEDIR: rmdir of a file, -ENOTDIR.
no-row: the corpus holds no row of this exact call, a flag word wider than 32 bits
kernel: include/uapi/asm-generic/unistd.h:__NR_unlinkat; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:unlinkat,path_init,do_rmdir,may_delete@v6.18.46 -/
theorem unlinkat_flag_2_pow_32_plus_removedir_through_the_dispatcher (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 4294967808, 0, 0, 0] (name_at [97]) (fun _ => none))
        unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 2) unlink_model [] := by
  rw [Checks.Cases.SyscallTable.syscall_at_35]
  sys_norm

/-- The pathname is a1: with a1 pointing at "." the call is typed LAST_DOT.
no-row: the corpus holds no row of this exact call, with its dirfd and flag arguments
kernel: include/uapi/asm-generic/unistd.h:__NR_unlinkat; fs/namei.c:unlinkat,path_init,link_path_walk,do_unlinkat@v6.18.46 -/
theorem unlinkat_pathname_is_a1 (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] (name_at [46]) (fun _ => none))
        unlink_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 2) unlink_model [] := by
  rw [Checks.Cases.SyscallTable.syscall_at_35]
  sys_norm

end UnlinkatRouting

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.DispatchSurface
