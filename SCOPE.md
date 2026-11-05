# Scope, assumptions and known gaps

Read this document before you use a proof as evidence about a real program.
It tells you which system the model describes, where the model is narrower
than that system, which assumptions it does not check, where it is less
precise, and where a run under QEMU user mode is not a Linux run. It also
records known gaps from the namespace work in a separate Lean translation.
The design priorities in [README.md](README.md#design-priorities) refer to
this document.

## Supported systems

- Stable Linux v6.18.46 (commit `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`),
  on riscv64.
- For instructions: the RISC-V specification (RV64GC).

Bugs in Linux do not count. The model describes one system, so no rule of
it chooses between two systems' answers, and a source and a target cannot
answer the same call as if they ran on different machines.

Other stable kernels (v4.17 and later) are a goal. They are not supported
now. The model does not check claims about them.

Each configuration choice that the model fixes is an assumption about the
Linux system. "Assumptions that the model does not check" below lists
them; `CONFIG_EVENTFD=y` is one, and `eventfd2` therefore answers
`-EINVAL` for a refused flag word and never `-ENOSYS`.

## Known Lean translation gaps from namespace work

The Lean translation of this Rocq model is maintained separately; its
source is not included in this repository.

- The namespace layer's Lean translation is pending.
- Mount propagation, including the open-parent path guards and the
  user-namespace ENOSPC-before-chroot checks, is pending too. Its pending
  outside-entry translation includes the mount-namespace anonymous/origin
  fields and builders, the entered-namespace and superblock-group closures,
  clone inheritance, the five closed-launch fast paths, path printing, the
  root-stack walk's fuel of one more than the mount count
  (`Ns.Walk.ns_top_open`), the mount-flag test (`Ns.Propagation.flags_open`)
  and its declines, the `pivot_root` decline in an open namespace, and the
  corresponding cases. Agreement of these additions has not been checked.
- Children's pid namespaces, allocation states, cursor/limit launch facts and their checks have not yet been translated.
- Partial pid-allocation rollback and its failure-state checks are pending too.
- The namespace clone mask, SIGCHLD check, core-gate lemma and regression cases have not yet been translated.

The bullets record pending translation work, not Lean code or evidence that
the two models agree.

## Where QEMU user mode differs

QEMU user mode for riscv64 is **not** a supported system. The list below
names each place where the model's answer and QEMU user mode's answer
differ, with the file and the function on each side. A run under
`qemu-riscv64` gives a trace that a Linux launch also gives when the run
depends on none of them. A `qemu-riscv64` counterexample that depends on
one of them is not a Linux run.

Each entry reads: what the model answers (Linux's), then what QEMU user
mode answers. QEMU citations are QEMU 10.0.11.

### The machine

- **The LR/SC reservation across a system call.** `ecall` clears the
  reservation (`Run.advance_past_svc`), so `lr; ecall; sc` fails the `sc`.
  Linux clears it on each return to user mode: `ret_from_exception`
  (`arch/riscv/kernel/entry.S`) ends with `REG_SC x0, a2, PT_EPC(sp)`, and
  the unprivileged specification makes an `sc` fail when another `sc`
  stands between the `lr` and it. QEMU user mode keeps the reservation:
  `cpu_loop` (`linux-user/riscv/cpu_loop.c`) never writes `env->load_res`,
  and the one place that clears it on a mode change,
  `riscv_cpu_set_mode` (`target/riscv/cpu_helper.c`), is built out under
  `CONFIG_USER_ONLY`. So the same `sc` can succeed under qemu-user.
- **A failing store-conditional.** A `sc.w` or `sc.d` that fails still
  passes the alignment check and the memory permission check
  (`Riscv/Sem.v`, the `Sc` arm). The unprivileged specification requires
  the permission check ("No SC.W instruction shall retire unless it passes
  memory permission checks"), the privileged specification (11.1.3.1)
  makes it a store's, and Sail checks for a write. QEMU user mode before
  commit `d107b748072c` ("target/riscv: Generate access fault if sc
  comparison fails", 2026-04-29) skips both checks on a failing `sc` and
  retires it with rd = 1. That is a QEMU bug, and 10.0.11 carries the fix.
- **Which store breaks a reservation.** The model compares the access base
  address (`Riscv/Sem.v`, `inval_resv`). QEMU user mode compares the
  value: `gen_sc` (`target/riscv/insn_trans/trans_rva.c.inc`) emits a
  `cmpxchg` of `load_val`. So a same-address same-value rewrite (ABA), or
  a partly overlapping store, fails the `sc` in the model and can leave
  it succeeding under qemu-user.

### The start state and the address space

- **The entry block.** The model lays Linux's block, from the entry
  stack pointer up to the stack VMA's end, with an auxiliary vector of
  27 entries, or 29 with `CONFIG_RSEQ`
  (`StackLayout.build_stack_bytes`, `StackLayout.auxv_entries`). QEMU
  user mode builds another one (`create_elf_tables`, `setup_arg_pages`
  and `load_elf_binary` in `linux-user/elfload.c`): 18 auxv entries in
  another order, with `AT_SYSINFO_EHDR` last and pointing at QEMU's own
  vDSO (`load_elf_vdso`), no cache entries, no `AT_MINSIGSTKSZ` and no
  rseq entries; no `arch_align_stack` pad; and a stack top where
  `target_mmap(0, ...)` puts an 8 MiB mapping, not `STACK_TOP` less a
  draw. Only the order of the strings and the `AT_RANDOM` block is the
  same. So the model admits no QEMU start state at all, and this
  difference reaches any program whose output or control flow depends
  on an entry address or on an auxv entry beyond those musl reads by
  type.

- **Where a new mapping goes.** The model gives the address Linux
  v6.18.46 gives: the hint if the hint is free, else the highest free
  range below `mm->mmap_base`, else the lowest free range from
  `TASK_UNMAPPED_BASE` up (`mm/mmap.c`, `__get_unmapped_area` and
  `generic_get_unmapped_area_topdown`; `mm/vma.c`, `unmapped_area_topdown`
  and `unmapped_area`; the model is `Sys/Mm/Mmap.v`, `linux_place`). Each
  of the three is bounded above by `State.alloc_top`, which is not one of
  Linux's bounds; "Known gaps in precision" gives the difference as R-a,
  R-b and R-c. QEMU
  user mode instead searches the host process's own free space
  (`linux-user/mmap.c`, `mmap_find_vma`), so a qemu-user run gives a Linux
  address only by chance.
- **The entry stack pointer.** `Run.valid_sp` requires a pointer in the
  top 2 GiB of the Sv48 user address space. Linux puts it there for each
  stack limit, with address randomisation on or off
  (`randomize_stack_top` in `mm/util.c`, `setup_arg_pages` in
  `fs/exec.c`). QEMU user mode puts the guest stack where the host kernel
  maps it (`setup_arg_pages` in `linux-user/elfload.c`). On an x86_64
  host it gives these entry stack pointers:

  - 8 MiB stack limit, address randomisation off: in the window.
  - 8 MiB stack limit, address randomisation on: below the window.
  - 1 GiB stack limit: below the window.
  - Unlimited stack limit: below the window.

  The statements say nothing about a launch that puts the pointer below
  the window.
- **The vDSO pair.** Linux installs a vDSO and a vvar mapping at
  `execve`. QEMU user mode maps only a vDSO, as an ordinary mapping
  (`load_elf_vdso`, `linux-user/elfload.c`). The `munmap` assumption
  below says what the model answers for a range that meets either.

### System calls

- **`set_robust_list`.** The model answers Linux's: 0 for a length of 24
  and `-EINVAL` otherwise (`SYSCALL_DEFINE2(set_robust_list)`,
  `kernel/futex/syscalls.c`). QEMU user mode answers `-ENOSYS` for every
  length and pointer (`TARGET_NR_set_robust_list` in `do_syscall1`,
  `linux-user/syscall.c`), so that guest userspace falls back to a
  non-robust futex. The model admitted both answers at each call until
  this revision.
- **`mmap` with a misaligned offset.** The model answers `-EINVAL` for
  every length: `riscv_sys_mmap` (`arch/riscv/kernel/sys_riscv.c`) tests
  the offset before `ksys_mmap_pgoff` reads the length. QEMU user mode
  rounds and tests the length first, so for a length within a page of
  2^64 it answers `-ENOMEM` (`target_mmap`, `linux-user/mmap.c`).
- **`mmap` with a closed fd and no `MAP_ANONYMOUS`.** The model answers
  `-EBADF`: `ksys_mmap_pgoff` (`mm/mmap.c`) runs `fget` before `do_mmap`.
  QEMU user mode never resolves the fd; `target_mmap`
  (`linux-user/mmap.c`) validates the request itself, so a zero length, a
  length within a page of 2^64, an invalid `MAP_TYPE`, an unknown prot bit
  and `MAP_FIXED` at an unaligned address each get QEMU's own `-EINVAL` or
  `-ENOMEM` before any host call.
- **`clock_getres` with a NULL `tp`.** The model answers 0 and writes
  nothing, whatever is mapped at address 0: `SYSCALL_DEFINE2(clock_getres)`
  (`kernel/time/posix-timers.c`) skips the copy under `if (!error && tp
  && put_timespec64(...))`. QEMU user mode attempts the copy and discards
  its result (`TARGET_NR_clock_getres` in `do_syscall1`,
  `linux-user/syscall.c`, whose `host_to_target_timespec` does not test
  for NULL), so under qemu-user the call can write 16 bytes at address 0.
- **`mremap(MREMAP_MAYMOVE)`: a misaligned `old`, a `new_size` that rounds
  to 0, an equal size, a shrink.** The model answers Linux's `-EINVAL`,
  `ret_only old` and in-place shrink (`mm/mremap.c`,
  `check_mremap_params` and `mremap_at`). QEMU user mode reserves a fresh
  range with `mmap_find_vma` before the host `mremap` (`target_mremap`,
  `linux-user/mmap.c`), so it gives `-ENOMEM` before `-EINVAL` and
  relocates the equal and the shrink call.
- **`ioctl` with a request outside the modeled set.** The model resolves
  the fd first: `-EBADF` on a closed fd, `-ENOTTY` for a tty-only request
  on a file, a socket, a pipe or `/dev/null`
  (`SYSCALL_DEFINE3(ioctl)` and `vfs_ioctl`, `fs/ioctl.c`). QEMU user mode
  answers before the fd: `do_ioctl` (`linux-user/syscall.c`) returns
  `-TARGET_ENOTTY` for a request it does not know and `-TARGET_EFAULT`
  from `lock_user` for an `IOC_W` or `IOC_RW` request.
- **`readv` and `writev`: a closed fd, an fd of the wrong mode, a raw
  `iovcnt` over `IOV_MAX` whose low 32 bits are in range.** The model
  answers Linux's `-EBADF`, and the truncated transfer for the wide count:
  Linux validates the `unsigned int` count and resolves the fd before it
  imports the vector (`fs/read_write.c`, `do_readv` and `do_writev`).
  QEMU user mode validates the raw 64-bit count and locks the vector in
  `lock_iovec` (`linux-user/syscall.c`) before the fd, so it answers
  `-EINVAL` or `-EFAULT` there.
- **`writev` to a regular file from a source that is readable at the
  start and not throughout.** The model answers the short write of the
  gathered prefix. QEMU user mode cuts at the faulting descriptor in
  `lock_iovec` (`linux-user/syscall.c`).
- **`sendto` and `sendmsg` with a buffer that `access_ok` passes and the
  memory does not back.** The model follows Linux: the fd resolves, and
  the copy faults inside `tcp_sendmsg_locked` (`net/ipv4/tcp.c`) or
  `sk_stream_wait_connect` (`net/core/stream.c`) answers `-EPIPE` without
  copying. QEMU user mode locks the whole buffer first and answers
  `-EFAULT` in both cases (`do_sendto`, `linux-user/syscall.c`).
- **`socket` and `socketpair` with a type word carrying an unknown flag
  bit.** The model answers Linux's `-EINVAL`
  (`__sys_socket_create`, `net/socket.c`). QEMU user mode drops the
  unknown bits in `target_to_host_sock_type` (`linux-user/syscall.c`), so
  the call can succeed.
- **`eventfd2` with a refused flag word.** The model answers `-EINVAL`
  (`SYSCALL_DEFINE2(eventfd2)`, `fs/eventfd.c`). A qemu-user host whose
  target is sparc64, mips or parisc accepts some of those words, because
  its `TARGET_O_NONBLOCK` and `TARGET_O_CLOEXEC` differ
  (`linux-user/syscall_defs.h`).
- **`epoll_pwait` with a closed `epfd` beside a `maxevents` outside
  `1..EP_MAX_EVENTS`, or an events buffer that `access_ok` refuses.** The
  model answers `-EBADF`: v6.18.46 resolves the fd first
  (`do_epoll_wait`, `fs/eventpoll.c`). QEMU user mode checks the count and
  locks the buffer first (`TARGET_NR_epoll_pwait`,
  `linux-user/syscall.c`).
- **`accept4` with a closed fd beside unknown flags or a non-NULL
  address.** The model answers `-EBADF`: `__sys_accept4` (`net/socket.c`)
  resolves the fd before the flags. QEMU user mode checks the flags and
  validates the address length first (`do_accept4`,
  `linux-user/syscall.c`).
- **Transfers: `read`, `write`, `pread64`, `pwrite64`.** The model
  answers in Linux's order. QEMU user mode locks the whole buffer before
  the host call (`lock_user`, `linux-user/uaccess.c`), so a buffer that is
  readable in part gives a different answer.

The entries above are the ones the model and QEMU user mode are known to
differ on. The list is maintained by hand; no tool checks that it is
complete. A replay of 4,291 recorded traces (`reports/corpus-replay.md`)
through extracted checkers found twelve system calls where the model
answers and an older tree declines; each of the twelve was read against
v6.18.46 and the model answers Linux's at every one.

This sentence used to add "(19,693 judged system calls)". **That figure is
withdrawn as unmeasured**: no report in `reports/` produces it, and no run
behind it could be found. The judged-record counts that DO carry a run are
in `reports/evidence-checked-entry.md`: the corpus holds 23,984 syscall
records, of which 19,070 reach the boundary, because `--replay` stops a
trace at its first unreproduced verdict and the records after one are never
judged. The trace count, 4,291, is measured two ways in
`reports/evidence-corpus-replay-features.md`.

## Where older Linux versions differ

Some shapes are contested for a reason that is not QEMU user mode. The
model answers v6.18.46's, and an older stable kernel answers otherwise.
A proof says nothing about those kernels; "Supported systems" above
already says so. These are the known cases.

- **`flock` with `LOCK_MAND`, or with an unrecognised operation, on a
  closed fd.** The model answers 0 for `LOCK_MAND` and `-EINVAL` for an
  unrecognised operation, both before the fd lookup
  (`SYSCALL_DEFINE2(flock)`, `fs/locks.c`: the `LOCK_MAND` test and
  `flock_translate_cmd` precede `CLASS(fd, f)(fd)`). Kernels v4.17 to
  v5.19 resolve the fd first. QEMU user mode passes the call through to
  the host, so it answers what its host kernel answers; it is not a
  difference of its own.
- **`flock` granting a lock to the sole opener whose type does not match
  the fd mode.** The model answers 0. That holds while
  `f_op->flock` is NULL, which is the case for the file systems the
  model describes; an NFS mount supplies one and can answer otherwise.
  This is a file-system difference, not a system one.
- **`mremap(MREMAP_MAYMOVE)` whose rounded `new_len` passes
  `TASK_SIZE`.** The model answers `-EINVAL`: from v6.17
  `check_mremap_params` (`mm/mremap.c`) tests `new_len > TASK_SIZE`
  unconditionally. Up to v6.16 that test sat inside `mremap_to`, so a
  MAYMOVE grow reached `-ENOMEM` instead.
- **A `MAP_FIXED` `mmap` at a misaligned address.** The model answers
  v6.18.46's: `__get_unmapped_area` (`mm/mmap.c`) takes
  `mmap_end = arch_get_mmap_end(addr, len, flags)`, which on riscv64 is
  `STACK_TOP_MAX` for every address, so the only `-ENOMEM` before the
  alignment `-EINVAL` is `len > mmap_end - mmap_min_addr`. Two older
  riscv64 forms of that macro make `mmap_end` depend on the address, and
  then the same call answers `-ENOMEM` where v6.18.46 answers `-EINVAL`
  (`arch/riscv/include/asm/processor.h`):

  - up to v6.9, the three-way form added by `add2cc6b6515` ("RISC-V: mm:
    Restrict address space for sv39, sv48, sv57"): a nonzero address
    below `VA_USER_SV48` gives `mmap_end = VA_USER_SV39` = 2^38, so a
    misaligned fixed `mmap` of more than 2^38 less a page answers
    `-ENOMEM`. Commit `6be7ee4bebd1` ("riscv: Improve
    `arch_get_mmap_end()` macro", v6.9) rewrote that form without
    changing which address gives which end;
  - v6.9 to v6.11, the hint-as-ceiling form of `b5b4287accd7` ("riscv:
    mm: Use hint address in mmap if available"): a nonzero address with
    `addr + len` at or below 2^(VA_BITS-1) gives `mmap_end = addr + len`,
    so an address of 1 to 4095 answers `-ENOMEM`.

  Commit `2116988d5372` ("riscv: mm: Do not restrict mmap address based
  on hint", v6.11) made the macro unconditional, which is the form the
  model follows. The model's own band above `State.alloc_top` is a
  separate limit and is residual R-b below, not a version difference.
- **`socket` with a type at or above `SOCK_MAX` and a family of 44 or
  45, and AF_INET protocols 256 to 262.** `NPROTO` and `IPPROTO_MAX`
  grew across the stable series (`include/linux/socket.h`,
  `include/uapi/linux/in.h`), so an older kernel answers
  `-EAFNOSUPPORT` or `-EINVAL` where v6.18.46 does not.
- **The order of `accept4`'s flag check and `epoll_pwait`'s parameter
  checks against the fd lookup.** v6.18.46 resolves the fd first in both
  (`__sys_accept4`, `net/socket.c`; `do_epoll_wait`, `fs/eventpoll.c`),
  and older kernels do not. QEMU user mode also checks first, so these
  two are in the QEMU list above as well.
- **`eventfd2` with a refused flag word.** For a riscv64 guest QEMU user
  mode and Linux agree; the entry in the QEMU list above applies only to
  a sparc64, mips or parisc target, whose `TARGET_O_NONBLOCK` and
  `TARGET_O_CLOEXEC` differ.

## Where the model is narrower

The statements restrict these cases, or the model says `unmodeled` for
them. A proof says nothing about a program in such a case.

Every `setsockopt` answer in the table assumes the launch value
`in_cgroup_bpf_setsockopt` is false. With a present hook the call is
`unmodeled`, as the cgroup-BPF row explains.

| Area | Limit |
| --- | --- |
| Threads | The model has one thread. It has no scheduler and no shared-memory interleaving. For `fork`-like calls, the model describes the parent only. It does not run the child. `clone` answers two flag words: `SIGCHLD` alone, and `SIGCHLD` with one or more of `CLONE_NEWNS`, `CLONE_NEWUSER`, `CLONE_NEWPID`, `CLONE_NEWNET`, `CLONE_NEWIPC`, `CLONE_NEWUTS` and `CLONE_NEWCGROUP` and no other bit (`Kernel.Fork.clone_ns_flags_b`). For the second word too the model describes the parent only, by choice: the parent gets a child pid (and the model records that it has a child, and appends the pid to its list of unreaped children, `State.m_child_pids`, oldest first as `copy_process` keeps `task->children`, `kernel/fork.c`, v6.18.44; identical at v6.18.46) or an errno. With either word the parent gives up the offset of each inherited descriptor (`Kernel.Fork.forfeit_inherited`): after the clone only the child reads it. The fork word records the pid the same way (`State.with_child`). The child runs in the new namespaces, and this model says nothing about it. `wait4` answers one shape, `wait4(-1, status, WNOHANG, NULL)` (`Kernel.Exit.wait4_spec`): `-ECHILD` for a caller with no child, and for a caller with a recorded child the environment's choice of 0 or the pid of a recorded child, with an exit or killed status word stored at `status` unless it is NULL; the reaped pid leaves the list (`wait_task_zombie` and `release_task`, `kernel/exit.c`, v6.18.44; identical at v6.18.46). A returned pid passes the same positive, envelope and not-own-tid test as clone (`Kernel.Fork.clone_pid_ok_b`), even for a raw model. A caller with a recorded child is answered only if the process installed `SIG_DFL` for `SIGCHLD` with `SA_NOCLDWAIT` clear while it had no recorded child (`State.m_sigchld_dfl`, set by `Kernel.Signal.sigchld_dfl_install` only in a process with no recorded child, `Kernel.Signal.sigchld_install_model`; a clone child copies it, as `copy_sighand` copies the actions, `kernel/fork.c`, v6.18.46): the bit is set only if every child the process has was cloned while SIGCHLD was SIG_DFL. Without that install, or with an install made after a child was recorded, the call is `unmodeled`: the disposition the process started with is its launcher's and may be `SIG_IGN`, and Linux decides when a child exits, from the parent's disposition then, whether to reap that child itself (`do_notify_parent`, `kernel/signal.c:2241-2259`, v6.18.46), so a child cloned under `SIG_IGN` may be gone before a later install. A caller whose recorded children were all reaped is `unmodeled`. A caller with a recorded child also declines when a non-NULL `status` pointer is not four writable bytes, including the bare 0 outcome. Linux leaves the pointer untouched when only live children make the call return 0; it answers `-EFAULT` only if it reaps and the later status copy-out fails (`kernel_wait4`), losing the status. A childless caller still gets `-ECHILD` regardless of that pointer. |
| Capabilities | The model holds the inheritable capability set (`State.m_cap_inheritable`), seeded from `State.ProcInput.in_cap_inheritable`; every word is a launch value. It holds no effective or permitted set. A child copies the inheritable set with its credentials. On this branch no modeled call reads or writes the held set. `capget` answers a version-3 header with pid 0, or with a NULL data pointer (0, and the pid is not read). For a caller whose real, effective and saved uids are all non-zero it reports empty effective and permitted sets, and the inheritable set is the environment's choice within the valid bits. For a caller with a uid 0 the copy-out is `unmodeled`: its sets are the bounding set combined with the inheritable set, and the model does not know the bounding set beyond `CAP_SETUID` and `CAP_SETGID`. `capset` answers a version-3 header with pid 0 and six zero data words, from a caller whose three uids are all non-zero: 0 or `-ENOMEM`. For both calls a header, pid word or data range that `access_ok` refuses is `-EFAULT` (`kernel/capability.c`, v6.18.44). Every other shape of either call is `unmodeled`. |
| Signals | The model does not run signal handlers. It has three signals: `SIGABRT`, raised by `tkill`/`tgkill` on the abort path; `SIGPIPE`, raised by a write whose far end has no reader; and `SIGKILL`, raised by `kill` with the caller's own process id. The modeled SIGKILL is fatal for a non-init caller; pid 1 ignores its own signal and returns 0 unchanged, as the `kill` row describes. Each is behind a declaration of the launch, and with the declaration off the call that would raise it declines: `State.in_abort_terminal` for `SIGABRT`, `State.in_sigpipe_terminal` for `SIGPIPE` and `State.in_selfkill_terminal` for `SIGKILL`, all pinned off by `Run.valid_input`, so no run under the ordinary statements dies by a signal. With the declaration on (`Run.valid_input_abort`; `Run.valid_input_sigpipe_kills` and `Run.valid_input_channel_closed`), `SIGABRT` and `SIGPIPE` each end the run with a death that is not an exit (`State.KillEv`), or, where the launch mask blocks it, return the errno and leave the signal pending until a `rt_sigprocmask` uncovers it. `rt_sigaction` declines every install that would change either disposition, so no modeled call moves one. For `SIGABRT` the model assumes the launch left the disposition at `SIG_DFL`. For `SIGPIPE` it no longer assumes: the launch declares it (`State.in_sigpipe_default`), `Run.valid_input` pins the declaration to `SIG_DFL`, and `Run.valid_input_sigpipe_ignored` is the launch that ran `signal(SIGPIPE, SIG_IGN)` before `execve` — a launch `execve` preserves (`fs/exec.c`, `begin_new_exec`'s `flush_signal_handlers` with `force_default = 0`, Linux v6.18.46), under which the same write returns `-EPIPE` and the program runs on. No other signal is modeled: `SIGSEGV` is reported as the error transition rather than as a death, `SIGCHLD`'s default action is to ignore it, `SIGXFSZ` needs an `RLIMIT_FSIZE` the model does not carry, and nothing outside the process can send one. For `SIGCHLD`, `rt_sigaction` answers one install, `SIG_DFL` with `SA_NOCLDWAIT` clear: 0, and in a process with no recorded child the install is recorded in `State.m_sigchld_dfl`, which `wait4` reads before it answers a caller with a recorded child (`Signal.sigchld_dfl_install`, `Signal.sigchld_install_model`); in a process with a recorded child the install answers 0 and records nothing, so the bit is set only if every child the process has was cloned while SIGCHLD was SIG_DFL. It declines `SIG_IGN`, every handler, and `SIG_DFL` with `SA_NOCLDWAIT` set, under which Linux reaps an exiting child itself (`do_notify_parent`, `kernel/signal.c`, v6.18.44), so the recorded install is never contradicted and nothing clears it. `Kernel.Exit.wait4_spec` makes no assumption about the `SIGCHLD` disposition at launch; the multi-process core's own `wait4` arms in `Procs.v` still rest on the launch assumption "At launch SIGCHLD is not at SIG_IGN" below, until the fix tracked in #125 lands. |
| `kill` | With `State.in_selfkill_terminal` on, `kill` answers a call that names the caller's own process id (the value `getpid` returned). For `SIGKILL`, pid 1 ignores its own SI_USER signal and returns 0 with the model unchanged: sender and target are the same process and share a pid namespace, so `force` is false (`sig_task_ignored`, `kernel/signal.c:91-96`; `prepare_signal`, `:935`; `__send_signal_locked`, `:1048-1054`; `send_signal_locked`, `:1195-1214`, v6.18.46). Another positive own pid ends with death by signal 9 (`State.KillEv`; `complete_signal`, `:1003-1025`; `get_signal`, `:2875-2886`). A signal above 64 is `-EINVAL` before delivery, pid 1 included (`check_kill_permission`, `:805-806`). Pid `INT_MIN` is `-ESRCH` (`kill_something_info`, `:1589-1590`). Every other pid (another process, a process group, `-1`), signal 0, every other signal, an unpinned pid and a model mask with SIGKILL blocked are unmodeled. With the declaration off, every call is unmodeled. While another process lives, `kill` is answered as the other calls private to a process are. |
| `prctl` | The model answers seven options: `PR_CAPBSET_READ` (1 for `CAP_SETUID` and `CAP_SETGID`, 0 or 1 chosen at each call for every other capability, or `-EINVAL` past `CAP_LAST_CAP`; `security/commoncap.c`, `cap_task_prctl`, v6.18.44), `PR_SET_PDEATHSIG`, `PR_SET_DUMPABLE` and `PR_SET_NO_NEW_PRIVS` with Linux's 0 or `-EINVAL`, `PR_GET_PDEATHSIG`, `PR_GET_DUMPABLE` and `PR_GET_NO_NEW_PRIVS` (`SYSCALL_DEFINE5(prctl)`, `kernel/sys.c`, v6.18.44). The model holds the parent-death signal (`State.m_pdeath_signal`, 0 at launch): `PR_SET_PDEATHSIG` stores it, `PR_GET_PDEATHSIG` stores it as a 4-byte `int` at its pointer and answers 0 (`-EFAULT` with nothing stored for a range `access_ok` refuses, `unmodeled` for a range `access_ok` admits that memory does not wholly back), and `setuid`, `setgid`, `setresuid` and `setresgid` reset it to 0 when they move the effective id, as `commit_creds` does (`kernel/cred.c`, v6.18.44). `setgroups` and `capset` do not reset it. The model holds the no-new-privs bit (`State.m_no_new_privs`, false at launch): `PR_SET_NO_NEW_PRIVS` sets it, nothing clears it, `PR_GET_NO_NEW_PRIVS` answers 1 or 0, or `-EINVAL` for a nonzero `arg2` to `arg5`. The model holds the dumpable mode (`State.m_dumpable`, 1 at launch): `PR_SET_DUMPABLE` writes 0 or 1, the four id setters write the build's `fs.suid_dumpable` (`State.kb_suid_dumpable`) when they move the effective id, as `commit_creds` does, and `PR_GET_DUMPABLE` answers it, 2 included. A clone copies both (`copy_process`, `mm_init`, `kernel/fork.c`). Every other option is `unmodeled`. |
| Parent process | The model holds the current parent pid (`State.m_ppid`), seeded from `State.ProcInput.in_ppid`. A child starts with its parent's pid, the parent's key in the process table (`copy_process` sets `p->real_parent`, `kernel/fork.c`, v6.18.44). On this branch `getppid` does not read the held value: it answers any pid below 2^22, 0 included (a parent outside the caller's pid namespace), chosen afresh at each call. A statement that needs a particular parent takes it as a premise. The model also keeps two bits, false at launch and in a child, for what a later `getppid` may still show: `State.m_reparent_unseen` (since the last `getppid` answer a nonzero parent-death signal has replaced a 0, so the parent may have died unseen while it was 0) and `State.m_reparent_moved` (an answer moved the parent pid in the current reparent window); `State.with_pdeath_signal` and `State.with_ppid_answered` write them, a write of the parent-death signal already held changes neither, and on this branch no modeled call reads them. |
| Session id | `getsid` answers pid 0 and the caller's own tid once the model has pinned it (`SYSCALL_DEFINE1(getsid)`, `kernel/sys.c`, v6.18.44). After a successful `setsid` the answer is the tid. Before one it is any pid below 2^22, 0 included (a session led from an ancestor pid namespace), chosen afresh at each call: Linux answers one fixed number until the process's own `setsid`, and the model does not pin it. Every other pid, a negative one included, is `unmodeled`. |
| `setsid` in the namespace model | For a task outside the released world `setsid` answers the caller's pid in its own pid namespace, and `-EPERM` once a `setsid` of its process has succeeded (`ksys_setsid`, `kernel/sys.c:1268-1301`, v6.18.46). Linux also answers `-EPERM` when a live task's process group is the caller's pid. No modelled process makes such a group, because `setpgid` has no arm; a process outside the model can only when the caller is pid 1 of a pid namespace the model made and its modelled parent exits: the caller is then reparented to a reaper the environment owns, and that reaper may call `setpgid(caller, caller)` in the caller's session before the caller execs (`kernel/sys.c:1144-1150`). Another task of such a namespace whose parent exits goes to the namespace's pid 1 or to a child subreaper at its level (`find_new_reaper`, `kernel/exit.c:642-675`), a modelled process. The launch value `env_foreign_pgroups` names that event. **Its default `false` assumes that no environment reaper calls `setpgid` on the caller before the caller's `setsid`;** under it the answer in a pid namespace the model made is exactly the pid. A statement that wants that case names `env_foreign_pgroups := true`; under `true`, and in the host's pid namespace, where group membership is the environment's, `-EPERM` is admitted beside the success, as for the released `setsid`. The arm records the leader bit only; Linux also sets the session and group ids, which no call the namespace model answers reads. When `setpgid` is modelled, this row and `Ns.Task.setsid_arm` must read the group table. |
| Credentials read back | `getresuid` and `getresgid` store the real, effective and saved ids, 4 bytes each, through the three pointers in order, and answer 0 (`SYSCALL_DEFINE3(getresuid)`, `SYSCALL_DEFINE3(getresgid)`, `kernel/sys.c`, v6.18.44). A pointer whose 4-byte range `access_ok` refuses answers `-EFAULT` with the stores before it already made, as Linux leaves them. A range `access_ok` admits that memory does not wholly back is `unmodeled`, even after an earlier store: a store that straddles into an unmapped page can leave part of itself behind. |
| Supplementary groups | `setgroups` answers a privileged caller only for the empty list: 0 with the list cleared, or `-ENOMEM` (`SYSCALL_DEFINE2(setgroups)` and `set_current_groups`, `kernel/groups.c`, v6.18.44). A non-empty list, and a size Linux refuses with `-EINVAL`, are `unmodeled`. An unprivileged caller gets `-EPERM` for every argument. |
| `close_range` | With flags 0 the model closes every descriptor in the range, of any kind, and answers 0; an unknown flag bit or `fd > max_fd` is `-EINVAL` (`SYSCALL_DEFINE3(close_range)`, `fs/file.c`, v6.18.44). `CLOSE_RANGE_CLOEXEC` and `CLOSE_RANGE_UNSHARE` are `unmodeled`: the model records no close-on-exec bit. |
| `pipe2` | `pipe2` answers a flag word of 0 or `O_CLOEXEC` alike: the two lowest free descriptors, the read end first, written through `fildes` with one copy; or `-EMFILE`, `-ENFILE` or `-ENOMEM` with nothing installed; or `-EFAULT` when `access_ok` refuses the eight-byte destination range or when byte 0 of `fildes` is unwritable (`do_pipe2`, `__do_pipe_flags`, `create_pipe_files`, `fs/pipe.c`; `alloc_fd`, `fs/file.c`; v6.18.46). `O_CLOEXEC` sets only the two descriptors' close-on-exec bit, which the model does not record (see the `execve` row). A word with `O_NONBLOCK`, `O_DIRECT` or `O_NOTIFICATION_PIPE` is `unmodeled`, and a word with any other bit is `-EINVAL`. A destination that `access_ok` admits with byte 0 writable but not all eight bytes writable is `unmodeled`. |
| Address-space size | The system call specifications use Sv48. Thus you cannot prove the Sv39 and Sv57 statements for an image that can run. |
| Stack limit | The stack limit is 8 MiB. A larger or unlimited `RLIMIT_STACK`, which selects the legacy mmap layout, is outside the model. The model counts the whole entry block against this limit, from the stack VMA's end `StackLayout.ed_top` down, as Linux counts it. |
| Arguments | `Run.valid_input` requires that the arguments after `argv[0]` do not contain `/` and are not `..`. Thus a proof about `cp src dst` does not apply to `cp /tmp/src dst`. A statement that must cover path arguments uses the second launch predicate `Run.valid_input_paths`, named the way `Run.valid_input_abort` names the aborting launch: it is `Run.valid_input` with `Run.valid_argv_paths` in place of `Run.valid_argv`, which drops only that clause, and `Run.valid_input_paths_of_valid_input` shows it admits every ordinary launch. Both predicates also bound the lists (`Run.valid_argv` and `Run.valid_argv_paths`, `Run.valid_envp`): 1 to 1024 arguments and at most 2 MiB of argument bytes, at most 256 environment variables and at most 128 KiB of environment bytes, and at most 131071 bytes in each string. Each count of bytes includes the terminating NUL of each string. These are the model's own per-list bounds. Linux's own bound is joint, and `Run.valid_launch` carries it: the exec file name, the envp strings and the argv strings with their NULs, plus 8 bytes for each argv and envp pointer, are at most 2 MiB together at the 8 MiB stack limit (`bprm_stack_limits`, `fs/exec.c`). Linux answers `E2BIG` for a larger launch. `Run.valid_launch` also says which exec file names `execve` can present (`State.in_execfn`): a path of 1 to 4095 bytes without a NUL, or `/dev/fd/N`, or `/dev/fd/N/` and such a path that does not start with `/` (`getname_flags` in `fs/namei.c`, `alloc_bprm` in `fs/exec.c`). Both binaries of a pair run under the same exec file name, as they run on the same input. A launch outside these bounds is outside the model. |
| `execve` from the program | The model has no `execve` (221) or `execveat` (281) arm: a run stops at the call (`Run.syscall_spec_execve_unmodeled`, `Run.execve_boundary_stops`), and what the new image does is outside the model. A statement about a program that ends in an exec names the state at the call: `Run.execve_boundary` reads the path, argv and envp from the program's memory (`Run.cstr_at`, `Run.strv_at`), and the model at the call gives the credentials and the descriptor table. `Run.star_calls` is `Run.star` with a log of the system calls that returned on the way, in order (`Run.SysCall`: number, a0 to a5, return value, and the bytes it stored: its copy-outs and its zero-filled ranges), so a statement can say which calls came before the exec, what each answered and what each stored. A call that ends the process is not in the log; its event is in the trace. Three limits. First, a statement over the runs that reach the boundary says nothing about a program whose runs all stop earlier, at a declined call or a fault. Since the boundary is itself uncovered (`Run.unmodeled_at` holds there), `~ Run.reaches_unmodeled` cannot rule that out; such a statement must also show that every configuration a run reaches where the next step is the error transition (an uncovered call, a fault) is the boundary, or show that the boundary is reached. Second, the descriptor table at the call is not the new image's: the model records no close-on-exec bit, so a descriptor present at the call may be closed by the exec (`do_close_on_exec` in `begin_new_exec`, `fs/exec.c`); a claim that a descriptor is absent carries over to the new image, a claim that one is present does not. The exec can also change the credentials (a set-user-ID or set-group-ID file, file capabilities). Third, Linux returns from a failed exec and the program goes on; the model has no continuation, so nothing is said about that path. `execveat` has no boundary predicate. |
| Standard input and output | The fds 0, 1 and 2 are external channels, and their direction is fixed: 0 is read-only, 1 and 2 are write-only (`State.FdChannel`). The model answers `-EBADF` for the other direction. Thus a proof says nothing about a program that is handed a connected socket on fd 0, as an inetd-style server is. `setns` on one of them answers `-EINVAL`, and that answer rests on a second assumption of the model: fds 0, 1 and 2 are pipes, sockets or terminals. None of those is a namespace file or a pidfd, and Linux answers `-EINVAL` for every file that is neither (`SYSCALL_DEFINE2(setns)`, `kernel/nsproxy.c`, v6.18.46). The `-ESPIPE` of `lseek` and the `-EINVAL` of `fsync` on these fds rest on the same assumption. Thus a proof also says nothing about a program that is handed a namespace file or a pidfd on fd 0, 1 or 2. |
| Inherited descriptors | A launch may hand the process descriptors above 2 that its parent opened (`State.ProcInput.in_inherited_fds`): each is a descriptor number and the bytes of a regular file, open read-only at offset 0 (`State.OInherited`). `Run.valid_input` and every statement written before the field pin the list empty, so those statements say nothing about a launch with descriptors other than 0, 1 and 2. `Run.valid_input_inherited` admits numbers from 3 up to 2,147,483,583 (`sysctl_nr_open_max` less one, `fs/file.c`, v6.18.46), strictly increasing, each file at most `MAX_LFS_FILESIZE` bytes; `NsProcs.lholts_ns_within_budget` and `NsProcs.lholts_ns_after_clone` take it. On such a descriptor `read` answers Linux's bytes from the held offset and moves it; `close` and `close_range` remove it; `fcntl`'s `F_GETFD` and `F_SETFD` answer. A successful `clone` with either word (and `clone3` with the fork image) leaves the offset with the child: the parent keeps the descriptor, but the model no longer holds its offset, so on it the parent's `close`, `close_range`, `F_GETFD` and `F_SETFD` answer and `read` is `unmodeled`. A failed `clone` leaves the offset with the parent. `write` answers `-EBADF` and `setns` `-EINVAL` on either form: the description is read-only (`vfs_write`, `fs/read_write.c`), and a regular file is neither a namespace file nor a pidfd (`kernel/nsproxy.c`, v6.18.46). Every other call but `close`, `close_range`, `F_GETFD` and `F_SETFD`, and `read` while the model holds the offset, is `unmodeled`. The model does not count the description's references: no answer it gives for a read-only regular file depends on them. |
| Network | The list of connections is never empty. Thus the model does not include an environment where no peer ever connects. |
| AF_UNIX sequenced-packet pairs | `socketpair (AF_UNIX, SOCK_SEQPACKET, 0)`, with or without `SOCK_CLOEXEC`, stores the two lowest free descriptor numbers below `RLIMIT_NOFILE` and gives two connected ends (`State.FdSeqpacket`), or answers `-EMFILE` or `-ENOMEM` with nothing stored, `-EFAULT`, or `-ENFILE` or `-ENOMEM` with both numbers stored (`__sys_socketpair`, `net/socket.c`; `unix_create`, `unix_socketpair`, `net/unix/af_unix.c`; v6.18.46). A partly writable destination is `unmodeled`. With `SOCK_NONBLOCK`, or with protocol `PF_UNIX`, the call is `unmodeled`. The model sends no message on an end, so its receive queue is always empty. Without a cgroup-BPF setsockopt hook, `setsockopt` at `SOL_SOCKET` answers `SO_PASSCRED` and stores it, with `-EINVAL` for a length under 4 and `-EFAULT` for a value it cannot read (`sk_setsockopt`, `net/core/sock.c`); another option is `unmodeled`, and another level is `-EOPNOTSUPP`. A present hook makes the call `unmodeled`, as the next row states. `recvmsg` with flags 0, no address and one buffer answers 0 (end of file) once the other end is closed, and is `unmodeled` while the other end is open, because it would wait for a message no process of the run can send. A header or iovec it cannot read is `-EFAULT`, more than 1,024 iovecs `-EMSGSIZE`, and a negative buffer length `-EINVAL`; the ordered `msg_flags` and `msg_controllen` write-back stores can each fault, and a partly writable store is `unmodeled` (`copy_msghdr_from_user`, `____sys_recvmsg`, `net/socket.c`). `ftruncate` and `fsync` answer `-EINVAL`, and `getdents64` answers `-ENOTDIR`. The shared descriptor arms answer `close` and `close_range` with 0, `F_SETFD` with 0, `F_GETFD` with 0 or `FD_CLOEXEC`, and `setns` with `-EINVAL`; epoll with an end as `epfd` answers `-EINVAL`, subject to its earlier parameter and access checks. `dup3` onto an end replaces and closes it. `dup` of an end and `clone` with an end open are `unmodeled`. Other operations on an end are `unmodeled` unless an earlier kind-independent check answers. |
| Cgroup-BPF setsockopt | `State.ProcInput.in_cgroup_bpf_setsockopt` (field 25) names whether the launch has a cgroup-BPF setsockopt hook. The model retains it in `State.m_cgroup_bpf_setsockopt`, including across child creation. If true, every `setsockopt` call is `unmodeled`: the hook can rewrite the level, option name, length or bytes, or bypass the handler with success (`do_sock_setsockopt`, `net/socket.c:2342-2363`; `__cgroup_bpf_run_filter_setsockopt`, `kernel/bpf/cgroup.c`; v6.18.46). An errno-only choice would miss these effects. The ordinary input predicates and finite-input conversion pin the field false; the raw boundary requires an explicit value. `Checks.CgroupBpfEmbedding` embeds every old 24-field input with false, preserves its self-kill value, and proves the false-field dispatch equivalence and run-state preservation. The earlier 23-field embedding composes both false defaults. This is a launch value, not a global assumption that no hook exists. |
| Memory budgets | The source can allocate 16 GiB and the target 512 GiB (`State.source_alloc_limit`, `State.target_alloc_limit`). The `*_budgets` statements change this premise. The `*_budgets_only` statements have a finer premise for the source: it excludes a first-touch or a cumulative refusal, but not a single request that is larger than the whole budget (`Run.alloc_refuse_reason`). |
| Files | The file model has no full directory tree, no symbolic links, no device files except `/dev/null` and `/dev/urandom`, and no permissions. |
| Writes to an inode with an unmapped owner | Linux refuses every permission check that asks for write access to an inode whose uid or gid is unmapped (4294967295) with `-EACCES`, after the read-only `-EROFS` and before the mode bits are read (`inode_permission`, `fs/namei.c:589-590`; `HAS_UNMAPPED_ID`, `include/linux/fs.h:2587-2591`; v6.18.46). Linux asks for write access through `inode_permission` with `MAY_WRITE`, directly or through `path_permission` and `file_permission` (`include/linux/fs.h:3101-3110`). Each arm of the model that reaches such a call is listed here with the kernel line. A host (local disk) file system can hold such an inode: an on-disk uid or gid 0xFFFFFFFF reads as INVALID (`i_uid_write` and `i_gid_write`, `include/linux/fs.h:1609-1617`, called by ext4's `__ext4_iget`, `fs/ext4/inode.c:5302-5303`; the initial user namespace maps 0 to 4294967294 only, `kernel/user.c:38-56`, so `make_kuid` gives -1, `kernel/user_namespace.c:333`, 425). Linux makes no tmpfs inode with an unmapped owner: a tmpfs root takes the `uid=` and `gid=` options, which must map (`mm/shmem.c:4678`, 4690), or the mounter's fsuid and fsgid (5365-5366, 5155-5156); a new inode takes the creator's fsuid and fsgid, or a set-group-ID parent's gid (`inode_init_owner`, `fs/inode.c:2593-2605`); `chown` refuses an unmapped id (`fs/open.c:730-752`, 775-778); the model has no idmapped mount. With a case on a host file system, a state Linux makes (`W_unmapped` and `W_sticky` in `Checks/Cases/Ns/FilesCases.v`): `openat` and `openat2` opening an existing file for writing, with or without `O_CREAT` (`may_open`, `fs/namei.c:3565`, called at 3973), before the read-only mount's `-EROFS` (`file_get_write_access`, `fs/open.c:926`) and after the read-only superblock's (`sb_permission`, `fs/namei.c:550-551`), and in a sticky directory where `may_create_in_sticky` (3953-3956) depends on a sysctl the tables do not hold, where the `-EACCES` is Linux's answer under every value (`Files.sticky_answer`); `faccessat` with `W_OK` (`do_faccessat`, `fs/open.c:509`, before the read-only mount's `-EROFS` at 523-524). Answered, with the answer unchanged on every state Linux makes, because the model answers them only in tmpfs; their cases are code-path checks on a tmpfs state Linux does not reach: `openat` and `openat2` creating a free name with `O_CREAT` (`may_o_create`, `fs/namei.c:3622-3623`); `mkdirat` (`vfs_mkdir`'s `may_create`, 4440, 3318); `symlinkat` (`vfs_symlink`'s `may_create`, 4810, 3318); `unlinkat` without `AT_REMOVEDIR` (`vfs_unlink`'s `may_delete`, 4658, 3274). The same holds for the `/proc/sys/user` branch of the open and of `faccessat`, which runs the test before `proc_sys_permission` (`fs/namei.c:593`): Linux makes those inodes root's (`proc_sys_make_inode`, `fs/proc/proc_sysctl.c:490-493`; the set's root has no `set_ownership`, `kernel/ucount.c:58-61`), and its case is a code-path check too. Answered without the check, so the test changes no answer: `mkdirat` and `symlinkat` in a procfs or devpts directory, which `FsOps.create_tmpfs` answers `-EPERM` without asking `may_create`. That `-EPERM` is a wrong answer, corrected separately (#110): in procfs, Linux's lookup answers `-ENOENT` for a missing name first (`proc_lookup_de`, `fs/proc/generic.c:266`, through `lookup_one_qstr_excl`, `fs/namei.c:1705-1712`, in `filename_create`, 4231-4234); in devpts, `filename_create`'s deferred `-EROFS` (4223, 4236-4237) and `may_create` (4440, 4810; 3307-3318) come before the `-EPERM` (4444-4446, 4814-4815). Reached, and the model declines, so it gives no wrong answer: `openat` with `O_TRUNC` of a regular file, after the read-only mount's `-EROFS`, which comes first and is answered (`mnt_want_write`, `fs/namei.c:3967-3970`; the truncation is not modeled); `openat` of a FIFO, a socket or a device that the mount allows (`may_open`, 3546-3556, then 3565); `__O_TMPFILE` (`vfs_tmpfile`, 4019); `unlinkat` with `AT_REMOVEDIR` (`vfs_rmdir`'s `may_delete`, 4532, 3274); an `O_CREAT` create, `mkdirat`, `symlinkat` or a removal in a host directory, and an `O_CREAT` create or a removal in a procfs or devpts directory (`Files.create_file`, `FsOps.create_tmpfs`, `FsOps.unlink_at_parent`); `bind` of the AF_UNIX socket to a path (`unix_bind_bsd`'s `vfs_mknod`, `net/unix/af_unix.c:1403`, then `may_create`, `fs/namei.c:4305`, 3318) and `sendto` from it to a path (`unix_find_other`, `net/unix/af_unix.c:2182`, then `path_permission`, 1241), which `Ns.Net.bind_arm` and `Ns.Net.sendto_arm` decline; the `FIDEDUPERANGE` ioctl (`may_dedupe_file`, `fs/remap_range.c:427`) and the `FS_IOC_ENABLE_VERITY` ioctl (`fsverity_ioctl_enable`'s `file_permission`, `fs/verity/enable.c:345`), which both `ioctl` arms decline. No write-permission check in Linux: `write` and `writev` test the open file's mode (`vfs_write`, `fs/read_write.c:670-677`; `vfs_writev`, 1037-1051), and their `rw_verify_area` asks only the security module (473); a write to a `/proc/sys/user` file asks `sysctl_perm` (`proc_sys_call_handler`, `fs/proc/proc_sysctl.c:570-572`); `fchmod`'s `notify_change` asks for write access only for a time update (`may_setattr`, `fs/attr.c:376-384`, called at 428) and answers `-EOVERFLOW` for such an inode (523-528); `chdir` and `fchdir` ask `MAY_EXEC` and `MAY_CHDIR` (`fs/open.c:565`, 592) and the path walk `MAY_EXEC` (`fs/namei.c:1858`, 1873); `madvise` answers only `MADV_DONTNEED`, and its write test is for `MADV_COLD` and `MADV_PAGEOUT` on a file mapping (`mm/madvise.c:341-342`); `faccessat2` has no arm in `Ns.Spec.ns_table`, and the released arm (`Fs.Open.faccessat2_spec`) answers only `F_OK`, which asks for no write; the other arms of `Ns.Spec.ns_table` reach none of the three calls (a search of `fs/namespace.c`, `fs/fcntl.c`, `fs/ioctl.c`, `fs/stat.c`, `fs/statfs.c`, `fs/readdir.c`, `fs/d_path.c`, `fs/file.c`, `fs/read_write.c`, `fs/pipe.c`, `fs/eventfd.c`, `net/socket.c`, `net/netlink/`, `kernel/nsproxy.c`, `kernel/fork.c`, `kernel/exit.c`, `kernel/capability.c`, `kernel/signal.c`, `kernel/futex/`, `kernel/time/`, `kernel/sched/syscalls.c`, `mm/mmap.c`, `mm/mremap.c`, `mm/mprotect.c` and `drivers/char/random.c` finds none; `kernel/sys.c` has one, with `MAY_EXEC`, 1985). No arm in either table (`Ns.Spec.ns_spec` and the released table answer `unmodeled`): `truncate` (`vfs_truncate`, `fs/open.c:88`), `renameat2` (`vfs_rename`, `fs/namei.c:5118-5132`, and a directory moved to another parent, 5144-5156), `linkat` (`may_create`, 4908; `may_linkat`'s `safe_hardlink_source`, 1229), `mknodat` (`vfs_mknod`, 4305), `utimensat` with no time given (`may_setattr`, `fs/attr.c:380-381`), the `setxattr` and `removexattr` calls (`xattr_permission`, `fs/xattr.c:155`, from 282 and 541), `connect` and `sendmsg` to an AF_UNIX path (`net/unix/af_unix.c:1241`), `mq_open` (`ipc/mqueue.c:892`), `mincore` (`mm/mincore.c:217-218`), `cachestat` (`mm/filemap.c:4631`), `clone3` with `CLONE_INTO_CGROUP` and a write to `cgroup.procs` (`cgroup_may_write`, `kernel/cgroup/cgroup.c:5333`, from 6772 and 5353) and `bpf`'s `BPF_OBJ_GET` (`kernel/bpf/inode.c:508`). `HAS_UNMAPPED_ID`'s other callers answer other errnos, and none is reached by the model: `may_delete`'s `-EPERM` (`fs/namei.c:3280-3283`, after its `-EOVERFLOW` for the same ids at 3267-3270), `vfs_link`'s `-EPERM` (4925-4926) and `may_write_xattr`'s `-EPERM` (`fs/xattr.c:103-104`); `atime_needs_update` (`fs/inode.c:2155-2156`) skips an access-time update and changes no answer. The released file model (`Sys/Fs/`) holds no owners: its `openat` arms that can open for writing or create, and its `unlinkat` removal, admit `-EACCES` as a refusal of the environment (`Open.openat_errnos`, `Namei.unlinkat_errnos`); its `faccessat` and `faccessat2` answer only `F_OK`, which asks for no write; `ftruncate` (`do_ftruncate`, `fs/open.c:163-199`), `write`, `pwrite64` and `writev` reach no `inode_permission`; its `socket` and AF_INET `socketpair` arms make AF_INET sockets (`Socket.socket_spec`, `Socket.socketpair_modeled_b`), and its AF_UNIX SEQPACKET pairs have no pathname operations, so its `bind`, `connect`, `sendto` and `sendmsg` reach no AF_UNIX path; its `clone3` admits only a zero flag word, so no `CLONE_INTO_CGROUP`; its `ioctl` answers neither `FIDEDUPERANGE` nor `FS_IOC_ENABLE_VERITY`, and its `madvise` only `MADV_DONTNEED`. Two released `unlinkat` answers come after `may_delete`'s checks in Linux and admit neither `-EACCES` nor `-EOVERFLOW`: `AT_REMOVEDIR` on a file (`-ENOTDIR`, `Namei.unlink_found_spec`; `fs/namei.c:3284-3286`) and a directory under the run's `/tmp` (`-EISDIR`, `Namei.unlinkat_tmp_spec`; 3289-3290). Linux's `may_delete` answers first there: `-EOVERFLOW` when the victim's owner is unmapped (3267-3270), and `-EACCES` when the parent directory's owner is unmapped or its mode refuses the write (3274). These are wrong released answers, corrected separately (#109). |
| Immutable and append-only inodes | An inode with the immutable or the append-only flag (`S_IMMUTABLE`, `S_APPEND`) is outside the model: the tables do not record either flag. A host file system can carry them, and so can tmpfs (`shmem_set_inode_flags`, `mm/shmem.c:3050-3053`; v6.18.46). On such an inode Linux answers `-EPERM` where the model answers by the mode bits, for example: a permission check that asks for write access (`inode_permission`, `fs/namei.c:581-582`, before the unmapped-owner `-EACCES` at 589-590), as in an open for writing or `faccessat` with `W_OK`; an open for writing of an append-only file without `O_APPEND`, or with `O_TRUNC` (`may_open`, 3572-3576); a removal from an append-only directory, or of an immutable or append-only file (`may_delete`, 3277-3283); `fchmod` (`may_setattr`, `fs/attr.c:368-369`). |
| Paths under `/proc` | `openat` answers two shapes on a procfs name: "/proc", or a name that starts with "/proc/" and has no `..` component (`Open.proc_path_b`), given absolutely or relative to an O_PATH descriptor on one. O_PATH (alone, or with `O_DIRECTORY` and `O_NOFOLLOW`; `O_CLOEXEC`, `O_LARGEFILE` and `O_NONBLOCK` are ignored) gives an O_PATH descriptor (`State.OProcPath`). O_RDONLY gives a `State.OProcFile` only for `/proc/sys/kernel/overflowuid` and `/proc/sys/kernel/overflowgid`; these regular sysctl leaves use `proc_dointvec_minmax` in `kernel/sys.c` (lines 186 and 195, v6.18.44; identical at v6.18.46). Every other sysctl name is `unmodeled`, including `/proc/sys/` and `/proc/sys/kernel`: they are directories whose `.read` is `generic_read_dir`, returning `-EISDIR` (`fs/proc/proc_sysctl.c`:867-870,1566-1567; `fs/libfs.c`:224-227, v6.18.44; identical at v6.18.46). Either answered open may instead be any errno but `-EINTR` (`Syscall.errno_any`; `fs/namei.c` and `fs/open.c`, v6.18.44). Every other flag word on a procfs name, and O_PATH on any other name, is `unmodeled`. `read` on an `OProcFile` answers 0 to `count` bytes of the environment's choice, or any errno but `-EINTR`, for a `count` of at most 128 KiB; a destination that is only partly writable is `unmodeled`. `newfstatat` relative to an `OProcPath` descriptor answers only for flags 0 and `AT_SYMLINK_NOFOLLOW`: any errno but `-EINTR`, or 0 with 128 bytes whose padding is zero; a partly writable statbuf is `unmodeled`. `close`, `close_range` and `dup3` (onto it) remove these descriptors and `clone` passes them; fcntl's F_SETFD answers 0 and F_GETFD answers 0 or FD_CLOEXEC. getsockname, getpeername, getsockopt and shutdown answer -EBADF on `OProcPath`, and -ENOTSOCK on `OProcFile` or `OEventFd`; setsockopt gives those answers only without a cgroup-BPF hook, and otherwise declines as the cgroup-BPF row states. `read` and `write` answer -EBADF on `OProcPath`: `ksys_read` and `ksys_write` take the descriptor with `fdget_pos`, which refuses an O_PATH file (`fs/read_write.c`, `fs/file.c`, v6.18.46). `write` answers -EBADF on `OProcFile`, which is open read-only (`vfs_write`). `setns` answers -EBADF on `OProcPath` and -EINVAL on `OProcFile` (the `setns` row). Every other call on one is `unmodeled`. `newfstatat` and `readlinkat` from `AT_FDCWD` decline a path walk the flat file model cannot represent, including a `..` component or a separator path other than a canonical `/tmp/<name>`, because it may reach procfs or an unmodeled directory. No modeled run can give `-EINTR`: Linux answers it only when a signal handler runs or a signal/notification interrupts the call, and the assumptions below exclude both. |
| `eventfd2` descriptors | `eventfd2` with an accepted flag word gives the lowest free descriptor, holding an eventfd with that flag word (`State.OEventFd`), or `-ENOMEM`, `-EMFILE` or `-ENFILE` (`do_eventfd`, `fs/eventfd.c`, v6.18.44; identical at v6.18.46). The counter is shared with every other holder of the eventfd, so the model holds it as the environment's (`eventfd_read`, `eventfd_write`, `fs/eventfd.c`, v6.18.44; identical at v6.18.46). An eventfd is NON-BLOCKING when its `eventfd2` word has `EFD_NONBLOCK`, under the assumption that no other holder changes its `O_NONBLOCK` ("Assumptions that the model does not check"). `read` of at least 8 bytes on a NON-BLOCKING eventfd answers `-EAGAIN`, or 8 with a nonzero value delivered at the buffer, exactly 1 under `EFD_SEMAPHORE` (`ReadWrite.read_eventfd_spec`); a BLOCKING `read` is `unmodeled`, because it may wait. `write` of exactly 8 bytes answers `-EINVAL` for the value 2^64 - 1, decided before anything else about the counter, and otherwise 8, with `-EAGAIN` also admitted on a non-blocking eventfd (`ReadWrite.write_eventfd_spec`). A program whose eventfd counter comes within v of 2^64 - 1 at a write of v has no statement here: there Linux makes a blocking write wait. For v = 1 the counter needs about 1.8 x 10^19 prior increments. The exclusion is partly an environment condition: the counter is shared, so the program's part is its own writes and the world's part is every other writer's, whoever they are. A `read` of fewer than 8 bytes and a `write` of other than 8 are `-EINVAL`, a buffer `access_ok` refuses is `-EFAULT`, and a read destination only partly writable is `unmodeled`. `select`, `poll` and `epoll` on an eventfd are `unmodeled`; fcntl's F_SETFD/F_GETFD and the five socket calls answer as the Paths under `/proc` row says, and `setns` answers `-EINVAL` (the `setns` row). |
| The `/proc/self/fd` directory | `openat` answers "/proc/self/fd", given absolutely or as "self/fd" relative to an O_PATH descriptor on "/proc" (relative to any other descriptor it is `unmodeled`), for a read-only flag word whose other bits are `O_DIRECTORY` and `O_NOCTTY` (`O_CLOEXEC`, `O_LARGEFILE` and `O_NONBLOCK` are ignored; `Open.procfd_dir_word`): the lowest free descriptor holding the listing of the caller's own descriptor table at position 0 (`State.OProcFdDir`), or any errno but `-EINTR`. Every other directory under `/proc` stays `unmodeled`. On this descriptor, `fstat` answers a directory with mode 0500 (the "fd" entry of `tgid_base_stuff`, `fs/proc/base.c`, v6.18.44; identical at v6.18.46), every other member the environment's; fcntl's `F_GETFL` answers the open word with `O_LARGEFILE` added and `O_CLOEXEC` and `O_NOCTTY` removed (`build_open_flags`, `do_dentry_open`, `fs/open.c`); and `getdents64` lists ".", "..", then every open descriptor of the model's table at that call, in ascending order, from the stored position (`Readdir.procfd_getdents_spec`; `proc_readfd_common`, `fs/proc/fd.c`; `filldir64`, `fs/readdir.c`, v6.18.44; identical at v6.18.46). The names, `d_off`, `d_reclen` and `d_type` are exact and `d_ino` is the environment's. A buffer with no room for the next record is `-EINVAL`, one `access_ok` refuses is `-EFAULT`, and one only partly writable is `unmodeled`. After a call that reaches the end, the position is the kernel's `max_fds + 2`, which the model does not know, so a later `getdents64` on that descriptor is `unmodeled`. `write` on it answers `-EBADF` (the directory is open read-only), and `read` answers `-EFAULT` for a buffer `access_ok` refuses and `-EISDIR` otherwise (`vfs_read`, `fs/read_write.c`; `generic_read_dir`, `fs/libfs.c`; v6.18.46). Duplicating it and `clone` while one is open are `unmodeled`, because two descriptors would share one directory position. `close`, `close_range` and fcntl's F_SETFD/F_GETFD answer, the five socket calls answer `-ENOTSOCK`, and `setns` answers `-EINVAL` (the `setns` row). |
| `signalfd4` | `signalfd4(-1, mask, 8, flags)` with flags made of `SFD_CLOEXEC` and `SFD_NONBLOCK` only gives the lowest free descriptor holding a signalfd with the mask, `SIGKILL` and `SIGSTOP` removed, and the flag word (`State.OSignalFd`), or `-ENOMEM`, `-EMFILE` or `-ENFILE` (`SYSCALL_DEFINE4(signalfd4)`, `do_signalfd4`, `fs/signalfd.c`, v6.18.44; identical at v6.18.46). A `sizemask` other than 8 and a flag outside those two are `-EINVAL`, and a mask `copy_from_user` cannot read is `-EFAULT`. A `ufd` other than -1, which updates an existing signalfd, is `unmodeled`. `read`, `select`, `poll` and `epoll` on a signalfd are `unmodeled`, and so are duplicating it and `clone` while one is open, because two descriptors would share one mask. `write` answers `-EINVAL`: a signalfd has no write operation (`signalfd_fops`, `fs/signalfd.c`; `vfs_write`, `fs/read_write.c`; v6.18.46). `close`, `close_range` and fcntl's F_SETFD/F_GETFD answer, the five socket calls answer `-ENOTSOCK`, and `setns` answers `-EINVAL` (the `setns` row). |
| Namespace and mount model descriptors | A descriptor may hold `State.ONsFile h`, an open file that the namespace and mount model holds under handle `h`. No arm of `spec_table` makes one, so a run from `init_config` never holds one. Its object may be a directory, a regular file, a procfs file, an eventfd or a socket, so the model answers only what Linux answers for every open file: `close` and `close_range` remove it, `fcntl`'s `F_SETFD` and `F_GETFD` answer, `dup3` onto it replaces it, and `clone` passes it. `close` answers 0 on the condition that the namespace and mount model mints an `ONsFile` only on an object whose `f_op->flush` is absent or cannot fail: `SYSCALL_DEFINE1(close)` returns `filp_flush`'s result (`fs/open.c`, v6.18.44), and FUSE, NFS, CIFS, orangefs, ecryptfs and overlayfs have a `.flush` that can fail. Every other call on it is `unmodeled`, and while one is open `flock` on any file and `unlinkat` are `unmodeled` too, because its object may be that file. |
| `setns` | `setns` answers `-EBADF` on a number that names no descriptor or names an O_PATH descriptor (`State.OProcPath`), and `-EINVAL` on every other descriptor except `State.ONsFile`, on which it is `unmodeled` (`SYSCALL_DEFINE2(setns)`, `kernel/nsproxy.c`; `fdget`, `fs/file.c`; v6.18.46). No descriptor of the model is a pidfd, and only an `ONsFile` may be a namespace file, so the model never joins a namespace with `setns`. The answer on fds 0, 1 and 2 rests on the assumption the Standard input and output row names. |
| Shared memory | The model has no shared mapping. `mmap` with `MAP_SHARED` is `unmodeled`, anonymous requests included. Linux builds an anonymous shared mapping on a shmem file (`mm/vma.c`, `__mmap_new_vma` calls `shmem_zero_setup`), so `vma_is_anonymous` is false for it, its pages survive the zap that `MADV_DONTNEED` performs, and a `fork` shares them instead of copying them. `Sys/Mm/Mmap.v` gives the full reason and what an arm would take. |
| A pid namespace's init exits | This holds for every pid namespace the tables hold that has a parent, whatever its allocation state (`PaUnknown`, `PaEmpty`, `PaInit` or `PaClosed`): a namespace the model made, and a namespace stated at launch, which `mk_pidns` (`Ns/Tables.v`) gives `PaUnknown`, including one whose pid 1 is a launched process (the fixtures `inside` and `no_admin_inside` in `Checks/Cases/Ns/CloneCases.v` are such a launch). When that namespace's init group ends, Linux closes its allocation and kills every other task of the namespace (`find_child_reaper`, kernel/exit.c:616-630; `zap_pid_ns_processes`, kernel/pid_namespace.c:200-232, v6.18.46). The namespace model's `exit` and `exit_group` answer as the released model does (`Ns.Pass`) and kill no other task, and the namespace's allocation state does not change: which tasks are in a namespace is the multi-process core's table, not the namespace state. A program that relies on pid 1's exit killing the other tasks in its pid namespace has no statement here. A clone into a different children's namespace already in `PaInit` or `PaUnknown` declines. When a namespace's init is outside the model, no model step can observe its end. |
| Children's pid namespace at launch | The default `cx_pidns_children = None` means that the launched process's pid namespace for children is its own active namespace (`pidns_children`). A launch that unshared or joined another namespace before exec sets `with_pidns_children` from measured facts. It is outside the released world and must state the whole context: namespace ids, each pid, capability sets, root, cwd, umask, securebits, close-on-exec descriptors, no-new-privs and dumpable. The released launch defaults are not measurements of that launch. |
| Measuring a children's pid namespace | `readlink` of `/proc/self/ns/pid_for_children` can return ENOENT both for a new namespace and for one closed by its failed first fork; a successful link does not establish that allocation remains enabled (kernel/pid_namespace.c:374-377; fs/nsfs.c:376-388, v6.18.46). Only provenance covering creation through launch can reconstruct `PaEmpty`: the launcher made the namespace with unshare, made no clone after it, and excluded outside entry, allocation and control writes for that whole interval. That establishes parent, owner, level, cursor 0 and the new-namespace limit. Other launches state measured allocation facts or use `PaUnknown`. |
| Pid allocation during the run | The launch value `env_outside_pids`, read by `ns_outside_pids`, defaults to false: no outside task allocates in or writes ns_last_pid or pid_max of any namespace whose cursor the model holds, for the whole run. True declines every clone that needs such a cursor. An outside task can enter or allocate through a children's namespace (kernel/pid_namespace.c:401-423; kernel/fork.c:2202). ns_last_pid selects the writer's active namespace; a pid_max descriptor retains the namespace chosen at open, even when passed to another writer (kernel/pid_namespace.c:289-302; kernel/pid.c:668-693; fs/proc/proc_sysctl.c:553-571, v6.18.46). This value says nothing about pre-launch events or occupancy. |
| Pid occupancy and limits at launch | `pidns_max` states each model namespace's measured limit, default 4194304. `pidns_cursor_clear` defaults to true and assumes that no pid above the cursor and below that limit is reserved at launch. A launch that cannot establish this sets it false. Every model level, including ancestors of an empty child namespace, must establish the fact; no in-run interference does not imply it. Cursor 7 with pid 8 occupied declines even with `env_outside_pids = false`. New namespaces establish their own clear range, not their ancestors'. Allocation at the bound declines instead of guessing Linux's cyclic search (kernel/pid.c:191-252; lib/idr.c:105-136, v6.18.46). |
| Parent-death signal | The multi-process core (`Procs.v`) holds each process's parent-death signal (`State.m_pdeath_signal`) but does not deliver it: when a parent exits, a child that armed `PR_SET_PDEATHSIG` is not signalled (`exit_notify` and `forget_original_parent`, `kernel/exit.c`, v6.18.44). A program that relies on its parent's death killing it has no statement here; a statement may still read the armed signal with `PR_GET_PDEATHSIG`. |
| Namespace-model calls while another process lives | While another process lives, a task outside the released world gets the core's own numbers (`Procs.multiproc_base`: among them `clock_gettime`, whose clock the core brings up to every peer's, and `unlinkat`, which the core refuses when it removes a path a peer's descriptor or stat pin names) and the calls `Ns.Spec.ns_multiproc` lists: the calls a sandbox's setup child makes between its clone and its exec (path walks, mounts, `pivot_root`, `unshare`, `capget`, `capset`, `prctl`, `umask`, `getpid`, `sethostname`, `setsid`, `socket` and the netlink calls, `rt_sigprocmask`), each only where its answer reads and writes the namespace state (one copy, shared as Linux shares it), the task's own context, descriptor table and address space (per process after a clone without CLONE_VM: `brk`, `munmap`, `mremap`, `mprotect`, `madvise`, and `mmap` with MAP_ANONYMOUS), or nothing a peer can change: `read`, `write`, `fstat`, `fchmod`, `getdents64`, `ioctl` and the socket calls on a descriptor of the namespace model, `read` of an eventfd, `read` of an inherited descriptor that holds its offset (after a clone of either word only the child holds it), `writev` of a standard channel, `close` of an opaque descriptor, and `fcntl` F_GETFD/F_SETFD. Every other call is a model error there, never an answer: the multi-process core keeps the released file system, pipes and sockets per process. A task in the released world gets the core's own list. |
| The vDSO | The model maps the vDSO text and the four vvar pages that `execve` installs, and answers a call to an exported entry with the system call's own specification (`Run.sstep`'s vDSO arm). It does not run the vDSO's instructions. Four cases are `unmodeled`, and a proof says nothing about a program that reaches one: a load from the vvar pages; a fetch at any text address that is not an exported entry; a call to `__vdso_getrandom` or `__vdso_rt_sigreturn`; and an outcome of a call that returns `-EFAULT`. A store to the text or to vvar is a fault, as on Linux: the kernel maps neither with `VM_WRITE`. The text mapping carries no `x` flag in the model, although Linux maps it `PROT_READ\|PROT_EXEC`: the flag says "the model fetches and executes these bytes", and of the vDSO's bytes it does not. |

The entry premises also limit the launches that a statement covers, and
they limit them to Linux's own. For one input and one kernel build
(`State.KernelBuild`), `Run.entry_launch_ok_va` admits exactly the
stack VMA ends, entry stack pointers and mmap bases that a Linux
v6.18.46 launch gives, and `StackLayout.build_stack_bytes` lays Linux's
bytes between the stack pointer and that end. There is no band. The
three rules are `randomize_stack_top` and `setup_arg_pages`
(`mm/util.c`, `fs/exec.c`) for the end, `create_elf_tables`
(`fs/binfmt_elf.c`) for the stack pointer, and `mmap_base` with
`arch_mmap_rnd` (`mm/util.c`) for the base. This closes the residual
R-d that earlier revisions named, where `sp` and the base were drawn
apart: `Checks/Cases/EntryLaunch.v`'s `a1_kind1_pair_refused` refutes
its example pair, `sp` = 0x7fffe0000000 with the base at 0x7ffff8000000.

The launch's own facts are therefore premises of each statement:
whether the launch randomises, the `stack_guard_gap` boot parameter,
`vm.mmap_rnd_bits`, `CONFIG_RSEQ`, the vector unit's `VLENB`, the
machine's four cache leaves and which vDSO image the build carries.
They are fields of `State.KernelBuild`, which is part of the input, so
both binaries of a pair are launched on one machine by one launcher.

These cases stay outside the model:

- QEMU user mode. It builds another entry block entirely; "Where QEMU
  user mode differs" below gives it.
- A kernel whose vDSO image the model does not hold. `State.KernelBuild`
  names an image, so a statement says nothing about a build whose image
  is not among them.
- Sv39 with a large `stack_guard_gap`. `mmap_base` then clamps the gap
  at `STACK_TOP / 6 * 5`, and Linux's top-down search stops at the
  stack's guard region instead (`mm/vma.c`), so the vDSO's address and
  the stack floor can differ from the model's. The proofs use Sv48.
- A program run by a task whose `brk_randomized` bit is clear, on a
  kernel built with `CONFIG_COMPAT_BRK`. A launch that does not
  randomise (`State.kb_aslr` false) is in scope, and so is the program
  break it gets. `Sys/Mm/Mmap.v`'s `min_brk` is `vm_start_brk`, Linux's
  `mm->start_brk`. `SYSCALL_DEFINE1(brk)` (`mm/mmap.c`) uses that value
  except under `CONFIG_COMPAT_BRK` with `current->brk_randomized` clear,
  where it takes `mm->end_data`, a lower floor: Linux then grants a
  break below the heap base that the model answers with the unchanged
  break. The bit is set by an exec that moves the break, which needs
  `PF_RANDOMIZE` and `randomize_va_space` 2 (`fs/binfmt_elf.c`,
  `load_elf_binary`). Nothing clears it, and `fork` copies it, so in the
  ordinary case it is set: a kernel without `CONFIG_COMPAT_BRK` has no
  such floor, and with `randomize_va_space` 2 from boot, `init`'s exec
  sets the bit for every later task, a `setarch -R` launch included. It
  stays clear only on a task whose lineage had no randomising exec while
  `randomize_va_space` was 2: for example, a `setarch -R` shell started
  under `randomize_va_space` 1 (the boot default with
  `CONFIG_COMPAT_BRK`, `mm/memory.c`), which then runs the program after
  the setting is raised to 2. A statement says nothing about a program
  run from such a task. `Run.valid_brk` holds both of Linux's initial
  breaks: its band `[image top, image top + 1 GiB]` holds the randomised
  break and also the fixed page-rounded image top that a launch without
  randomisation gets.

The finite input record is a surjection onto the finite inputs, not an
encoding of them. `EquivalenceDefinition/FinInput.v`'s `to_proc_input`
pads the record's random field with `State.default_urandom`, the
all-zero stream, so a record carrying no random bytes and one carrying a
list of zeros denote the same input: `to_proc_input_not_inj` exhibits
that collision, and `to_proc_input_inj` holds only with the random
fields assumed equal. Nothing is lost to a statement quantified over
inputs, because everything the record denotes is finite and every finite
input is denoted (`finite_input_surjection`,
`valid_finite_input_surjection`), so the two quantifiers coincide. What
an argument may not do is count finite records, or conclude that two
runs differ because their records differ. `FinInput.v`'s header carries
the reasoning.

## Assumptions that the model does not check

If one of these assumptions is false, a proof can be correct but it does
not apply.

- No other process, also not a child of the program, changes the modeled
  files or holds locks on them.
- No other holder of an eventfd's open file description, for example a
  child that got it at a modeled `clone`, changes its `O_NONBLOCK` with
  `fcntl(F_SETFL)` or `ioctl(FIONBIO)`. The eventfd `read` and `write`
  arms take `O_NONBLOCK` from the word the eventfd was made with
  (`ReadWrite.efd_nonblock_b`), and Linux reads it from the file's
  `f_flags` at each call (`eventfd_read`, `eventfd_write`,
  `fs/eventfd.c`; `setfl`, `fs/fcntl.c`; v6.18.44, identical at
  v6.18.46).
- Each inherited descriptor (`State.ProcInput.in_inherited_fds`) is an
  open file description of its own: no two of them share one; no process
  outside the model reads it, seeks it or truncates it while the run
  lives; and no process, the run's own processes included, changes its
  file while the run lives. Linux keeps one offset per description and
  moves it at every `read` through any descriptor that names it
  (`ksys_read`, `fs/read_write.c`; `dup_fd`, `fs/file.c`; v6.18.46), and
  the model holds one offset per inherited descriptor. The model also
  holds the file's bytes apart from its file system, with no inode
  identity, so a write to the same file through a path would leave those
  bytes stale. Only a statement over `Run.valid_input_inherited` rests on
  this assumption: every other input predicate pins the list empty.
- The modeled files, the inherited descriptors' files and the standard
  descriptors' far ends sit on file
  systems whose `close` cannot fail. `SYSCALL_DEFINE1(close)` returns
  `filp_flush`'s result, and `filp_flush` runs the file's `f_op->flush`
  (`fs/open.c`, v6.18.44; identical at v6.18.46). FUSE, NFS, CIFS,
  orangefs and ecryptfs supply one that can return an error, and
  overlayfs passes the call to the file below it. The model answers 0
  for `close` on every descriptor kind, so a program whose files live
  on such a file system can see an error the model does not give.
- `/dev/null` is the null device (major 1, minor 3). `/dev/urandom` is the
  random device (major 1, minor 9).
- `CONFIG_UNIX=y`: AF_UNIX is registered, so its supported socket types do
  not answer `-EAFNOSUPPORT` for a missing family (`__sock_create`,
  `net/socket.c`, v6.18.46); allocation and argument failures still apply.
- procfs is mounted at `/proc` in the process's root, and nothing under
  `/proc/sys` is a symbolic link. `Open.proc_path_b` and
  `Open.proc_sys_file_b` read the name, not the file system: a name
  that starts with "/proc/" is taken to be a procfs name, and an
  `O_RDONLY` open is answered only for `/proc/sys/kernel/overflowuid`
  and `/proc/sys/kernel/overflowgid`; every other sysctl name declines.
- No BPF LSM program is attached to `file_alloc_security`.
  `EventFd.eventfd2_errnos` is the list of errnos an accepted `eventfd2`
  can meet without one (`do_eventfd`, `fs/eventfd.c`, and
  `alloc_empty_file`, `fs/file_table.c`, v6.18.44); such a program could
  return any errno.
- The working directory is not `/`. The flat file model has no directory
  tree or symlinks, so this makes a slash-free relative `proc` name
  unable to reach the procfs mount; a relative path with a separator or
  a `..` component is declined by `Stat.statat_cwd_path` regardless.
- No tracer (`ptrace`) or other outside agent changes the process.
- The binary is a static executable (`ET_EXEC`). `tools/elf_snapshot.py`
  refuses an image whose `e_type` is not `ET_EXEC`, so a snapshot cannot
  carry a PIE. The model needs this twice. For a static PIE (`ET_DYN` with
  no `PT_INTERP`) the model can give a wrong initial program break, and
  Linux maps the segments through the mmap region before it installs the
  vDSO pair (`fs/binfmt_elf.c`, `load_elf_binary`: the segment mapping has
  a load bias of 0, and `ARCH_SETUP_ADDITIONAL_PAGES` comes after it), so
  the pair is not directly below the mmap base and the next bullet is
  false.
- At launch the process has no children and no tracees. The model takes
  `-ECHILD` from `wait4` and `waitid` only while no modeled `clone` has
  recorded a child (`State.m_has_children`, the comment at the head of
  `Sys/Kernel/Exit.v`). `execve` does not reap a child in Linux, so a
  launcher that forks a grandchild, or attaches a tracee, before it
  execs the image makes this assumption false.
- At launch SIGCHLD is not at SIG_IGN. A launcher's SIG_IGN survives
  `execve` (`begin_new_exec` calls `flush_signal_handlers` with
  `force_default = 0`, `fs/exec.c`, and that function keeps SIG_IGN,
  `kernel/signal.c`), and under it Linux reaps an exiting child itself
  (`do_notify_parent`, `kernel/signal.c`): `wait4` then answers 0 and
  then `-ECHILD`, never the child's pid, and the model admits the pid and
  rejects that `-ECHILD`. The model declines every SIG_IGN or
  SA_NOCLDWAIT install for SIGCHLD that the process makes
  (`Kernel.Signal.sigchld_dfl_install`), and `execve` clears `sa_flags`,
  so only the launch's SIG_IGN is open (Linux v6.18.44; identical at
  v6.18.46). `Kernel.Exit.wait4_spec` does not need this assumption: it
  answers a recorded child only while `State.m_sigchld_dfl` is set, and
  the bit is set only if every child the process has was cloned while
  SIGCHLD was SIG_DFL (`Kernel.Signal.sigchld_install_model` sets it
  only in a process with no recorded child). The assumption still covers
  the multi-process core's own `wait4` arms in `Procs.v`, which do not
  read the bit, until the fix tracked in #125 lands.
- Nothing outside the process makes a signal pending for it, or wakes it
  as if one were: no other process sends it a signal; it is not frozen
  (`freeze_task`, `kernel/freezer.c`, for suspend and the cgroup v1
  freezer; `cgroup_freeze_task`, `kernel/cgroup/freezer.c`, for the
  cgroup v2 freezer); and no livepatch transition signals it
  (`klp_send_signals`, `kernel/livepatch/transition.c`). A SIGCHLD from
  its own child is allowed: at SIG_DFL it is discarded (`sig_ignored`,
  `kernel/signal.c`), and while it is blocked it does not make
  `signal_pending` true (`recalc_sigpending_tsk`, `kernel/signal.c`).
  In particular the parent does not exit while a parent-death signal is
  set (`prctl(PR_SET_PDEATHSIG)`): Linux then sends that signal
  (`forget_original_parent`, `kernel/exit.c`, v6.18.44), and the model
  has no transition for it. A statement about a program that sets one
  holds for the runs in which the parent outlives it.
- The launcher set no parent-death signal before its `execve`. The
  model starts the signal at 0 (`State.m_pdeath_signal_init_model`), but
  `execve` keeps the value a launcher set with `prctl(PR_SET_PDEATHSIG)`
  (`begin_new_exec`, `fs/exec.c`, v6.18.44, clears it only for a secure
  exec), so for such a launch the first `prctl(PR_GET_PDEATHSIG)` reads
  the launcher's signal, which the model refuses.
- The launcher set no no-new-privs bit before its `execve`, and the exec
  that started the process raised no privilege and could read its own
  binary. The model starts the bit false (`State.m_no_new_privs_init_model`)
  and the dumpable mode 1 (`State.m_dumpable_init_model`). `execve` keeps a
  bit the launcher set (a container started with no_new_privs, as
  Kubernetes' `allowPrivilegeEscalation: false` does, starts with it set).
  `begin_new_exec` (`fs/exec.c`, v6.18.44) gives the build's
  `fs.suid_dumpable` instead of 1 to an exec whose binary the launching user
  cannot read (`would_dump`) or whose effective ids differ from the real
  ones, and `commit_creds` does to one that gained a capability.
- The process runs in the init user namespace, under the capability
  LSM alone, with the capability state `State.creds_privileged`
  describes. The credential calls, `getresuid`, `getresgid`, `getsid`,
  `prctl` and `setgroups` answer for that kernel (the credentials
  section of `Sys/Kernel/Sys.v`): a second LSM (SELinux, AppArmor, a BPF
  program on `task_prctl`, `task_getsid` or `task_fix_setgroups`) can
  refuse where the model answers. The namespace model rests on the same
  assumption. Beside the tables' answer, an arm of `Ns.Spec.ns_table`
  admits only the environment refusals its file lists, each with the
  Linux v6.18.44 function that returns it (`Ns.Spec.ns_injected_table`):
  an allocation failure (`-ENOMEM`, the `-ENFILE` of a socket's inode,
  `-ENOSPC`, `-EMFILE`, `-ENOBUFS`, and `set_cred_ucounts`'s `-EAGAIN`),
  the system-wide file limit (`-ENFILE`), a full netlink hash table
  (`-EOVERFLOW`), a tmpfs instance at its inode or size limit
  (`-ENOSPC`), an I/O error (`-EIO`), and the `-EAGAIN` of an `openat2`
  whose walk took a `..` under `RESOLVE_IN_ROOT` while something was
  renamed or mounted. The `-EIO` is a host file system's, or that of a
  tmpfs page a write cannot read back: a hardware-poisoned page
  (`shmem_write_begin`, `mm/shmem.c`) or a swapped-out page whose swap-in
  fails (`shmem_swapin_folio`). It admits no refusal of a security
  module, so a second LSM's hook (`security_path_unlink`,
  `security_sb_mount`, `security_create_user_ns`, a socket hook) can
  refuse where it answers. Two other refusers are outside the model too,
  and the model assumes neither is there: a fanotify permission
  listener, which can refuse an open (`fsnotify_open_perm_and_set_mode`,
  called by `do_dentry_open`, `fs/open.c`), a read or a write
  (`fsnotify_file_area_perm`, called by `rw_verify_area`,
  `fs/read_write.c`) and a directory read (`iterate_dir`,
  `fs/readdir.c`); and a cgroup-BPF sysctl program, which can refuse a
  sysctl write such as one to `/proc/sys/user/max_user_namespaces`
  (`BPF_CGROUP_RUN_PROG_SYSCTL` in `proc_sys_call_handler`,
  `fs/proc/proc_sysctl.c`). Under `Run.forced_only_cfg` its filter
  (`Ns.Spec.ns_refusal`) removes each listed refusal wherever the model
  also admits the tables' own answer. A tables' answer that the
  environment can also return (a count limit's `-ENOSPC`, the `-ENOMEM`
  of a sysctl write of 4 MiB or more) is kept (`Ns.Arm.ni_forced`,
  checked of every row by `Ns.Spec.ns_injected_forced`). On a descriptor
  of the released model (`write`, `getdents64`) the filter is the
  released one, with the released table's family
  (`Ns.Spec.released_fd_call`). A namespace `clone` is the core's call,
  and its failures are not listed ("Errors of a namespace `clone`"
  below).
- The host file systems the namespace model walks (`Ns.Tables.SbHost`)
  are local disk file systems: a lookup, an open or the read of a link's
  text there fails, beside the tables' answer, only for lack of memory
  or with an I/O error (`-EIO`), as `Ns.Arm.walk_pairs` and the arm files
  list. A network or FUSE file system can answer other errnos, which the
  namespace model does not give.
- No host mount event reaches a mount namespace of the namespace model,
  under the default launch. A peer group that the tables hold and that
  also has a member outside the tables is open: a mount or unmount at that
  outside member propagates to every member in the tables and to every
  slave below them (`propagate_mnt`, `propagate_umount`, `fs/pnode.c`,
  v6.18.46), at any time and without a call of the model. The launch names
  these groups in `Ns.Tables.env_open_groups`. Host
  `/proc/<pid>/mountinfo` files reveal namespace-held peers, but not
  detached trees: mountinfo alone cannot establish that no host process
  holds a detached copy of a mount of a model group. The default empty
  group list assumes that no such host-held detached copy exists either.
  The separate launch value `Ns.Tables.env_entered_mntns` names namespaces
  an outside task may enter or alter through a path or descriptor. Its
  default `[]` means: no process outside the model enters or changes a
  model mount namespace, including a detached tree held by a model task,
  or changes mounts through a path or descriptor into such a tree
  (`setns`, `kernel/nsproxy.c:536-569`; `mntns_install`,
  `fs/namespace.c:6261-6274`; `may_change_propagation`, `2823-2834`), nor
  reconfigures the superblock of a model mount through a mount the tables
  do not hold (`fspick` with `FSCONFIG_CMD_RECONFIGURE` needs no
  `check_mnt`, only `may_mount` and `CAP_SYS_ADMIN` over the superblock's
  user namespace: `fs/fsopen.c:163-194, 251-268, 296-297`).
  Both-empty defaults keep the exact successful and error cases unchanged.
  Named nondefault uncertainty declines rather than claiming stale topology.
  `Ns.Propagation.entered_closure` also includes anonymous trees whose
  originating real namespace is listed, and every origin-None anonymous
  tree under any nonempty entered list, including records added later.
  `open_groups` adds every peer group on a superblock represented in this
  closure, even in an unlisted namespace: an outside `SET_GROUP` can join
  a private listed mount to such a group (`fs/namespace.c:3328-3355`).
  `CLONE_NEWNS` adds the copied real namespace when the source is listed;
  `CLONE_NEWNS` through unshare remains unsupported. With both lists empty
  no outside event reaches a model namespace
  (`Ns.Propagation.closed_no_outside_event`). Otherwise a call whose answer
  reads uncertain topology has no answer: a path walk that
  enters such a mount or whose ".." climbs through such a parent mount
  (`Ns.Walk.follow_mounts_fuel`, `Ns.Walk.choose_mountpoint_fuel`,
  `Ns.Propagation.open_mount`), `getcwd` and the text of a procfs
  cwd/root/fd link whose upward path steps into such a parent mount
  (`Ns.Files.path_open`: a host unmount can detach the child below it,
  `fs/pnode.c:500-535`, `586-593`; `fs/namespace.c:1752-1753`,
  `1813-1819`, `993-1000`; the climb then stops there,
  `fs/d_path.c:110-125`), or whose start or visited mount belongs to an
  entered namespace (an outside move can change even a private cwd mount's
  path), a `clone` or `unshare` with
  `CLONE_NEWUSER`, after the earlier level/count `ENOSPC` checks pass
  (`kernel/user_namespace.c:91-107`), which reads the topmost mount on
  the caller's mount namespace's root mount to decide whether the caller
  is chrooted (`Ns.UserArms.current_chrooted`; `current_chrooted`,
  `fs/namespace.c:6118-6132`), and a `/proc/<pid>/fd` link to a
  descriptor the released model opened, whose path resolves from the
  topmost mount on the host's root mount (`Ns.Arm.host_loc`), when a
  mount of the stack from that root mount to its top is such a mount
  (`Ns.Walk.ns_top_open`), a bind or a new mount (`mount(2)`)
  in a mount namespace that holds such a mount, or onto a shared mount
  whose propagation tree holds one or reaches a namespace that holds one
  (`Ns.Propagation.ns_open`, `Ns.Propagation.attach_check`), a
  propagation change (`mount(2)` with `MS_SHARED`, `MS_SLAVE`,
  `MS_PRIVATE` or `MS_UNBINDABLE`) or a `mount_setattr` whose target, or
  with `MS_REC` or `AT_RECURSIVE` whose subtree, holds one, or, for a
  change to slave, private or unbindable, whose slaves it hands over, or
  the mounts whose slave lists it changes, hold one
  (`Ns.Propagation.targets_open`: `change_mnt_propagation` takes the next
  peer among the group's members outside the tables too,
  `fs/pnode.c:101-116`, and `transfer_propagation` sets the master of
  each slave it hands over, `fs/pnode.c:74-88`; a `mount_setattr` still
  answers the `EPERM` or `EBUSY` that its selected tree alone decides,
  `mount_setattr_prepare`, `fs/namespace.c:4710-4743`, as it reads those
  slaves and mounts only after these checks), an
  `umount2` with `MNT_DETACH` whose subtree, candidates or parents' peers
  and slaves hold one (`Ns.Propagation.umount_detach_prop`: every
  `MNT_DETACH` runs `umount_tree` with `UMOUNT_PROPAGATE`,
  `fs/namespace.c:1949`, `1793-1794`, and `propagate_umount` gathers its
  candidates on those peers and slaves, `fs/pnode.c:505-531`), and a read
  of `/proc/<pid>/mountinfo` of a mount namespace that holds one
  (`Ns.Mountinfo.mountinfo_text`), and a `pivot_root` whose mount
  namespace holds one, after both walks (`Ns.MountArms.pivot_root_fn`,
  `Ns.Propagation.ns_open`: its tests read the new root's, the old root's
  and put_old's mounts and parents, `fs/namespace.c:4584-4618`). Every
  answer that reads a mount's flags or its superblock's read-only state
  also has no answer when some mount on that superblock is such a mount
  (`Ns.Propagation.flags_open`): an outside task in the namespace can
  change them (`do_mount_setattr`, `fs/namespace.c:4781-4838`, its
  `check_mnt` at 4816; `do_reconfigure_mnt`, 3211-3241; `do_remount`,
  3248-3294). These are a write `open` or `O_TRUNC` (`EROFS`), an `open`
  of a device (`EACCES` for nodev, unless the superblock's `SB_I_NODEV`
  decides it), `faccessat` for `W_OK` or for `X_OK` on a regular file
  (unless `SB_I_NOEXEC` decides it), a file, directory, node or link
  creation after its `ENAMETOOLONG`, `fchmod`, `unlinkat`, a new mount
  (`mount(2)`) in a namespace that holds such a mount
  (`Ns.NewMount.new_mount_shared`: `mnt_already_visible` reads procfs
  mounts' flags), and a read of `/proc/<pid>/mountinfo` of a namespace
  that holds such a mount (each line prints its superblock's read-only
  state, `show_mountinfo`, `fs/proc_namespace.c:182`). `statfs` and
  `fstatfs` then admit any `f_flags`. The
  path-text check declines a start in an entered namespace even when the
  start is the caller's root, where Linux prints "/" without reading
  topology (`fs/d_path.c:107`): a decline, never a wrong answer.
- The sysctls `kernel.overflowuid` and `kernel.overflowgid` hold 65534,
  the kernel's default (`include/linux/highuid.h:41-42`,
  `kernel/sys.c:167-168`, v6.18.46), and the host does not write them
  during the run. This is the default of the namespace model's launch
  value `Ns.Tables.env_overflow_ids`, `Some (65534, 65534)`. A stat in
  the namespace model shows an owner id that has no mapping in the
  caller's user namespace, the id 4294967295 included, as that value
  (`from_kuid_munged`, `from_kgid_munged`,
  `kernel/user_namespace.c:466-473`, `533-541`; `Ns.Files.munged_ok`).
  The host's root can set each sysctl to any value from 0 to 65535 at
  any time (`kernel/sys.c:184-202`). A statement for a launch that
  measured other values names them (`Some (u, g)`, through
  `Ns.Tables.env_with_overflow_ids`); a statement for a host that may
  write the sysctls during the run names `None`, under which such an id
  is shown as any value from 0 to 65535. A mapped id is exact under
  every value. A named `u` or `g` outside 0 to 65535 is no value a host
  can hold, and a stat under it has no answer
  (`Ns.Files.stat_ids_decided`); so has a stat by a caller whose user
  namespace the tables do not hold, and a stat of an owner whose uid or
  gid in the tables is outside 0 to 4294967295 (no kernel id is,
  `include/linux/uidgid_types.h:7-13`).
- An rtnetlink handler can fail for lack of memory: `rtnl_newlink` with
  `-ENOMEM` (`net/core/rtnetlink.c`), `inet_rtm_newaddr` with `-ENOBUFS`
  (`net/ipv4/devinet.c`), and a link or address dump with `-ENOBUFS` when
  `__netlink_dump_start` cannot allocate the dump's first part
  (`netlink_dump`, `net/netlink/af_netlink.c`, v6.18.46). Linux still
  answers `sendto` with the request's length and reports the error inside
  the acknowledgement (`netlink_ack`). A change leaves the namespace
  unchanged. A dump keeps running: once the acknowledgement is read,
  `netlink_recvmsg` runs the dump again from its first part, so the
  dump's datagrams follow the acknowledgement. The namespace model admits
  that outcome (`Ns.Net.nl_handler_errnos`). Its effect is the answer's
  own, the request's length; only the state after the call, where the
  acknowledgement lives, shows the failure. The refusal filter
  (`Ns.Ext.ext_refusal`) is given the call's whole outcome, and under
  forced-only the namespace model's filter removes this outcome wherever
  the model also admits the answer without the failure
  (`Ns.Spec.ns_alloc_refusal`, `Ns.Net.nl_alloc_after`). Under may-fail
  it stays.
- A loopback device can come up without its address. When `lo` comes
  up, `inetdev_event` adds 127.0.0.1/8 only if `inet_alloc_ifa` can
  allocate it (`net/ipv4/devinet.c`, v6.18.46); otherwise the device is
  up with no address, and the request is still acknowledged with 0. The
  namespace model admits that outcome beside the one with the address
  (`Ns.Net.lo_up_noaddr`). It is an allocation failure whose effect is
  the success's own, so as above only the state after the call shows it:
  under forced-only the filter removes it and keeps the outcome with the
  address, and under may-fail both stay. `Ns.Net.nl_alloc_after` gives
  the kernel lines of both failures.
- A write to a tmpfs file can stop short. When a later page of the write
  cannot be allocated or read, `generic_perform_write` (`mm/filemap.c`,
  v6.18.44) returns the bytes it has already written, a count that ends
  on a page boundary (`Ns.FsOps.write_short`). A count is no refusal, so
  forced-only keeps it too.
- The launch left `SIGPIPE` at its default disposition, and the
  statements say which launch they mean rather than assuming one. On
  Linux a write to a pipe or a socket whose reader has gone raises
  `SIGPIPE` and the default action ends the program — as in
  `fuzz_target input | true`, once `true` has exited (`anon_pipe_write`,
  `fs/pipe.c`, and `sk_stream_error`, `net/core/stream.c`, Linux
  v6.18.46, commit `1f99e9ab748f`). **The model gives that ending on a
  launch that declares it** (`State.with_killed`, `Run.sstep_killed`;
  the declaration is `State.in_sigpipe_terminal`, and
  `Run.valid_input_sigpipe_kills` and `Run.valid_input_channel_closed`
  set it). `Run.valid_input` pins it OFF: there a write that would
  raise `SIGPIPE` at `SIG_DFL` declines, whatever the mask, so no run
  under the ordinary statements ends by signal 13 and every error-free
  statement keeps the meaning it had before the write arms could raise
  the signal; the declined write is an error. Which world a statement is
  about is a declared field, `State.in_sigpipe_default`: `Run.valid_input`
  pins it to the default disposition, and `Run.valid_input_sigpipe_ignored`
  is the launch that ran `signal(SIGPIPE, SIG_IGN)` before `execve` — a
  disposition `execve` preserves (`begin_new_exec` calls
  `flush_signal_handlers` with `force_default = 0`, `fs/exec.c`) — under
  which the same write returns `-EPIPE` and the program runs on. **The
  shape of the reader is declared too, and pinned**:
  `State.in_channel_reader` is a launch fact with one value for the
  whole run, and `Run.valid_input` pins it present — the run whose
  standard output is read throughout — so the ordinary statements are
  about that launch and no other. The reader-gone launch has its own
  name, `Run.valid_input_channel_closed`, in the shape
  `Run.valid_input_abort` has for the abort declaration, and a
  statement that means both readings asks for
  `Run.valid_input_channel_either`. The model pins the reader, and
  names the reader-gone launch so a proof can ask for it, the shape
  the abort declaration already has.
  A reader that goes away PART WAY
  through the output is a third thing the model has no term for, and a
  program whose reader goes away mid-output is outside the model.
- No write to a regular file fails. The model has no `ENOSPC`, `EDQUOT`
  or `EIO` out of the page cache (the write arm of
  `Sys/Fs/ReadWrite.v`). The one failure `write` injects is not a
  regular file's: `Run.injected_table` carries syscall 64 under the
  `fs` family with `ReadWrite.write_errnos` = `[ENOMEM]`, which is the
  page a write into an EMPTY pipe must allocate (`anon_pipe_get_page`,
  `fs/pipe.c`). A write that merges into a pipe's existing page, and
  every write to a file, a channel or `/dev/null`, allocates nothing
  and cannot reach it.
- `mmap_min_addr` is 4096. The model declines only the address 0, because
  `cap_mmap_addr` rejects nothing else at that setting
  (`Sys/Mm/Mmap.v`, the `-EPERM` note). With a larger setting, Linux
  answers `-EPERM` for a fixed mapping below it, and the model admits
  the mapping. Linux takes the larger of the `vm.mmap_min_addr` sysctl and
  `CONFIG_LSM_MMAP_MIN_ADDR` (`security/min_addr.c`,
  `update_mmap_min_addr`). That option depends on SELinux and its default
  is 65536 (`security/Kconfig`, `LSM_MMAP_MIN_ADDR`). A kernel built with
  SELinux, which the riscv64 defconfig is, therefore has
  `mmap_min_addr` = 65536 and is outside this assumption.
- The vDSO and the vvar mapping are the first pair that the kernel places
  below the mmap base, with the vvar part lower. Linux installs them at
  `execve` after it maps the segments: `load_elf_binary` calls
  `ARCH_SETUP_ADDITIONAL_PAGES` (`fs/binfmt_elf.c`), and
  `__setup_additional_pages` (`arch/riscv/kernel/vdso.c`) asks
  `get_unmapped_area` for the two parts together, then installs the vvar
  part at the result and the text part above it. The model's ledger now
  carries the pair at that position (`State.vdso_reserved`,
  `State.init_model`), so it does not assume such a call away: a `munmap`,
  a fixed `mmap` or an `mremap` whose range meets the pair gets
  `unmodeled` (`Sys/Mm/Mmap.v`, `munmap_spec`), which is the model's
  fail-closed answer and not Linux's answer.
- The kernel build's vDSO text is 1 to 16 pages. The model reads the count
  from the kernel build in its input (`State.vdso_text_pages`), and the
  vvar part is always 4 pages (`arch/riscv/include/asm/vdso.h`,
  `__VDSO_PAGES`, which `__setup_additional_pages` holds `VDSO_NR_PAGES`
  to). A build with a larger vDSO text puts the pair, and each placement
  below it, lower than any model state does.
- The memory budget is a strict per-process commit limit. The model
  meters anonymous backing against `State.vm_limit` and forces a
  refusal once a request would pass it (`Sys/Mm/Mmap.v`,
  `mmap_noreserve_backed_ok` and `brk_budget_ok`). Linux accounts that
  way only under `vm.overcommit_memory` = 2, `OVERCOMMIT_NEVER`, where
  `__vm_enough_memory` (`mm/util.c`) tests the request against
  `vm_commit_limit()`. The default is `OVERCOMMIT_GUESS` = 0
  (`sysctl_overcommit_memory` in the same file), under which a request
  fails only when it alone passes `totalram_pages() + total_swap_pages`,
  and `OVERCOMMIT_ALWAYS` = 1 never fails. The model holds neither the
  machine's memory nor its commit limit, so its budget is a parameter of
  the run (`Run.mi_alloc_limit`) and not a reading of any of those
  settings. Each refusal the budget forces is also admissible under the
  errno `alt` of its arm, so the budget narrows which runs a statement
  covers rather than claiming an answer Linux does not give.
- The process uses the top-down mmap layout. The process does not have
  the `ADDR_COMPAT_LAYOUT` personality (`setarch -L`), and
  `vm.legacy_va_layout` is 0. (An unlimited `RLIMIT_STACK` also selects
  the legacy layout; see "Stack limit" above.) In the legacy layout
  Linux puts the mmap base at `TASK_UNMAPPED_BASE` (0x2aaaaab000) plus
  the random offset. That base can be below the floor of
  `Run.valid_mmap_base`, and then the model has no start state for that
  launch.
- The stack guard gap is at most 0x4aba6a2ab000 bytes (about 74.7 TiB;
  the `stack_guard_gap` boot parameter gives the gap in pages, so this
  is 0x4aba6a2ab pages). `State.stack_guard_gap_bytes` states the bound
  by construction, so every value of `State.KernelBuild`'s `kb_guard`
  names a machine the model describes, with any `vm.mmap_rnd_bits`.
  Under Sv48 and Sv57, below that bound, `mmap_base` never clamps the
  gap at `STACK_TOP / 6 * 5`, and the mmap base never falls below the
  floor of `Run.valid_mmap_base`: with 33 bits and the largest gap the
  lowest base is exactly `State.mmap_base_min`. A larger gap can put
  the base below that floor, and the model then has no start state for
  the launch. A guard gap within about 1 GiB of 2^64 bytes wraps the
  kernel's arithmetic, and the mmap base can then lie above the bottom
  of the stack; the bound excludes that too.
- `execve` loads the binary directly, not through `binfmt_misc` and not
  as a script. `bprm->have_execfd` is then 0, so the auxv carries no
  `AT_EXECFD`, `AT_FLAGS` is 0, and the exec file name is the one the
  caller passed (`fs/exec.c`, `alloc_bprm`).
- The launch is not a secure exec. The binary has no set-user-id bit,
  no set-group-id bit and no file capability, and no LSM asks for
  secure mode (`cap_bprm_creds_from_file` in `security/commoncap.c`,
  `security/selinux/hooks.c`). `AT_SECURE` is therefore 0. The model
  also cannot express such a launch: `State.ProcInput` has no effective
  id, so `State.init_model` derives the effective and saved ids from
  the real ones.
- The process runs in the initial user namespace with default
  securebits, a capability bounding set that holds `CAP_SETUID` and
  `CAP_SETGID`, no ambient capabilities and a binary without file
  capabilities, and the exec that started it was not unsafe
  (`check_unsafe_exec`, `fs/exec.c`): no tracer, no `no_new_privs`, and
  no `fs_struct` shared with another process. The rest of the bounding
  set may be narrowed, as a container narrows it (Docker's default set
  holds 14 capabilities, these two among them). The only security
  module that answers the credential and capability hooks is the
  capability module. Under these, a process holds `CAP_SETUID` and
  `CAP_SETGID` in its effective set exactly when its effective uid is
  0, and its permitted set is empty exactly when none of its uids is 0
  (`security/commoncap.c`, `cap_bprm_creds_from_file` and
  `cap_emulate_setxuid`). The model reads privilege from the effective
  uid (`State.creds_privileged`). `capget` reports the empty sets of a
  caller with no uid 0 and is `unmodeled` for a caller with one, and
  `prctl(PR_CAPBSET_READ)` answers 1 for these two capabilities and 0
  or 1 for the others (`Kernel.Capability`, `Kernel.Sys.prctl_spec`).
  SELinux and AppArmor can refuse or narrow these answers.
- The machine has one view of its caches. `get_cacheinfo`
  (`arch/riscv/kernel/cacheinfo.c`) reads the CPU that runs the
  `execve`, and `State.KernelBuild` holds one `State.CacheView`. The
  kernel's own comment says the interface assumes a homogeneous view.
- A file system limits each name component, for example to 255 bytes on
  ext4 and 1024 on FUSE. `Run.valid_execfn` bounds the whole name and
  does not look at components, so it admits an exec file name that some
  file system refuses.
- The file that `AT_EXECFN` names holds the image. On Linux the name
  resolves to the file `execve` loaded. The model holds the image's
  segments, not its file, so `State.in_fs` need not hold a file at that
  name and a program that opens its own `AT_EXECFN` gets the file
  system's answer.
- The vDSO image of the kernel that launched the process is one of the
  measured images in `Vdso.vdso_images`. The model holds the bytes of
  one `vdso.so` per kernel build it describes, read out of a build this
  project made; `measure/MEASUREMENT.md` records which build, with which
  toolchain, and how the bytes and the symbol offsets were read. A
  kernel whose image is not in the list has no `State.kb_vdso` value, so
  no statement says anything about it. The entry of this list today is
  the riscv64 `defconfig` build of v6.18.46 (two text pages, 5704
  bytes, sha256 `0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39ca
  b23958df36`); the same kernel with `CONFIG_TRANSPARENT_HUGEPAGE=y`
  gives the same bytes.
- A vDSO function keeps the callee-saved registers and `sp`, and writes
  no memory but its own frame below `sp` and the buffers its arguments
  point at. The psABI requires this of a compiled function, and
  `measure/MEASUREMENT.md` records the check against the measured
  image's disassembly. The model does not re-check it for an image
  added later.

## Known gaps in precision

Design priority 2 asks that the model include no behavior that Linux
v6.18.46 does not give. The model does not meet it in these cases. In each
case, a statement that compares sets of behaviors (for example,
equivalence) can be true of the model and false of Linux.

- **No parameter for the Linux configuration.** The model does not choose
  between Linux configurations (for example, the two mmap layouts). Where
  they differ, the model lets each system call choose again. A real system
  makes the choice the same way each time. Also, the source and the target
  can make different choices, as if they ran on different machines.
  "Assumptions that the model does not check" above pins each
  configuration the model does fix. This holds for the system calls. It
  does not hold for the start state: the launch's randomisation mode, its
  guard gap, its `vm.mmap_rnd_bits`, its `CONFIG_RSEQ`, its vector unit,
  its caches and its vDSO image are fields of `State.KernelBuild`, which
  the two binaries of a pair share, so there the model does carry a
  parameter for the machine and both binaries read the same one.
- **`F_GETFD` and the close-on-exec bit.** The model records no
  close-on-exec bit, so `fcntl` `F_GETFD` answers 0 or `FD_CLOEXEC` on
  every descriptor. Linux answers the one value set by the call that
  created the descriptor or by its last `F_SETFD`
  (`do_fcntl`, `fs/fcntl.c:465-467`, v6.18.46). A program that branches
  on the bit has both branches admitted.
- **Errors of a namespace `clone`.** For the namespace flag word
  (`Kernel.Fork.clone_ns_flags_b`) the model admits every errno from 1 to
  4095 but `-EINTR`. The failures run through `create_user_ns`,
  `copy_namespaces` and every per-namespace init function, including
  each network namespace's pernet init, and they cannot be listed with
  confidence. Linux gives only some of them. `kernel/fork.c`'s
  `fatal_signal_pending(current)` `-EINTR` path ends the task before it
  returns; the signal-pending assumption above excludes the other
  interrupt paths.
- **The status word of a reaped child.** `wait4` lets the environment
  choose the status word of the child it reaps from two shapes: an exit,
  `(code & 0xff) << 8`, and a death by a signal 1 to 64, with or without
  the core-dump bit 0x80 (`Kernel.Exit.wait_status_okz`). Linux kills
  only by a signal whose action is fatal (under the default actions,
  SIGSTOP stops and SIGCHLD and SIGCONT are ignored), and sets the core
  bit only for a signal whose default action dumps core
  (`coredump_finish`, `fs/coredump.c`, v6.18.44; identical at v6.18.46).
- **The eventfd counter.** A non-blocking `read` of an eventfd may
  deliver any nonzero value (exactly 1 under `EFD_SEMAPHORE`) or answer
  `-EAGAIN` at each call, and a non-blocking `write` may answer 8 or
  `-EAGAIN`, independently of every earlier call. Linux answers from
  one counter that the program's own reads and writes move; the model
  holds that counter as the environment's because other processes
  share it.
- **The `/proc/self/fd` listing.** `d_ino` of every record is the
  environment's, and so is the choice of `DT_UNKNOWN` with `d_ino` 1 for
  a descriptor (what `proc_fill_cache` writes when it cannot get a
  dentry) in place of `DT_LNK`. The position at the end of the listing is
  any value above every open descriptor and at most 2^31 + 2; Linux
  gives one value, `max_fds + 2`, the same on each call. `fstat` on the
  directory pins the type and the mode only.
- **The inheritable capability set.** `capget` lets the environment
  choose the inheritable set on each call, within the valid bits. Linux
  gives the same set on each call until it changes, and 0 after an
  answered `capset`.
- **The capability bounding set.** `prctl(PR_CAPBSET_READ)` chooses 0
  or 1 again on each call for every valid capability other than
  `CAP_SETUID` and `CAP_SETGID`. Linux gives the same bit on each call:
  no modeled call changes the bounding set (`PR_CAPBSET_DROP` is
  `unmodeled`). Also, the model admits 1 for a capability a container's
  set lacks, and 0 for one a full set holds.
- **Clock resolution.** For supported non-CPU clock IDs, `clock_getres`
  accepts any positive nanosecond value below one second. Linux returns
  1 ns or a tick-based resolution (`posix_get_hrtimer_res` and
  `posix_get_coarse_res`, `kernel/time/posix-timers.c`), and which of the
  two, and the value of `hrtimer_resolution`, follow the kernel build and
  the boot (`CONFIG_HIGH_RES_TIMERS`, `CONFIG_HZ`). The model does not
  constrain later calls to use the same resolution.
- **R-a, an mmap base above `State.alloc_top`.** The model's stack window is
  `[sp - 8 MiB, sp)`. Linux measures its 8 MiB from the end of the stack
  VMA, which is above `sp` by the entry image. With an entry image of more
  than about 1 MiB and a high base draw, Linux's `mm->mmap_base` can lie
  above `State.alloc_top`, while the model searches below `alloc_top`. The
  model's top-down addresses are then lower than Linux's by at most the
  entry image size less 1 MiB. The refusals differ only when no free range
  of the requested size is left. It stays open because the model counts
  only its own entry image against the stack limit (see "Stack floor").
  LPS pull request #25, which makes the stack window count the entry
  image, makes `alloc_top` Linux's floor and closes it.
- **R-b, a hint or a fallback above `State.alloc_top`.** Linux honours a
  free address hint anywhere up to `STACK_TOP_MAX`, which is 2^47, the band
  above the stack included, and its bottom-up fallback searches up to the
  same limit, which reaches the guard gap below the stack (`mm/mmap.c`,
  `generic_get_unmapped_area_topdown`: the hint test is
  `mmap_end - len >= addr` with the two gap tests, and the fallback sets
  `info.high_limit = mmap_end`; `arch/riscv/include/asm/processor.h`,
  `arch_get_mmap_end`, which gives `STACK_TOP_MAX`). The model honours a
  hint, and searches, only below `State.alloc_top`. It stays open because
  the dynamic stack is a bound in this model and not an entry in the
  ledger, so the model cannot tell a free address above the stack from the
  stack itself. The stack VMA in the ledger closes it.
- **R-c, the stack guard gap.** When the stack has grown to its limit,
  Linux keeps a mapping `stack_guard_gap` below it: the search subtracts
  that gap from the start of a `VM_GROWSDOWN` VMA
  (`include/linux/mm.h`, `vm_start_gap`, through `stack_guard_start_gap`;
  `vm_end_gap` is the matching rule above a `VM_GROWSUP` VMA). The model
  allows a mapping there when the mmap base or a hint reaches
  `State.alloc_top`. It stays open for the reason R-b gives: the ledger has
  no stack VMA, so it has no gap to keep. The stack VMA in the ledger
  closes it.
  The same gap reaches `brk`: Linux refuses a grow to within a page and
  `stack_guard_gap` of the stack's start, because the `vma_find` at
  `SYSCALL_DEFINE1(brk)` (`mm/mmap.c`) searches up to
  `newbrk + PAGE_SIZE + stack_guard_gap` and compares against
  `vm_start_gap(next)`. `Sys/Mm/Mmap.v`, `brk_grow_ok` tests only the
  installed pages and the one page above them, against a ledger with no
  stack VMA in it, so `State.alloc_top` stands in for that refusal — and
  stands in for it only while the stack has not grown to within
  `stack_guard_gap` and a page of that bound. The stack VMA in the
  ledger closes this too.
- **What a vDSO call leaves behind.** After a call to an exported vDSO
  entry, the caller-saved registers other than `a0`, and the bytes of
  `[sp - F, sp)`, take the values of the launch's draw
  (`StackLayout.ed_vdso`), not the values the vDSO's own code wrote.
  `F` is the chosen image's largest measured frame (240 bytes for the
  image in the list). So the model admits leftovers that no image
  leaves. Because the draw reads the state before the call, one of its
  choices is Linux's, and for a statement that must hold at every entry
  the extra choices cost precision only: a program that reads a
  leftover — an uninitialized local in the next call's frame, say — has
  no proof that depends on the value. Every other byte below `sp` keeps
  its value, and `sp`, `gp`, `tp` and `s0`-`s11` keep theirs.
- **Which route a clock reading takes.** Linux's vDSO answers a
  `CLOCK_MONOTONIC` reading from the vvar time data when the clock
  source has a vDSO mode, and makes system call 113 otherwise
  (`__cvdso_clock_gettime_common`, `lib/vdso/gettimeofday.c`). The
  model has no term for the clock source, so it answers both routes
  with `PosixTimers.clock_gettime_spec` and lets the environment choose
  the time, as it does for the system call. A real run's two routes
  give the same reading; the model lets them differ.
- **`munmap` failures.** An `munmap` that unmaps pages can answer
  `ENOMEM` at every call, and under a reading that admits only the
  failures the state forces it can answer `ENOMEM` at no call. On Linux
  the answer depends on kernel memory, which the model does not hold.
  The call that unmaps pages goes to `do_vmi_align_munmap`
  (`mm/vma.c`, Linux v6.18.46). That function clears the range in the
  mapping tree with `vma_iter_clear_gfp` (`include/linux/mm.h`), which
  answers `-ENOMEM` when the tree cannot get a node, and
  `vms_gather_munmap_vmas` has the same failure in `mas_store_gfp` one
  step earlier. Both are before the point of no return, and both
  re-attach what they detached (`reattach_vmas`), so the mapping keeps
  its pages. The model gives the same two answers, under an `alt`, for
  an unmap of one whole mapping and for a partial unmap. A range with
  no mapped pages keeps its single answer 0: Linux returns there in
  `do_vmi_munmap` (`mm/vma.c`) before any allocation.
- **Random bytes.** The bytes of `/dev/urandom` are an input
  (`State.ProcInput.in_urandom`): the source and the target see the same
  stream. The bytes of `getrandom` are a free choice at each call: the source
  and the target choose them independently. Thus "equivalent" means a
  different thing for each API. Two programs that print the same random
  bytes in a different order are equivalent if both use `getrandom`, but not
  if both use `/dev/urandom`. A program that uses `/dev/urandom` and one
  that uses `getrandom` for the same work cannot be proved equivalent.
- **Short writes to a channel.** A write to a channel delivers a nonempty
  prefix of the readable bytes, of the environment's choosing. For a
  blocking pipe write of at most `PIPE_BUF` (4096) Linux delivers all of
  it or fails, so the positive short return that the model admits here is
  a behavior no supported system gives. The write arm of
  `Sys/Fs/ReadWrite.v` names it a known soundness gap. The model
  classifies fds 1 and 2 as channels without knowing whether the far end
  is a pipe, a terminal or a file, so it admits the short return for all
  three.
- **A channel with no reader — fixed, and what it cost.** This used to
  be a gap: the write arm could not see whether fds 1 and 2 still had a
  reader, so a write to a stdout whose reader was gone got a count,
  where Linux raises `SIGPIPE` and kills the process. The model now has
  a death that is not an exit, and the launch says which case it is
  (`State.ProcInput.in_channel_reader`). `Run.valid_input` pins that
  field present, so every ordinary statement is about the run whose
  standard output is read; the writing end of `prog | head -1` is
  `Run.valid_input_channel_closed`, named the way
  `Run.valid_input_abort` names the aborting launch, and a statement
  that means both readings asks for `Run.valid_input_channel_either`:
  the model pins the reader, and names the reader-gone launch so a
  proof can ask for it.
  What is left is NOT the
  SIGPIPE disposition: that was an unstated premise and is now a
  declaration (`State.ProcInput.in_sigpipe_default`, pinned to
  `SIG_DFL` by `Run.valid_input`, with
  `Run.valid_input_sigpipe_ignored` for the launch that ignored the
  signal; see "Signals"). What is left is that the model has ONE answer
  per run: a reader that goes away at a point the model can see is not
  expressible, so a program whose reader goes away in the middle of its
  output is outside the model.
- **A socket write that delivers.** A write to a socket with no
  connection is answered — `-EPIPE`, and the `SIGPIPE` that goes with
  it (`net/core/stream.c`, `sk_stream_wait_connect` and
  `sk_stream_error`). A write to a CONNECTED socket is still
  `unmodeled`: it would have to choose a short count, or consume a
  pending peer error and rewrite the descriptor, which is
  `sendto`/`sendmsg`'s machinery. So `write(2)` on a socket is covered
  exactly where the connection is absent.
- **After a vDSO call.** The model does not run the vDSO's
  instructions. It applies the exported function's system-call
  specification in one step, so the caller-saved registers other than
  `a0`, and the bytes of the frame the call used below `sp`, are the
  entry's own `StackLayout.ed_vdso` choice. One of those choices is
  what the real image leaves, so for a statement that must hold at
  every entry the other choices cost precision only. For a statement
  with "there is an entry" they can cost soundness, as any extra start
  state can.
- **The vvar pages, other fetches in the vDSO text, and a vDSO call
  that would return `-EFAULT`** are `unmodeled`. The model has no bytes
  for the vvar pages and does not run the vDSO's code.
- **Stack floor.** `Run.init_machine_state` lays the entry block from
  the entry `sp` up to the stack VMA's end `StackLayout.ed_top`, and
  below `sp` it zero-maps the window `[Run.stack_window_lo, sp)`.
  `Run.stack_window_lo` is the higher of `ed_top - 8 MiB` and the mmap
  base plus the stack guard gap. Both are Linux's own floors at entry:
  `expand_downwards` (`mm/vma.c`, Linux v6.18.46) passes
  `size = vm_end - address` to `acct_stack_growth`, which answers
  `-ENOMEM` when `size` passes `RLIMIT_STACK`, and `expand_downwards`
  also refuses to grow within `stack_guard_gap` of the mapping below,
  which at entry is the vDSO text directly below the mmap base. The
  model carries `ed_top` as part of the entry, so this floor is exact
  at entry and there is no band.
  A mapping that the program makes later can raise Linux's floor, and
  the model's ledger does not raise the stack window with it. That is
  the residual: a program that maps a page just below its stack and
  then grows the stack into the guard gap above that mapping faults on
  Linux where the model answers.
  QEMU user mode has a band of the same kind, for a different reason;
  "Where QEMU user mode differs" above says where the guest stack goes.
- **A failing store-conditional on a write-only segment.** The model
  writes the failing `sc`'s permission check as a load and a store of
  the same bytes, so on a writable segment that lacks the `r` flag it
  faults, as a load from that segment already does
  (`RiscvSemantics.memory_read`). Linux on riscv maps every writable
  page readable (`arch/riscv/mm/fault.c`, `access_error`: "Write
  implies read"), so there both the load and the failing `sc` succeed.
- **Contents under /proc, chosen afresh.** The bytes a `read` of either
  modeled `/proc/sys` leaf and the 128 bytes a `newfstatat` relative to
  an O_PATH procfs descriptor delivers are the environment's choice at
  each call, as `getrandom`'s are: nothing pins a second read to the
  rest of the first one's text, or two stats of one namespace to one
  inode number. The source and the target choose them independently.
- **Every procfs name opens.** An O_PATH open is admitted for every
  procfs name but one (below), including a pid that does not exist and a
  name that is a link out of procfs ("/proc/self/root/etc"), and the procfs arms admit
  every errno from 1 to 4095 but `-EINTR` (`Syscall.errno_any`), because their errnos
  run through procfs's own lookups and the LSM hooks and cannot be
  listed with confidence. Nothing the model does with an `OProcPath`
  descriptor reads the object it names, so this costs precision only.
  The one open that does read what it reaches, "/proc/self/fd"
  (`State.OProcFdDir`), is not widened this way: it is answered only
  for the absolute name and for "self/fd" relative to an O_PATH
  descriptor on "/proc" itself (`Open.proc_open_target`). The name "fd"
  relative to a descriptor on "/proc/self" is `unmodeled` for every flag
  word, O_PATH included, because an `O_PATH|O_NOFOLLOW` open of
  "/proc/self" holds the symlink, from which Linux answers `-ENOTDIR`.
- **`kill` to the caller and the LSM.** An enabled LSM can answer
  `-EPERM` to `kill` even for a signal to the caller itself
  (`security_task_kill`, `kernel/signal.c:832`). The model answers
  instead, as it does for `tkill`.

## What the proofs do not check

- The executable checker of each system call is proved to agree with its
  specification. This does not show that the specification agrees with
  Linux. An error in both gives a correct proof of the wrong thing.
- Comments that state kernel behavior name the file and the function in
  Linux v6.18.46. No tool checks that these comments are correct.
