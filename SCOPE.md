# Scope, assumptions and known gaps

Read this document before you use a proof as evidence about a real program.
It tells you which system the model describes, where the model is narrower
than that system, which assumptions it does not check, where it is less
precise, and where a run under QEMU user mode is not a Linux run. The
design priorities in [README.md](README.md#design-priorities) refer to
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

- **Where a new mapping goes.** The model gives the address Linux
  v6.18.46 gives: the hint if the hint is free, else the highest free
  range below `mm->mmap_base`, else the lowest free range from
  `TASK_UNMAPPED_BASE` up (`mm/mmap.c`, `__get_unmapped_area` and
  `generic_get_unmapped_area_topdown`; `mm/vma.c`, `unmapped_area_topdown`
  and `unmapped_area`; the model is `Sys/Mm/Mmap.v`, `linux_place`). QEMU
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
complete. A replay of 4,291 recorded traces (19,693 judged system calls)
through extracted checkers found twelve system calls where the model
answers and an older tree declines; each of the twelve was read against
v6.18.46 and the model answers Linux's at every one.

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

| Area | Limit |
| --- | --- |
| Threads | The model has one thread. It has no scheduler and no shared-memory interleaving. For `fork`-like calls, the model describes the parent only. It does not run the child. |
| Signals | The model does not run signal handlers. |
| Address-space size | The system call specifications use Sv48. Thus you cannot prove the Sv39 and Sv57 statements for an image that can run. |
| Stack limit | The stack limit is 8 MiB. A larger or unlimited `RLIMIT_STACK`, which selects the legacy mmap layout, is outside the model. The model counts its own entry image against this limit, but not the parts of a real entry image that it leaves out; see "Stack floor" in "Known gaps in precision". |
| Arguments | `Run.valid_input` requires that the arguments after `argv[0]` do not contain `/` and are not `..`. Thus a proof about `cp src dst` does not apply to `cp /tmp/src dst`. It also bounds the lists (`Run.valid_argv`, `Run.valid_envp`): 1 to 1024 arguments and at most 2 MiB of argument bytes, at most 256 environment variables and at most 128 KiB of environment bytes, and at most 131071 bytes in each string. Each count of bytes includes the terminating NUL of each string. A launch outside these bounds is outside the model. |
| Standard input and output | The fds 0, 1 and 2 are external channels, and their direction is fixed: 0 is read-only, 1 and 2 are write-only (`State.FdChannel`). The model answers `-EBADF` for the other direction. Thus a proof says nothing about a program that is handed a connected socket on fd 0, as an inetd-style server is. |
| Network | The list of connections is never empty. Thus the model does not include an environment where no peer ever connects. |
| Memory budgets | The source can allocate 16 GiB and the target 512 GiB (`State.source_alloc_limit`, `State.target_alloc_limit`). The `*_budgets` statements change this premise. The `*_budgets_only` statements have a finer premise for the source: it excludes a first-touch or a cumulative refusal, but not a single request that is larger than the whole budget (`Run.alloc_refuse_reason`). |
| Files | The file model has no full directory tree, no symbolic links, no device files except `/dev/null` and `/dev/urandom`, and no permissions. |

The entry premises also limit the launches that a statement covers.
`Run.valid_sp` requires an entry stack pointer in the top 2 GiB of the
Sv48 user address space (`State.sp_window_lo` to `State.sp_window_hi`).
On Linux with Sv48 or Sv57, the pointer stays in this window for each
stack limit, with address randomisation on or off (`randomize_stack_top`
in `mm/util.c`, `setup_arg_pages` in `fs/exec.c`). The statements say
nothing about a launch that puts the pointer below the window. QEMU user
mode does put it below the window in three of four cases; "Where QEMU
user mode differs" has the measurements.

The model also builds its own auxiliary vector, with ten entries
(`StackLayout.auxv_entries`). Linux publishes more entries. Thus a
program can see a different vector in the model than on a real launch.
This occurs when the program reads an entry that the model omits, or
reads the whole vector in sequence. "The auxiliary vector" in "Known
gaps in precision" names the entries.

## Assumptions that the model does not check

If one of these assumptions is false, a proof can be correct but it does
not apply.

- No other process, also not a child of the program, changes the modeled
  files or holds locks on them.
- `/dev/null` is the null device (major 1, minor 3). `/dev/urandom` is the
  random device (major 1, minor 9).
- No tracer (`ptrace`) or other outside agent changes the process.
- The binary is a static executable (`ET_EXEC`). `elf-snapshot` does not
  check this. For a static PIE, the model can give a wrong initial program
  break.
- At launch the process has no children and no tracees. The model takes
  `-ECHILD` from `wait4` and `waitid` only while no modeled `clone` has
  recorded a child (`State.m_has_children`, the comment at the head of
  `Sys/Kernel/Exit.v`). `execve` does not reap a child in Linux, so a
  launcher that forks a grandchild, or attaches a tracee, before it
  execs the image makes this assumption false.
- No write to a regular file fails. The model has no `ENOSPC`, `EDQUOT`
  or `EIO` out of the page cache (the write arm of
  `Sys/Fs/ReadWrite.v`). The table of injected failures
  (`Run.injected_table`) carries one arm for `write`, and it is the
  `-ENOMEM` of the page a write to an empty pipe allocates
  (`anon_pipe_write`, `fs/pipe.c`); no arm of it reaches a regular file.
- `mmap_min_addr` is 4096. The model declines only the address 0, because
  `cap_mmap_addr` rejects nothing else at that setting
  (`Sys/Mm/Mmap.v`, the `-EPERM` note). With a larger setting, Linux
  answers `-EPERM` for a fixed mapping below it, and the model admits
  the mapping.
- No `munmap` range meets the vDSO or the vvar mapping. Linux installs
  this pair at `execve`. The model's ledger carries neither
  (`Sys/Mm/Mmap.v`, the `munmap` arms), so the model answers such a call
  as if they were not there. Linux unmaps a mapping of the pair that the
  range covers whole. It refuses with `-EPERM` when the mapping is sealed
  (`CONFIG_MSEAL_SYSTEM_MAPPINGS`), and with `-EINVAL` when the range
  starts or ends inside it, because a special mapping cannot be split
  (`special_mapping_split`, `mm/mmap.c`). The model admits neither error.
- The process uses the top-down mmap layout. The process does not have
  the `ADDR_COMPAT_LAYOUT` personality (`setarch -L`), and
  `vm.legacy_va_layout` is 0. (An unlimited `RLIMIT_STACK` also selects
  the legacy layout; see "Stack limit" above.) In the legacy layout
  Linux puts the mmap base at `TASK_UNMAPPED_BASE` (0x2aaaaab000) plus
  the random offset. That base can be below the floor of
  `Run.valid_mmap_base`, and then the model has no start state for that
  launch.
- `vm.mmap_rnd_bits` is at most 24, or the stack guard gap is at most
  0x4aba6a2ab000 bytes (about 74.7 TiB; the `stack_guard_gap` boot
  parameter gives the gap in pages, so this is 0x4aba6a2ab pages). The boot
  value of `vm.mmap_rnd_bits` is `CONFIG_ARCH_MMAP_RND_BITS`, which is
  18 to 24 on riscv64. Root can set it to at most 33 under Sv48. With 33
  bits and a larger guard gap, Linux can put the mmap base below the
  floor of `Run.valid_mmap_base`. With fewer bits the guard gap must be
  larger for that (about 106.6 TiB at 25 bits). With the default guard
  gap (256 pages), 33 bits keep the base in the band. Under these two
  assumptions the band is exactly the set of bases that Linux gives
  (`Checks.Cases.MmapBase.sv48_band_is_linux_set`). A guard gap within
  about 1 GiB of 2^64 bytes wraps the kernel's arithmetic, and the mmap
  base can then lie above the bottom of the stack. Linux can then place a
  mapping where the model refuses it (`State.alloc_top`), so a proof says
  nothing about a process with such a guard gap.

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
  configuration the model does fix.
- **Clock resolution.** For supported non-CPU clock IDs, `clock_getres`
  accepts any positive nanosecond value below one second. Linux returns
  1 ns or a tick-based resolution (`posix_get_hrtimer_res` and
  `posix_get_coarse_res`, `kernel/time/posix-timers.c`), and which of the
  two, and the value of `hrtimer_resolution`, follow the kernel build and
  the boot (`CONFIG_HIGH_RES_TIMERS`, `CONFIG_HZ`). The model does not
  constrain later calls to use the same resolution.
- **mmap placement.** A mapping without an address hint can go to any free,
  page-aligned address below `State.alloc_top`. This is wider than the
  placement policy of each supported system.
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
- **A channel with no reader.** The same arm cannot see whether the
  channel still has a reader. A write to stdout or stderr whose reader is
  gone gets a count. Linux raises `SIGPIPE`, which kills the process, or
  answers `EPIPE`.
- **The auxiliary vector.** The model publishes ten entries
  (`StackLayout.auxv_entries`). A real kernel also supplies `AT_GID`,
  `AT_EGID`, `AT_BASE`, `AT_ENTRY`, `AT_FLAGS`, `AT_CLKTCK`, `AT_EXECFN`
  and, from riscv's `ARCH_DLINFO`, `AT_SYSINFO_EHDR`, the
  cache-descriptor entries and `AT_MINSIGSTKSZ` (or `AT_IGNORE`), and
  with `CONFIG_RSEQ` also `AT_RSEQ_FEATURE_SIZE` and `AT_RSEQ_ALIGN`,
  which this one leaves out. Neither supplies `AT_PLATFORM`, because
  riscv's `ELF_PLATFORM` is `NULL`
  (`arch/riscv/include/asm/elf.h`). The 16
  bytes that `AT_RANDOM` points at are the highest bytes of the image,
  above the strings, where Linux puts them below the strings
  (`StackLayout.build_stack_bytes`). A libc reads the vector as a lookup
  table and sees no difference. A program that walks its own auxv, or
  that echoes the bytes around the `AT_RANDOM` block, has a modeled trace
  that its real trace does not match.
- **Stack floor.** `Run.init_machine_state` maps the entry image up to
  `Run.entry_page_top` and, below the entry `sp`, the window
  `[Run.stack_window_lo, sp)`. `Run.stack_window_lo` is
  `Run.entry_page_top - State.stack_max_size`, so the model counts its own
  entry image against the 8 MiB stack limit. Linux counts the whole
  stack VMA against `RLIMIT_STACK`, from its page-aligned top `vm_end`
  down: `expand_downwards` (`mm/vma.c`, Linux v6.18.46) passes
  `size = vm_end - address` to `acct_stack_growth`, which answers
  `-ENOMEM` when `size` passes the limit. That VMA holds the whole entry
  image: `do_execveat_common` (`fs/exec.c`) copies the exec filename and
  the argv and envp strings into it, `setup_arg_pages` (`fs/exec.c`)
  gives it its page-aligned top, and `create_elf_tables`
  (`fs/binfmt_elf.c`) writes `AT_RANDOM`, the auxv, `argc` and the
  pointers in it. So Linux never grows the stack below `vm_end - 8 MiB`.
  `vm_end` is at or above `Run.entry_page_top`, and can be pages higher,
  because the kernel's entry image carries more than the model's: the
  auxv entries of the bullet above, the exec filename, and the random
  pad of less than 4 KiB that `create_elf_tables` (`fs/binfmt_elf.c`)
  takes through `arch_align_stack` (`arch/riscv/kernel/process.c`).
  The separate call in `setup_arg_pages` adds nothing here: `PAGE_ALIGN`
  rounds its result back up, so that call moves the top by a whole page
  or not at all, and the same `stack_shift` moves the entry image with
  it. The model carries no `vm_end`.
  Thus the lowest `vm_end - Run.entry_page_top` bytes of the model's
  window, at most a few pages, are never stack on Linux.
  An access in that band succeeds in the model and faults on Linux, so
  a statement about a run whose stack reaches it
  can be true of the model and false of the real systems, and this one
  need not compare sets of behaviors: a single-run statement is enough.
  A program reaches the band only when its stack goes below
  `vm_end - 8 MiB`, which is at most a few pages above `Run.stack_window_lo`.
  The depth of the window below `sp` is `8 MiB - (Run.entry_page_top - sp)`,
  so it moves with the page offset of `sp` over a range of 4080 bytes. A
  program whose stack reaches a depth in that range faults under some
  stack addresses and not others, and a proof cannot show it equivalent
  even to itself. Linux's floor moves over a range of about the same
  size, through the pad above.
  QEMU user mode has a band of the same kind, for a different reason;
  "Where QEMU user mode differs" above says where the guest stack goes.
- **A failing store-conditional on a write-only segment.** The model
  writes the failing `sc`'s permission check as a load and a store of
  the same bytes, so on a writable segment that lacks the `r` flag it
  faults, as a load from that segment already does
  (`RiscvSemantics.memory_read`). Linux on riscv maps every writable
  page readable (`arch/riscv/mm/fault.c`, `access_error`: "Write
  implies read"), so there both the load and the failing `sc` succeed.

## What the proofs do not check

- The executable checker of each system call is proved to agree with its
  specification. This does not show that the specification agrees with
  Linux. An error in both gives a correct proof of the wrong thing.
- Comments that state kernel behavior name the file and the function in
  Linux v6.18.46. No tool checks that these comments are correct.
