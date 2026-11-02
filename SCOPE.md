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

| Area | Limit |
| --- | --- |
| Threads | The model has one thread. It has no scheduler and no shared-memory interleaving. For `fork`-like calls, the model describes the parent only. It does not run the child. |
| Signals | The model does not run signal handlers. It has two signals and both are fatal: `SIGABRT`, raised by `tkill`/`tgkill` on the abort path, and `SIGPIPE`, raised by a write whose far end has no reader. Each ends the run with a death that is not an exit (`State.KillEv`), or, where the launch mask blocks it, returns the errno and leaves the signal pending until a `rt_sigprocmask` uncovers it. `rt_sigaction` declines every install that would change either disposition, so no modeled call moves one. For `SIGABRT` the model assumes the launch left the disposition at `SIG_DFL`. For `SIGPIPE` it no longer assumes: the launch declares it (`State.in_sigpipe_default`), `Run.valid_input` pins the declaration to `SIG_DFL`, and `Run.valid_input_sigpipe_ignored` is the launch that ran `signal(SIGPIPE, SIG_IGN)` before `execve` — a launch `execve` preserves (`fs/exec.c`, `begin_new_exec`'s `flush_signal_handlers` with `force_default = 0`, Linux v6.18.46), under which the same write returns `-EPIPE` and the program runs on. No other signal is modeled: `SIGSEGV` is reported as the error transition rather than as a death, `SIGCHLD`'s default action is to ignore it, `SIGXFSZ` needs an `RLIMIT_FSIZE` the model does not carry, and nothing outside the process can send one. |
| Address-space size | The system call specifications use Sv48. Thus you cannot prove the Sv39 and Sv57 statements for an image that can run. |
| Stack limit | The stack limit is 8 MiB. A larger or unlimited `RLIMIT_STACK`, which selects the legacy mmap layout, is outside the model. The model counts the whole entry block against this limit, from the stack VMA's end `StackLayout.ed_top` down, as Linux counts it. |
| Arguments | `Run.valid_input` requires that the arguments after `argv[0]` do not contain `/` and are not `..`. Thus a proof about `cp src dst` does not apply to `cp /tmp/src dst`. It also bounds the lists (`Run.valid_argv`, `Run.valid_envp`): 1 to 1024 arguments and at most 2 MiB of argument bytes, at most 256 environment variables and at most 128 KiB of environment bytes, and at most 131071 bytes in each string. Each count of bytes includes the terminating NUL of each string. These are the model's own per-list bounds. Linux's own bound is joint, and `Run.valid_launch` carries it: the exec file name, the envp strings and the argv strings with their NULs, plus 8 bytes for each argv and envp pointer, are at most 2 MiB together at the 8 MiB stack limit (`bprm_stack_limits`, `fs/exec.c`). Linux answers `E2BIG` for a larger launch. `Run.valid_launch` also says which exec file names `execve` can present (`State.in_execfn`): a path of 1 to 4095 bytes without a NUL, or `/dev/fd/N`, or `/dev/fd/N/` and such a path that does not start with `/` (`getname_flags` in `fs/namei.c`, `alloc_bprm` in `fs/exec.c`). Both binaries of a pair run under the same exec file name, as they run on the same input. A launch outside these bounds is outside the model. |
| Standard input and output | The fds 0, 1 and 2 are external channels, and their direction is fixed: 0 is read-only, 1 and 2 are write-only (`State.FdChannel`). The model answers `-EBADF` for the other direction. Thus a proof says nothing about a program that is handed a connected socket on fd 0, as an inetd-style server is. |
| Network | The list of connections is never empty. Thus the model does not include an environment where no peer ever connects. |
| Memory budgets | The source can allocate 16 GiB and the target 512 GiB (`State.source_alloc_limit`, `State.target_alloc_limit`). The `*_budgets` statements change this premise. The `*_budgets_only` statements have a finer premise for the source: it excludes a first-touch or a cumulative refusal, but not a single request that is larger than the whole budget (`Run.alloc_refuse_reason`). |
| Files | The file model has no full directory tree, no symbolic links, no device files except `/dev/null` and `/dev/urandom`, and no permissions. |
| Shared memory | The model has no shared mapping. `mmap` with `MAP_SHARED` is `unmodeled`, anonymous requests included. Linux builds an anonymous shared mapping on a shmem file (`mm/vma.c`, `__mmap_new_vma` calls `shmem_zero_setup`), so `vma_is_anonymous` is false for it, its pages survive the zap that `MADV_DONTNEED` performs, and a `fork` shares them instead of copying them. `Sys/Mm/Mmap.v` gives the full reason and what an arm would take. |
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
- `/dev/null` is the null device (major 1, minor 3). `/dev/urandom` is the
  random device (major 1, minor 9).
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
- The launch left `SIGPIPE` at its default disposition, and the
  statements say which launch they mean rather than assuming one. On
  Linux a write to a pipe or a socket whose reader has gone raises
  `SIGPIPE` and the default action ends the program — as in
  `fuzz_target input | true`, once `true` has exited (`anon_pipe_write`,
  `fs/pipe.c`, and `sk_stream_error`, `net/core/stream.c`, Linux
  v6.18.46, commit `1f99e9ab748f`). **The model gives that ending**
  (`State.with_killed`, `Run.sstep_killed`), so a run under the ordinary
  statements can end by signal 13 rather than by `exit`, and a halts
  statement that only accepts an exit status is refuted by such a run
  rather than silently assuming it away. Which world a statement is
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

## What the proofs do not check

- The executable checker of each system call is proved to agree with its
  specification. This does not show that the specification agrees with
  Linux. An error in both gives a correct proof of the wrong thing.
- Comments that state kernel behavior name the file and the function in
  Linux v6.18.46. No tool checks that these comments are correct.
