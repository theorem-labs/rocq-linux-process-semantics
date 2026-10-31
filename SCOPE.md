# Scope, assumptions and known gaps

Read this document before you use a proof as evidence about a real program.
It tells you which systems the model describes, where the model is narrower
than those systems, which assumptions it does not check, and where it is
less precise than those systems. The design priorities in
[README.md](README.md#design-priorities) refer to this document.

## Supported systems

- Stable Linux v6.18.46 (commit `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`),
  on riscv64.
- QEMU user mode for riscv64.
- For instructions: the RISC-V specification (RV64GC).

Bugs in Linux or QEMU do not count.

Other stable kernels (v4.17 and later) are a goal. They are not supported
now. The model does not check claims about them.

In one case the model describes one supported system and not the other.
The LR/SC reservation survives a system call: `ecall` leaves `ms_resv`
as it is (`Run.apply_effect`, `Run.advance_past_svc`). QEMU user mode
keeps the reservation too. Linux clears it on each return to user mode
(`arch/riscv/kernel/entry.S`). Thus `lr; ecall; sc` has one outcome in
the model, and that outcome is QEMU's. A proof about such a sequence
says nothing about Linux.

A store-conditional (`sc.w`, `sc.d`) that fails still passes the
alignment check and the memory permission check (`Riscv/Sem.v`, the
`Sc` arm). The unprivileged specification requires a permission check
("No SC.W instruction shall retire unless it passes memory permission
checks"), the privileged specification (11.1.3.1) makes it a store's (a
store-conditional to a page without write permission raises a store
page fault), and Sail checks for a write. On a misaligned address, or on
memory the process may not write, the model faults. QEMU user mode
before commit `d107b748072c` ("target/riscv: Generate access fault if sc
comparison fails", 2026-04-29; 8.2.2 among them) skips both checks on a
failing `sc` and retires it with rd = 1. That is a QEMU bug, which this
model does not describe.

## Where the model is narrower

The statements restrict these cases, or the model says `unmodeled` for
them. A proof says nothing about a program in such a case.

| Area | Limit |
| --- | --- |
| Threads | The model has one thread. It has no scheduler and no shared-memory interleaving. For `fork`-like calls, the model describes the parent only. It does not run the child. |
| Signals | The model does not run signal handlers. It has two signals and both are fatal: `SIGABRT`, raised by `tkill`/`tgkill` on the abort path, and `SIGPIPE`, raised by a write whose far end has no reader. Each ends the run with a death that is not an exit (`State.KillEv`), or, where the launch mask blocks it, returns the errno and leaves the signal pending until a `rt_sigprocmask` uncovers it. The model holds no disposition for either: it assumes the launch left both at `SIG_DFL`, and `rt_sigaction` declines every install that would change one. A launcher that does `signal(SIGPIPE, SIG_IGN)` before `execve` is outside the model, because `execve` keeps an inherited `SIG_IGN` (`fs/exec.c`, `begin_new_exec`'s `flush_signal_handlers`, Linux v6.18.46). No other signal is modeled: `SIGSEGV` is reported as the error transition rather than as a death, `SIGCHLD`'s default action is to ignore it, `SIGXFSZ` needs an `RLIMIT_FSIZE` the model does not carry, and nothing outside the process can send one. |
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
in `mm/util.c`, `setup_arg_pages` in `fs/exec.c`).
QEMU user mode puts the guest stack where the host kernel maps it.
QEMU 10.0.11 on an x86_64 host gives these entry stack pointers:

- 8 MiB stack limit, address randomisation off: in the window.
- 8 MiB stack limit, address randomisation on: below the window.
- 1 GiB stack limit: below the window.
- Unlimited stack limit: below the window.

The statements say nothing about a launch that puts the pointer below
the window.

The model also builds its own auxiliary vector, with ten entries
(`StackLayout.auxv_entries`). Linux and QEMU user mode publish more
entries. Thus a program can see a different vector in the model than
on a real launch. This occurs when the program reads an entry that the
model omits, or reads the whole vector in sequence. "The auxiliary
vector" in "Known gaps in precision" names the entries.

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
  `Sys/Fs/ReadWrite.v`), and the table of injected failures
  (`Run.injected_table`) has no arm for `write`.
- `mmap_min_addr` is 4096. The model declines only the address 0, because
  `cap_mmap_addr` rejects nothing else at that setting
  (`Sys/Mm/Mmap.v`, the `-EPERM` note). With a larger setting, Linux
  answers `-EPERM` for a fixed mapping below it, and the model admits
  the mapping.
- No `munmap` range meets the vDSO or the vvar mapping. Linux installs
  this pair at `execve`. QEMU user mode maps only a vDSO, as an ordinary
  mapping (`load_elf_vdso`, `linux-user/elfload.c`). The model's ledger
  carries neither (`Sys/Mm/Mmap.v`, the `munmap` arms), so the model
  answers such a call as if they were not there. QEMU unmaps the range
  and answers 0. Linux unmaps a mapping of the pair that the range covers
  whole. It refuses with `-EPERM` when the mapping is sealed
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

Design priority 2 asks that the model include no behavior that no supported
system gives. The model does not meet it in these cases. In each case, a
statement that compares sets of behaviors (for example, equivalence) can be
true of the model and false of the real systems.

- **No parameter for the system.** The model does not choose between Linux
  and QEMU user mode, or between Linux configurations (for example, the two
  mmap layouts). Where they differ, the model lets each system call choose
  again. A real system makes the choice the same way each time. Also, the
  source and the target can make different choices, as if they ran on
  different systems. For example, repeated `set_robust_list` calls can
  alternate between Linux's return and QEMU's `ENOSYS` return.
- **Clock resolution.** For supported non-CPU clock IDs, `clock_getres`
  accepts any positive nanosecond value below one second. Linux returns
  1 ns or a tick-based resolution; QEMU user mode forwards the host result.
  The model does not constrain later calls to use the same resolution.
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
- **A channel with no reader — fixed, and what it cost.** This used to
  be a gap: the write arm could not see whether fds 1 and 2 still had a
  reader, so a write to a stdout whose reader was gone got a count,
  where Linux raises `SIGPIPE` and kills the process. The model now has
  a death that is not an exit, and the launch says which case it is
  (`State.ProcInput.in_channel_reader`). `Run.valid_input` constrains
  that field at neither value, so every statement covers both the run
  whose standard output is read and the writing end of
  `prog | head -1`. What is left is a PREMISE and not a gap: the model
  assumes the launch left `SIGPIPE` at `SIG_DFL` (see "Signals"), and
  it has one answer per run rather than a reader that goes away at a
  point the model can see. A program whose reader goes away in the
  middle of its output is outside the model.
- **A socket write that delivers.** A write to a socket with no
  connection is answered — `-EPIPE`, and the `SIGPIPE` that goes with
  it (`net/core/stream.c`, `sk_stream_wait_connect` and
  `sk_stream_error`). A write to a CONNECTED socket is still
  `unmodeled`: it would have to choose a short count, or consume a
  pending peer error and rewrite the descriptor, which is
  `sendto`/`sendmsg`'s machinery. So `write(2)` on a socket is covered
  exactly where the connection is absent.
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
  QEMU user mode has a band of the same kind. `setup_arg_pages` in
  `linux-user/elfload.c` makes one mapping of fixed size for the guest
  stack (QEMU 10.0.11). The stack size is `guest_stack_size`, and
  `TARGET_DEFAULT_STACK_SIZE` in `linux-user/main.c` sets it to 8 MiB
  by default. A finite soft `RLIMIT_STACK` above 8 MiB makes the
  mapping larger, and the "Stack limit" row above puts that case
  outside the model. `setup_arg_pages` also puts a `PROT_NONE` guard
  page below the stack. `load_elf_binary` writes the entry image
  inside the mapping, with the exec filename, the argv and envp
  strings, `AT_RANDOM`, the auxiliary vector, `argc` and the pointers.
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
