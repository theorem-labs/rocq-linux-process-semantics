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

## Where the model is narrower

The statements restrict these cases, or the model says `unmodeled` for
them. A proof says nothing about a program in such a case.

| Area | Limit |
| --- | --- |
| Threads | The model has one thread. It has no scheduler and no shared-memory interleaving. For `fork`-like calls, the model describes the parent only. It does not run the child. |
| Signals | The model does not run signal handlers. |
| Address-space size | The system call specifications use Sv48. Thus you cannot prove the Sv39 and Sv57 statements for an image that can run. |
| Stack limit | The stack limit is 8 MiB. A larger or unlimited `RLIMIT_STACK`, which selects the legacy mmap layout, is outside the model. The model does not count the entry image against this limit; see "Stack floor" in "Known gaps in precision". |
| Arguments | `Run.valid_input` requires that the arguments after `argv[0]` do not contain `/` and are not `..`. Thus a proof about `cp src dst` does not apply to `cp /tmp/src dst`. It also bounds the lists (`Run.valid_argv`, `Run.valid_envp`): 1 to 1024 arguments and at most 2 MiB of argument bytes, at most 256 environment variables and at most 128 KiB of environment bytes, and at most 131071 bytes in each string. Each count of bytes includes the terminating NUL of each string. A launch outside these bounds is outside the model. |
| Standard input and output | The fds 0, 1 and 2 are external channels, and their direction is fixed: 0 is read-only, 1 and 2 are write-only (`State.FdChannel`). The model answers `-EBADF` for the other direction. Thus a proof says nothing about a program that is handed a connected socket on fd 0, as an inetd-style server is. |
| Network | The list of connections is never empty. Thus the model does not include an environment where no peer ever connects. |
| Memory budgets | The source can allocate 16 GiB and the target 512 GiB (`State.source_alloc_limit`, `State.target_alloc_limit`). The `*_budgets` statements change this premise. |
| Files | The file model has no full directory tree, no symbolic links, no device files except `/dev/null` and `/dev/urandom`, and no permissions. |

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
  different systems.
- **mmap placement.** A mapping without an address hint can go to any free,
  page-aligned address below `State.alloc_top`. This is wider than the
  placement policy of each supported system.
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
- **Stack floor.** The model does not count the entry image against the
  8 MiB stack limit. `Run.init_machine_state` maps the entry image up to
  `Run.entry_page_top` and, in addition, the whole window
  `[sp - State.stack_max_size, sp)` below the entry `sp`. Linux counts
  the whole stack VMA against `RLIMIT_STACK`, from its page-aligned top
  `vm_end` down: `expand_downwards` (`mm/vma.c`, Linux v6.18.46) passes
  `size = vm_end - address` to `acct_stack_growth`, which answers
  `-ENOMEM` when `size` passes the limit. That VMA holds the whole entry
  image: `do_execveat_common` (`fs/exec.c`) copies the exec filename and
  the argv and envp strings into it, `setup_arg_pages` (`fs/exec.c`)
  gives it its page-aligned top, and `create_elf_tables`
  (`fs/binfmt_elf.c`) writes `AT_RANDOM`, the auxv, `argc` and the
  pointers in it. So Linux never grows the stack below `vm_end - 8 MiB`,
  and the lowest `vm_end - sp` bytes of the model's window are never
  stack on Linux. `vm_end` is at or above `Run.entry_page_top`, and can
  be pages higher, because the kernel's entry image carries more than
  the model's: the auxv entries of the bullet above, the exec filename,
  and the random pad of less than 4 KiB that `arch_align_stack`
  (`arch/riscv/kernel/process.c`) takes.
  An access in that band succeeds in the model and faults on Linux, so
  a statement about a run whose stack reaches it
  can be true of the model and false of the real systems, and this one
  need not compare sets of behaviors: a single-run statement is enough.
  A program reaches the band when its stack goes more than
  `8 MiB - (vm_end - sp)` below the entry `sp`. The band grows with the
  size of argv and envp, to about 2 MiB for the largest that
  `Run.valid_argv` and `Run.valid_envp` admit.
  QEMU user mode has a band of the same kind: its stack is one fixed
  8 MiB mapping with a guard page below it, and the entry image is
  inside it (`setup_arg_pages` and `load_elf_binary` in
  `linux-user/elfload.c`, QEMU 8.2.2).
- **vDSO and vvar.** The kernel installs this pair at `execve`, and the
  model's ledger does not carry it (`Sys/Mm/Mmap.v`, the `munmap`
  arms). An `munmap` of a free range that lands on the pair answers 0,
  where Linux unmaps it, or refuses with `-EPERM` under
  `CONFIG_MSEAL_SYSTEM_MAPPINGS`.

## What the proofs do not check

- The executable checker of each system call is proved to agree with its
  specification. This does not show that the specification agrees with
  Linux. An error in both gives a correct proof of the wrong thing.
- Comments that state kernel behavior name the file and the function in
  Linux v6.18.46. No tool checks that these comments are correct.
