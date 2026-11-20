# Scope, assumptions and known gaps

Read this document before you use a proof as evidence about a real program.
It tells you which system the model describes, where the model is narrower
than that system, which assumptions it does not check, where it is less
precise, and where a run under QEMU user mode is not a Linux run. The
design priorities in [README.md](README.md#design-priorities) refer to
this document.

## Supported systems

- Native Linux on riscv64, stable v6.16 to v6.18.46, in
  the one kernel configuration named below. A citation without a version
  is to v6.18.46 (commit `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`).
- For instructions: the RISC-V specification (RV64GC).

Bugs in Linux do not count. The model describes one system, so no rule of
it chooses between two systems' answers, and a source and a target cannot
answer the same call as if they ran on different machines.

Where v6.16, v6.17 and v6.18.46 answer a shape differently, the model
declines that shape; "Where Linux versions differ" below lists each one.
Kernels before v6.16 are not supported, and the model does not check
claims about them. QEMU user mode is not supported either: where it
answers otherwise, the model answers as Linux does.

### The configuration of record

The model describes the kernel configuration that the repository's
agreement checks boot: the `config` asset of the release
`vm/kernel-v6.18.46-c1f99e9ab-fbe185ef1-t20260515` (sha256
`5973c2c29f9450827b376cc864f0fd56db9b964c3e9ff94e0d230cce1fa27d68`).
It is not the plain riscv64 defconfig: `.github/workflows/kernel-image.yml`
builds it from v6.18.46's `arch/riscv/configs/defconfig`, merges
`testing/vm/kernel.fragment` over it, and turns off every `=m` symbol
the fragment does not name. Answers that depend on a configuration
option follow this configuration. Among them:

- `CONFIG_EVENTFD=y`, so `eventfd2` answers `-EINVAL` for a refused flag
  word and never `-ENOSYS`.
- `CONFIG_FUTEX=y`, so `set_robust_list` is answered and never `-ENOSYS`.
- `CONFIG_UNIX=y`, so `socketpair(AF_UNIX, SOCK_STREAM, 0)` succeeds.
- `CONFIG_INET=y`, which the fragment names: the riscv64 defconfig gets
  it only through `NET_9P_FD`'s `imply INET` (`net/9p/Kconfig`), and the
  fragment turns `CONFIG_NET_9P` off. So `inet_init`
  (`net/ipv4/af_inet.c`) registers `AF_INET` at boot, and
  `socket(AF_INET, ...)` reaches `inet_create`, never the absent-family
  `-EAFNOSUPPORT` of `__sock_create` (`net/socket.c`).
- `CONFIG_IPV6=y` (`net/ipv6/Kconfig` gives `IPV6` `default y`), so
  `AF_INET6` is registered and `socket(AF_INET6, SOCK_DGRAM, 0)` hands
  back a UDPv6 socket (`inet6_create`, `net/ipv6/af_inet6.c`).
- `CONFIG_SMC` is not set (it needs `CONFIG_INFINIBAND`), so
  `socket(AF_INET, SOCK_STREAM, 256)` answers `-EPROTONOSUPPORT`.
  `CONFIG_MPTCP` and `CONFIG_IP_SCTP` are not set either; the model
  declines protocols 262 and 132 under `SOCK_STREAM` all the same.
- `CONFIG_COMPAT=y`: `arch/riscv/Kconfig` gives `COMPAT` `default 64BIT`,
  and neither the riscv64 defconfig nor the fragment turns it off. So
  `MSG_CMSG_COMPAT` is `0x80000000` (`include/linux/socket.h`), and
  `sendmsg` and `recvmsg` answer `-EINVAL` for a flag word with bit 31
  set before they resolve the descriptor (`__sys_sendmsg`,
  `__sys_recvmsg`, `net/socket.c`). The model declines both shapes, a
  fail-closed gap that costs priority 3 only.
- No block device, FUSE, overlayfs or network file system:
  `CONFIG_BLOCK`, `CONFIG_FUSE_FS`, `CONFIG_OVERLAY_FS` and
  `CONFIG_NETWORK_FILESYSTEMS` are not set (`testing/vm/kernel.fragment`).
  `fs/Kconfig` offers ext4, btrfs and xfs, and vfat with the other FAT
  file systems, only under `CONFIG_BLOCK`, and virtiofs (`VIRTIO_FS`,
  `fs/fuse/Kconfig`) is a FUSE file system. The file systems built whose
  regular files hold the bytes written to them are tmpfs
  (`CONFIG_TMPFS=y`; devtmpfs is a shmem mount) and ramfs, which
  `fs/Makefile` always builds; rootfs is one of the two (`init_rootfs`,
  `init/do_mounts.c`). Both set `s_maxbytes` to `MAX_LFS_FILESIZE`,
  `LLONG_MAX` on riscv64 (`shmem_fill_super`, `mm/shmem.c`;
  `ramfs_fill_super`, `fs/ramfs/inode.c`), and both look a name up with
  `simple_lookup` (`fs/libfs.c`), which answers `-ENAMETOOLONG` for a
  component longer than `NAME_MAX`, 255 bytes.
- No file system that installs an `f_op->flock` of its own. At v6.18.46
  those are 9p, AFS, Ceph, FUSE, GFS2, NFS, OCFS2 and the SMB client.
  `fs/Kconfig` offers NFS, Ceph, SMB, AFS and 9p only under
  `CONFIG_NETWORK_FILESYSTEMS` and GFS2 and OCFS2 only under
  `CONFIG_BLOCK`, and the fragment turns off both and `CONFIG_FUSE_FS`.
  So `SYSCALL_DEFINE2(flock)` (`fs/locks.c`) takes the local path,
  `locks_lock_file_wait`, whatever file system holds the file, and a
  lock request by the sole opener is granted whatever its type and the
  descriptor's access mode.
- `CONFIG_SECURITY` is not set (`testing/vm/kernel.fragment` turns off
  what the riscv64 defconfig turns on), so no LSM is built: every LSM,
  and `BPF_LSM`, IMA and EVM too, depends on it (`security/Kconfig` and
  the files it sources, `kernel/bpf/Kconfig`). The `security_*` hooks
  are the inline stubs of `include/linux/security.h`, and
  `security_file_lock`, `security_file_permission`, `security_task_kill`,
  `security_task_alloc`, `security_socket_create` and
  `security_socket_socketpair` among them answer 0, so no LSM denial is
  an answer any supported kernel gives. `CONFIG_LSM_MMAP_MIN_ADDR`, which
  depends on SELinux (`security/Kconfig`), does not exist.
- `CONFIG_FANOTIFY` is not set (`fs/notify/fanotify/Kconfig` gives it
  `default n`, and neither the riscv64 defconfig nor the fragment sets
  it), so the fsnotify permission hooks are the stubs of
  `include/linux/fsnotify.h` and no listener answers a permission event
  with `FAN_DENY`.
- `CONFIG_KPROBES` is not set: `arch/Kconfig` gives it no default,
  neither the riscv64 defconfig nor the fragment sets it, and the one
  symbol that selects it, `KGDB_HONOUR_BLOCKLIST` (`lib/Kconfig.kgdb`),
  sits under the unset `CONFIG_KGDB`. So `CONFIG_FUNCTION_ERROR_INJECTION`,
  which depends on `KPROBES` (`lib/Kconfig.debug`), does not exist, and
  neither do `CONFIG_BPF_KPROBE_OVERRIDE` (`kernel/trace/Kconfig`) and
  `CONFIG_FAIL_FUNCTION` (`lib/Kconfig.debug`), which depend on it. The
  `ALLOW_ERROR_INJECTION` that every system call wrapper emits
  (`arch/riscv/include/asm/syscall_wrapper.h`) expands to nothing
  (`include/asm-generic/error-injection.h`), and
  `within_error_injection_list` is the stub that answers false
  (`include/linux/error-injection.h`), so `check_attach_modify_return`
  (`kernel/bpf/verifier.c`) refuses a `BPF_MODIFY_RETURN` program on a
  wrapper. So no BPF program and no `fail_function` answers a system
  call in place of its wrapper.
- `CONFIG_SECCOMP` is not set: `arch/Kconfig` gives it `def_bool y`, and
  `testing/vm/kernel.fragment` turns it off. So `CONFIG_SECCOMP_FILTER`,
  which depends on it, does not exist, the `seccomp` system call is not
  built (`COND_SYSCALL(seccomp)`, `kernel/sys_ni.c`), and
  `prctl(PR_SET_SECCOMP)` answers `-EINVAL` (`prctl_set_seccomp`,
  `include/linux/seccomp.h`): no task, the launcher included, can
  install a filter. `__secure_computing` is the stub of the same file
  that answers 0, so no seccomp filter answers a system call.
- `CONFIG_RTC_CLASS` is not set (`testing/vm/kernel.fragment` turns off
  what the riscv64 defconfig turns on), so `alarmtimer_get_rtcdev` is the
  stub that returns NULL (`include/linux/alarmtimer.h`) and `clock_getres`
  answers `-EINVAL` for `CLOCK_REALTIME_ALARM` and `CLOCK_BOOTTIME_ALARM`
  whatever `tp` is (`alarm_clock_getres`, `kernel/time/alarmtimer.c`).
- `CONFIG_RSEQ=y`: `init/Kconfig` gives `RSEQ` `default y` where
  `HAVE_RSEQ` holds, `arch/riscv/Kconfig` selects `HAVE_RSEQ`, and
  neither the riscv64 defconfig nor the fragment turns it off. So
  `create_elf_tables` (`fs/binfmt_elf.c`) puts `AT_RSEQ_FEATURE_SIZE`
  and `AT_RSEQ_ALIGN` in every auxiliary vector, 29 entries in all. The
  model also admits the 27-entry vector of a build without it ("Known
  gaps in precision").
- `CONFIG_TRANSPARENT_HUGEPAGE` is not set: `mm/Kconfig` gives it no
  default, and neither the riscv64 defconfig nor the fragment sets it.
  So `__get_unmapped_area` (`mm/mmap.c`) never sends an anonymous
  request to `thp_get_unmapped_area_vmflags` (`mm/huge_memory.c`) for
  its padded, 2 MiB-aligned search. The model also admits that
  placement ("Known gaps in precision").

The Kconfig entries of the options these bullets set or turn off are the
same text in v6.16, v6.17 and v6.18.46 except for three, and none of the
three changes an answer the model gives. `FUSE_FS` selects `FS_IOMAP`
from v6.17 on and v6.18.46 moves a path in its help text; the fragment
turns it off. `SMC` depends on `INET && INFINIBAND` and
on `m || ISM != m` in v6.16 and v6.17, and on `INET && INFINIBAND && DIBS`
in v6.18.46; it is off in all three, because `INFINIBAND`, whose entry
has no default, is set by none of the three defconfigs and not by the
fragment. `IP_SCTP` selects `CRYPTO`, `CRYPTO_HMAC` and `CRYPTO_SHA1` in
v6.16 and v6.17 and `CRYPTO_LIB_SHA1`, `CRYPTO_LIB_SHA256` and
`CRYPTO_LIB_UTILS` in v6.18.46; it has no default and is off in all
three. The three riscv64 defconfigs differ only in driver options (SoC,
sound, MMC, PWM, Ethernet, input, I2C, pin control and DMA drivers),
none of which changes an answer the model gives.

## Where QEMU user mode differs

QEMU user mode for riscv64 is **not** a supported system. The list below
names each place where the model's answer and QEMU user mode's answer
differ, with the file and the function on each side. A run under
`qemu-riscv64` gives a trace that a Linux launch also gives when the run
depends on none of them. A `qemu-riscv64` counterexample that depends on
one of them is not a Linux run.

Each entry reads: what the model answers (Linux's), then what QEMU user
mode answers. A QEMU citation with a line number is to QEMU 11.1.1's
`linux-user/` tree; one without is to QEMU 10.0.11.

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
  `cmpxchg` of `load_val`. So a same-address same-value rewrite (ABA)
  fails the `sc` in the model and can leave it succeeding under
  qemu-user, and a partly overlapping store that changes the reserved
  bytes leaves the `sc` succeeding in the model and fails it under
  qemu-user. The ISA allows either answer in both cases (`inval_resv`).

### The start state and the address space

- **The entry block.** The model lays Linux's block, from the entry
  stack pointer up to the stack VMA's end, with the auxiliary vector of
  29 entries that the configuration of record gives, and also admits
  the 27 of a build without `CONFIG_RSEQ`, which no supported kernel
  gives (`StackLayout.build_stack_bytes`, `StackLayout.auxv_entries`;
  "Known gaps in precision"). QEMU
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
  Linux's bounds. Where a free page-aligned HINT reaches above it, the
  model answers `unmodeled` rather than naming an address of its own
  (`Sys/Mm/Mmap.v`, `place_declined_b`), and the same where such a
  hint ends inside the stack's guard gap below it. The three cases
  that bound still cuts Linux's answer off in are an mmap base above
  `State.alloc_top`, the bottom-up fallback above it, and the guard
  gap at `brk`; "Soundness gaps" below gives all three as R-a, R-b and
  R-c, and "Known gaps in precision" holds R-c's full entry. QEMU
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
  `linux-user/syscall.c:13553-13563`), so that guest userspace falls back
  to a non-robust futex. A kernel built without `CONFIG_FUTEX` answers
  `-ENOSYS` too (`kernel/sys_ni.c:81`); the configuration of record has
  it.
- **`mmap` with a misaligned offset.** The model answers `-EINVAL` for
  every length: `riscv_sys_mmap` (`arch/riscv/kernel/sys_riscv.c`) tests
  the offset before `ksys_mmap_pgoff` reads the length. QEMU user mode
  rounds and tests the length first, so for a length within a page of
  2^64 it answers `-ENOMEM` (`target_mmap`, `linux-user/mmap.c:964`).
- **`mmap` with a closed fd and no `MAP_ANONYMOUS`.** The model answers
  `-EBADF`: `ksys_mmap_pgoff` (`mm/mmap.c`) runs `fget` before `do_mmap`.
  QEMU user mode never resolves the fd; `target_mmap`
  (`linux-user/mmap.c:964`, `target_mmap__locked` :914) validates the
  request itself, so a zero length, a length within a page of 2^64, an
  invalid `MAP_TYPE`, an unknown prot bit and `MAP_FIXED` at an unaligned
  address each get QEMU's own `-EINVAL` or `-ENOMEM` before any host call.
- **`mmap` with `MAP_FIXED` or `MAP_FIXED_NOREPLACE` whose page-rounded
  range reaches 2^64.** The model answers Linux's (`do_mmap` and
  `__get_unmapped_area`, `mm/mmap.c`; `do_mmap` sets `MAP_FIXED` for
  `MAP_FIXED_NOREPLACE` at :361-362): an address in `[2^64-4095, 2^64-1]`
  is handed back as itself (`IS_ERR_VALUE`, :854-855), and every other
  address is `-ENOMEM` (`addr > TASK_SIZE - len`, :857-858) before the
  alignment `-EINVAL`. That includes an aligned range that ends exactly
  at 2^64, such as `(2^64-4096, 4096)`. QEMU user mode tests the alignment
  first (`target_mmap`, `linux-user/mmap.c:994-997`), so it answers
  `-EINVAL` for every misaligned address there. Its range test (:999-1001)
  then accepts the aligned exact-end range: `guest_range_valid_untagged_vaddr`
  (QEMU 11.1.1 `include/user/guest-host.h:63-66`) accepts a range whose
  last byte is `guest_addr_max`, and without `-R`, `main` sets
  `guest_addr_max` to `~0ul` for a riscv64 guest
  (`linux-user/main.c:847-852`). So qemu-user passes that range to the
  host. With an identity `guest_base` on a Linux host, the host gives the
  same `-ENOMEM`; with another `guest_base` the host address can wrap,
  and qemu-user can answer otherwise.
- **`mmap` with a `MAP_SHARED_VALIDATE` word that carries a bit outside
  the legacy set, at length 0 or at a misaligned offset.** The model
  answers Linux's `-EINVAL`: `riscv_sys_mmap`
  (`arch/riscv/kernel/sys_riscv.c`) tests the offset first, `do_mmap`
  (`mm/mmap.c`) tests the zero length, and an anonymous word's type is
  read only after both. QEMU user mode reads the type first (`do_mmap`,
  `linux-user/syscall.c:6164-6186`) and answers `-EOPNOTSUPP` for a bit
  outside `TARGET_LEGACY_MAP_MASK` and `MAP_SYNC` (:6171-6178), such as
  `MAP_FIXED_NOREPLACE` in the word 0x100023.
- **`mmap` with `MAP_FIXED_NOREPLACE` over a range that holds no
  mapping.** The model grants the range or answers `-ENOMEM`: `do_mmap`
  (`mm/mmap.c`) answers `-EEXIST` only where `find_vma_intersection`
  finds a VMA. QEMU user mode answers `-EEXIST` on four kinds of free
  range: a gap between two LOAD segments, which `load_elf_image`
  (`linux-user/elfload.c:1065-1075`) reserves `PROT_NONE` with the rest
  of the image's span; the part of its own stack more than 8 MiB below
  the entry stack pointer, when `-s` or `QEMU_STACK_SIZE` asks for a
  larger stack (`setup_arg_pages`, `linux-user/elfload.c:395-436`); its
  own two-page vDSO (`load_elf_vdso`); and, without `-R`, a range that
  meets a host mapping, because `target_mmap` keeps the flag on the host
  `mmap` (`mmap_h_eq_g`, `linux-user/mmap.c:612-625`; `mmap_frag` and
  `mmap_h_gt_g` on a host with 16 or 64 KiB pages). Under `-R`,
  `target_mmap__locked` answers `-EEXIST` from its own page table
  (:925-931).
- **`mmap` with `MAP_FIXED` or `MAP_FIXED_NOREPLACE` at a low address.**
  The model grants every page-aligned address from 4096 up, or answers
  `-ENOMEM`: `mmap_min_addr` is 4096 (the `mmap_min_addr` assumption
  below), and that is the floor `cap_mmap_addr` (`security/commoncap.c`)
  tests. QEMU user mode without `-R` passes the request to the host
  `mmap` (`mmap_h_eq_g` and `mmap_h_gt_g`, `linux-user/mmap.c:605-630`
  and :792-912) and hands back the host's errno, so it answers `-EPERM`
  below a raised host floor, and on a host with 16 or 64 KiB pages for a
  request whose first host page is page 0.
- **`clock_getres` with a NULL `tp`.** The model answers 0 and writes
  nothing, whatever is mapped at address 0: `SYSCALL_DEFINE2(clock_getres)`
  (`kernel/time/posix-timers.c`) skips the copy under `if (!error && tp
  && put_timespec64(...))`. QEMU user mode attempts the copy and discards
  its result (`TARGET_NR_clock_getres` in `do_syscall1`,
  `linux-user/syscall.c`, whose `host_to_target_timespec` does not test
  for NULL), so under qemu-user the call can write 16 bytes at address 0.
- **`clock_getres` on the alarm clock ids.** The model answers `-EINVAL`
  for ids 8 and 9 whatever `tp` is, because in the configuration of
  record `alarm_clock_getres` (`kernel/time/alarmtimer.c`) has no RTC
  device to read. QEMU user mode hands the id to the host's
  `clock_getres` (`TARGET_NR_clock_getres` in `do_syscall1`,
  `linux-user/syscall.c:13472-13480`), so it gives the host kernel's
  answer, which on a host with an RTC is 0 and a resolution written at
  `tp`.
- **`mremap(MREMAP_MAYMOVE)`: a misaligned `old`, a `new_size` that rounds
  to 0, an equal size, a shrink.** The model answers Linux's `-EINVAL`,
  `ret_only old` and in-place shrink (`mm/mremap.c`,
  `check_mremap_params` and `mremap_at`). QEMU user mode reserves a fresh
  range with `mmap_find_vma` before the host `mremap` (`target_mremap`,
  `linux-user/mmap.c:1194-1209`), so it gives `-ENOMEM` before `-EINVAL`
  and relocates the equal and the shrink call.
- **`mremap` grow on a host whose pages are larger than 4 KiB, or under
  `-R`.** The model answers Linux's in-place grow, fresh move or
  `-ENOMEM` with nothing changed (`mm/mremap.c`, `mremap_at`). QEMU user
  mode's `target_mremap` (`linux-user/mmap.c:1194-1209`) hands the host
  `mremap` a source that is aligned for the guest page and not for the
  host page, and passes back the host's `-EINVAL` (`check_mremap_params`).
  Under `-R` it replaces the source with a `PROT_NONE` reservation after
  a failed host call (`mmap_reserve_or_unmap`, :1206-1208), so the
  source mapping is gone where Linux leaves it.
- **`madvise(MADV_DONTNEED)` over a range that ends exactly at 2^64.**
  The model answers Linux's `-EINVAL`: `is_valid_madvise`
  (`mm/madvise.c`) refuses a sum that wraps, such as
  `(2^64 - 4096, 4096)`. QEMU user mode's range test accepts a range
  whose last byte is `guest_addr_max` (`target_madvise`,
  `linux-user/mmap.c:1271`), which is `~0ul` without `-R`, and where no
  guest page lies it skips the host call and answers 0 (:1334-1341), the
  path its own comment calls wrong (:1303-1307).
- **`mprotect` with a length of 0.** The model answers 0 for every
  `prot` except the `PROT_GROWSDOWN|PROT_GROWSUP` pair: `do_mprotect_pkey`
  (`mm/mprotect.c`) returns on `!len` before `arch_validate_prot`. QEMU
  user mode validates `prot` first (`target_mprotect` and
  `validate_prot_to_pageflags`, `linux-user/mmap.c:121-197`), so it
  answers `-EINVAL` for `PROT_GROWSUP`, for `PROT_GROWSDOWN` outside its
  stack window, and for any bit of the low 32 outside
  `PROT_READ|PROT_WRITE|PROT_EXEC|PROT_SEM`. Inside the stack window the
  syscall entry strips `PROT_GROWSDOWN` and aims the call at the stack
  below `start` (`linux-user/syscall.c:11203-11216`), so it changes the
  protection of pages Linux leaves alone. A wrapping range with such a
  `prot` is `-ENOMEM` on Linux and `-EINVAL` under QEMU user mode.
- **`ioctl` with a request outside the modeled set, or a NULL argument.**
  The model resolves the fd first: `-EBADF` on a closed fd, `-ENOTTY` for a
  tty-only request on a file, a socket, a pipe or `/dev/null`, the
  argument never read (`SYSCALL_DEFINE3(ioctl)` and `vfs_ioctl`,
  `fs/ioctl.c`). QEMU user mode answers before the fd: `do_ioctl`
  (`linux-user/syscall.c:5698-5724`) returns `-TARGET_ENOTTY` for a
  request it does not know and `-TARGET_EFAULT` from `lock_user` for an
  `IOC_W` or `IOC_RW` request whose argument is unreadable (`TCSETS`,
  `TIOCSWINSZ` or `TIOCSPTLCK` with NULL).
- **`fcntl(F_GETFL)` on a socket.** The model answers `O_RDWR`, 2:
  `do_fcntl` (`fs/fcntl.c`) returns `f_flags`, and `sock_alloc_file`
  (`net/socket.c`) sets it to `O_RDWR` with `O_NONBLOCK` only.
  QEMU user mode built against glibc on an x86_64 host sets
  `TARGET_O_LARGEFILE` in every `F_GETFL` answer (`do_fcntl`,
  `linux-user/syscall.c:7508-7517`, and the last row of
  `fcntl_flags_tbl`, :474-476), so it answers 32770. Built against musl
  it answers 2.
- **`fcntl` on a closed fd with a command QEMU does not translate, or
  with a lock or `F_SETOWN_EX` command whose argument it cannot read.**
  The model answers `-EBADF`: `SYSCALL_DEFINE3(fcntl)` (`fs/fcntl.c`)
  resolves the fd before `do_fcntl` reads `cmd`. QEMU user mode
  translates the command first and answers `-EINVAL` for one it does not
  know (`do_fcntl` and `target_to_host_fcntl_cmd`,
  `linux-user/syscall.c:7452-7463` and :7262-7263), and copies a
  `struct flock` or `struct f_owner_ex` in before the host call
  (:7466-7471, :7540-7541), so it answers `-EFAULT` or `-EINVAL` there.
- **`getcwd` with a size the path does not fit.** The model answers
  `-ERANGE` whatever `buf` is: `SYSCALL_DEFINE2(getcwd)`
  (`fs/d_path.c`) compares the length before its only `copy_to_user`.
  QEMU user mode locks `buf` for writing first (`TARGET_NR_getcwd`,
  `linux-user/syscall.c:12284-12289`), so it answers `-EFAULT` at size 1
  for a `buf` that is not writable guest memory, at size 0 for an
  address above `reserved_va` under `-R`, and at `getcwd(NULL, 0)` when
  `guest_base` is 0, where `lock_user` hands back NULL for guest address
  0 and the case reads that as a failure.
- **`getgroups` with a positive size on a process with no supplementary
  groups, or with a size too small for the list.** The model answers 0
  or `-EINVAL`: `SYSCALL_DEFINE2(getgroups)` (`kernel/groups.c`) has no
  upper bound on the size, allocates nothing, and `groups_to_user`
  writes nothing for an empty list. QEMU user mode
  (`TARGET_NR_getgroups`, `linux-user/syscall.c:12582-12612`) answers
  `-EINVAL` for a size above `NGROUPS_MAX` (:12589-12591), `-ENOMEM`
  when its `g_try_new` copy fails (:12592-12596), and `-EFAULT` when
  `lock_user` refuses the destination (:12599-12604).
- **`setgroups` from an unprivileged caller.** The model answers
  `-EPERM` with nothing read: `SYSCALL_DEFINE2(setgroups)`
  (`kernel/groups.c`) runs `may_setgroups` first. QEMU user mode
  (`TARGET_NR_setgroups`, `linux-user/syscall.c:12613-12639`) tests the
  size first (`-EINVAL` for a negative size or one above `NGROUPS_MAX`,
  :12620-12621), then allocates (`-ENOMEM`, :12623-12627), locks the list
  (`-EFAULT`, :12628-12631) and reads every entry (:12633-12635) before
  the host call in which `may_setgroups` runs, so its `-EPERM` comes
  after a read of the whole list.
- **`clone3`.** The model answers one of Linux's answers
  (`SYSCALL_DEFINE2(clone3)`, `kernel/fork.c`). QEMU user mode has no
  `clone3` case: `do_syscall1`'s `default` answers `-ENOSYS` with
  nothing read (`linux-user/syscall.c:14618-14620`).
- **`prctl` with an option word at or above 2^32.** The model reads the
  low 32 bits: `SYSCALL_DEFINE5(prctl)` (`kernel/sys.c`) takes an `int`
  option, so `prctl(2^32 | PR_CAPBSET_READ, 0)` answers 1. QEMU user
  mode's `do_prctl` switches on the whole 64-bit word
  (`linux-user/syscall.c:6706-6711`) and answers `-EINVAL` from its
  `default` (:6860-6863).
- **`sigaltstack` with `SS_AUTODISARM` set.** The model masks the bit
  before it tests the mode, as `do_sigaltstack` (`kernel/signal.c`)
  does, so `ss_flags` of 0x80000000, 0x80000001 and 0x80000002 answer 0.
  QEMU user mode's `target_restore_altstack` switches on the raw word
  and answers `-EINVAL` to each (`linux-user/signal.c:317-319`).
- **`sched_setscheduler` with a negative `policy` or `pid` beside a
  non-NULL `param`.** The model answers `-EINVAL` with nothing read:
  `SYSCALL_DEFINE3(sched_setscheduler)` and `do_sched_setscheduler`
  (`kernel/sched/syscalls.c`) test both before `copy_from_user`. QEMU
  user mode reads the four-byte `param` first
  (`linux-user/syscall.c:12091-12104`): `-EFAULT` for one it cannot
  read, and the host's `-EINVAL` after a read of a readable one.
- **`readv` and `writev`: a closed fd or an fd of the wrong mode beside a
  count of 0, a raw `iovcnt` over `IOV_MAX`, an unreadable array or a
  negative length; a raw `iovcnt` over `IOV_MAX` whose low 32 bits are in
  range.** The model answers Linux's `-EBADF`, and the truncated transfer
  for the wide count: Linux resolves the fd, tests the mode, and only then
  imports the `unsigned int` count (`fs/read_write.c`, `do_readv`,
  `do_writev`, `vfs_readv`, `vfs_writev`; `lib/iov_iter.c`,
  `import_iovec`). QEMU user mode runs `lock_iovec` before the host call
  (`linux-user/syscall.c:3072-3132`; readv :11886-11895, writev
  :11897-11906): 0 for a count of 0 (:3082-3085), `-EINVAL` for a raw
  count over `IOV_MAX` (:3086-3089), `-EFAULT` for an unreadable array
  (:3097-3102) and `-EINVAL` for a negative length (:3113-3115).
- **`writev` to a regular file from a source that is readable at the
  start and not throughout.** The model answers the short write of the
  gathered prefix. QEMU user mode cuts at the faulting descriptor in
  `lock_iovec` (`linux-user/syscall.c:3120-3131`).
- **`sendto` and `sendmsg`: the order of the buffer, the address, the
  header and the fd.** The model follows Linux: `__sys_sendto` range-checks
  the buffer with `import_ubuf` (`access_ok` only), then resolves the fd,
  reads an address only when one is given, and the copy faults inside
  `tcp_sendmsg_locked` (`net/ipv4/tcp.c`) or `sk_stream_wait_connect`
  (`net/core/stream.c`) answers `-EPIPE` without copying; `__sys_sendmsg`
  resolves the fd before it reads the header (`net/socket.c`). QEMU user
  mode locks the buffer, the header and the iovec array before the host
  call (`do_sendto`, `linux-user/syscall.c:3636-3652`; `do_sendrecvmsg`
  :3445-3450; `lock_iovec` :3072-3132), so it answers `-EFAULT` for an
  in-range unmapped buffer, header, array or first segment (on a dead
  socket or a closed fd alike), `-EINVAL` for a negative `addrlen` beside
  a NULL address and for a negative later length on a closed fd, and the
  host's answer for a zero-length buffer or segment past `TASK_SIZE`,
  which Linux refuses with `-EFAULT`.
  Where both answer `-EFAULT` for a range `access_ok` refuses, QEMU user
  mode does so only while no guest page lies above `TASK_SIZE`: without
  `-R` its bound is 2^64 (`linux-user/main.c:847-853`), and it passes a
  range on such a page to the host. `sendmsg` with a nonzero
  `msg_iovlen` is `-ENOMEM` under QEMU user mode when `lock_iovec`'s
  allocation fails (`linux-user/syscall.c:3091-3095`), whatever the
  model answers. And a buffer, header or array in the model's entry-stack
  band below the bottom of QEMU user mode's own stack (`setup_arg_pages`,
  `linux-user/elfload.c:395-436`) is `-EFAULT` there, where the model
  answers by the fd and the socket.
- **`recvfrom` and `recvmsg`: the destination, `*addrlen`, the header
  and the iovec array, against the fd.** The model follows Linux:
  `__sys_recvfrom` imports the destination with `import_ubuf` first, so
  a range `access_ok` refuses is `-EFAULT` even at length 0
  (`lib/iov_iter.c`), then resolves the fd, and touches neither the
  destination's pages nor `*addrlen` off a socket, so beside a closed or
  non-socket fd an unmapped, read-only or write-only destination and an
  unreadable or negative `*addrlen` get that fd's `-EBADF` or `-ENOTSOCK`
  (`net/socket.c`); `__sys_recvmsg` resolves the fd before
  `___sys_recvmsg` reads the header. QEMU user mode locks the
  destination and the header for writing and imports the iovec array
  before the host call resolves the fd (`do_recvfrom`,
  `linux-user/syscall.c:3683-3741`; `do_sendrecvmsg` :3439-3454;
  `lock_iovec` :3072-3132). On a closed or non-socket fd it answers
  `-EFAULT` for a destination or header it cannot lock, which a
  read-only or write-only page fails (:3695), `-EFAULT` for an unreadable
  `*addrlen` and `-EINVAL` for a negative one (:3700-3708), `-EMSGSIZE`
  for a `msg_iovlen` over `IOV_MAX` (`do_sendrecvmsg_locked`,
  :3365-3371), `-ENOMEM` when `lock_iovec` cannot allocate (:3091-3095),
  `-EFAULT` for an array it cannot lock (:3097-3102), `-EINVAL` for a
  negative `iov_len` (:3113-3115), and 0 for a `msg_iovlen` of 0 without
  a host call (:3082-3085, :3373-3379). It also lets a zero-length
  destination past `TASK_SIZE` through its lock (:3692-3699), which
  Linux refuses with `-EFAULT`.
- **`socket` and `socketpair` with a type word carrying an unknown flag
  bit.** The model answers Linux's `-EINVAL` before anything is written
  (`__sys_socket_create` and `__sys_socketpair`, `net/socket.c`). QEMU
  user mode drops the unknown bits in `target_to_host_sock_type`
  (`linux-user/syscall.c:3183-3215`) and calls the host with the
  stripped word (`do_socket` :3233, `do_socketpair` :3618-3631), so
  `socket` can succeed or answer the stripped word's `-EPROTONOSUPPORT`
  or `-EAFNOSUPPORT`, and `socketpair(AF_INET, ...)` answers
  `-EOPNOTSUPP` with `usockvec` unwritten.
- **`socketpair(AF_INET, ...)`.** The model answers as `__sys_socketpair`
  (`net/socket.c`) does: it stores both descriptor numbers through
  `usockvec` before it asks the family, so it answers `-EOPNOTSUPP`
  with both numbers written, and `-EFAULT` for a `usockvec` the stores
  cannot reach. QEMU user mode writes `usockvec` only after a host call
  that succeeds (`do_socketpair`, `linux-user/syscall.c:3618-3633`), so
  it answers `-EOPNOTSUPP` with nothing written, for a `usockvec` it
  cannot write as well.
- **`socket(AF_NETLINK, ...)` with a type past `SOCK_MAX` and a protocol
  other than 9 and 15.** The model answers Linux's `-EINVAL` from
  `__sock_create`'s type range (`net/socket.c`). QEMU user mode answers
  its own `-EPROTONOSUPPORT` before the host call (`do_socket`,
  `linux-user/syscall.c:3243-3249`).
- **`eventfd2` with a refused flag word.** The model answers `-EINVAL`
  (`SYSCALL_DEFINE2(eventfd2)`, `fs/eventfd.c`). A qemu-user host whose
  target is sparc64, mips or parisc accepts some of those words, because
  its `TARGET_O_NONBLOCK` and `TARGET_O_CLOEXEC` differ
  (`linux-user/syscall_defs.h`; `TARGET_NR_eventfd2`,
  `linux-user/syscall.c:13865-13876`, clears only the target's masks).
- **`epoll_create1`, `epoll_ctl` and `epoll_pwait`: the flag word and
  the copies.** The model answers in Linux's order (`fs/eventpoll.c`):
  `do_epoll_create` refuses every bit but `EPOLL_CLOEXEC` with
  `-EINVAL`; `epoll_ctl` narrows `op` to an `int` and copies no event for
  `EPOLL_CTL_DEL`; `do_epoll_pwait` sets the signal mask first and tests
  `events` with `access_ok` alone, which reads no mapping. QEMU user mode
  passes `epoll_create1` a word with the bits `fcntl_flags_tbl` does not
  carry dropped (`linux-user/syscall.c:13939-13940`), so bit 31, bit 20
  alone and 3 give a descriptor; compares the full 64-bit `op` with
  `EPOLL_CTL_DEL` and locks a non-NULL `event` first (:13941-13968), so
  `op` 2^32 + 2 with an unreadable `event` is `-EFAULT`; and in
  `epoll_pwait` tests `maxevents` first and locks `events` for writing
  (:13973-14050), so an out-of-bounds `maxevents` beside an unreadable
  mask is `-EINVAL` where Linux answers `-EFAULT`, and an `events` range
  not mapped writable is `-EFAULT` where Linux answers the fd's or the
  mask's errno.
- **`timerfd_create` with a flag bit outside `TFD_CLOEXEC|TFD_NONBLOCK`.**
  The model answers Linux's `-EINVAL` (`SYSCALL_DEFINE2(timerfd_create)`,
  `fs/timerfd.c`). QEMU user mode passes the host a word with the bits
  `fcntl_flags_tbl` does not carry dropped (`TARGET_NR_timerfd_create` in
  `linux-user/syscall.c` at QEMU 11.1.1), so bit 31, 22 or 20, and bit 15
  on a host whose `O_LARGEFILE` is 0, gives a descriptor.
- **`epoll_pwait` with a closed `epfd` beside a `maxevents` outside
  `1..EP_MAX_EVENTS`, or an events buffer that `access_ok` refuses.** The
  model answers `-EBADF`: Linux resolves the fd first (`do_epoll_wait`,
  `fs/eventpoll.c`). QEMU user mode checks the count and locks the buffer
  first (`TARGET_NR_epoll_pwait`, `linux-user/syscall.c:13973-13994`).
- **`ppoll` with `nfds` 0 and a `ufds` above `TASK_SIZE`.** The model
  answers Linux's `-EFAULT` (`Sys/Fs/Select.v`,
  `ppoll_writeback_access`): `do_sys_poll` (`fs/select.c`) runs
  `user_write_access_begin` on `ufds` whatever `nfds` is. QEMU user mode
  reads `ufds` only when `nfds` is not 0 (`do_ppoll`,
  `linux-user/syscall.c:1544-1570`) and hands the host a NULL array, so
  it answers 0 once the timeout runs out.
- **`accept4` with a closed fd beside unknown flags or a non-NULL
  address.** The model answers `-EBADF`: `__sys_accept4` (`net/socket.c`)
  resolves the fd before the flags. QEMU user mode checks the flags and
  validates the address length first (`do_accept4`,
  `linux-user/syscall.c:3504-3513`).
- **Transfers: `read`, `write`, `pread64`, `pwrite64`.** The model
  answers in Linux's order. QEMU user mode locks the whole buffer before
  the host call (`lock_user`, `linux-user/uaccess.c`), so a buffer that is
  readable in part gives a different answer.
- **A `read` or `write` of more than 0x7ffff000 bytes on a host whose
  pages are larger than 4 KiB.** The model clamps the count at
  0x7ffff000 (`State.MAX_RW_COUNT`), riscv64 Linux's `MAX_RW_COUNT`
  (`include/linux/fs.h`; riscv64 has only 4 KiB pages,
  `arch/riscv/Kconfig`). QEMU user mode passes the call to the host,
  whose clamp on a 16 or 64 KiB host is 0x7fffc000 or 0x7fff0000.

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

## Where Linux versions differ

Some shapes are contested for a reason that is not QEMU user mode.

### Within v6.16 to v6.18.46

The supported versions answer these shapes differently, and the model
declines each one (`unmodeled`).

- **`mremap(MREMAP_MAYMOVE)` whose rounded `new_len` passes
  `TASK_SIZE`.** From v6.17 `check_mremap_params` tests
  `new_len > TASK_SIZE` before any VMA is looked up and answers `-EINVAL`
  (`mm/mremap.c:1775-1776`; v6.17 :1778-1779). v6.16 tests it only in
  `mremap_to` (`mm/mremap.c:1387-1389`, v6.16), which a call without
  `MREMAP_FIXED` never reaches, so it answers `-EFAULT` with no VMA at
  the address and `-ENOMEM` from `expand_vma` otherwise
  (`Mremap.mremap_spec`).
- **`getsockname` and `getpeername` on a stream-pair end whose address
  buffer does not take the whole address.** Each version answers
  `-EFAULT`, with different stores: v6.18.46's `move_addr_to_user` stores
  the length before it copies the address (`net/socket.c:276-314`), and
  v6.16's and v6.17's store it with `__put_user` after the copy
  (`net/socket.c:276-301`, v6.17), so there the length is not written
  (`Net.Socket.stream_getname`).
- **`mmap` with a page-aligned offset at or above 2^63.** v6.16 and v6.17
  shift a signed `off_t` offset in `riscv_sys_mmap`
  (`arch/riscv/kernel/sys_riscv.c:11-21`, v6.17), v6.18.46 an
  `unsigned long` one, so the page offset differs and `do_mmap`'s
  `-EOVERFLOW` test (`mm/mmap.c:373-374`) can fire on the older two. The
  model answers no such call: it declines every nonzero offset of an
  anonymous mapping and every mapping of a live fd (`Mmap.mmap_spec`).

### Before v6.16

The model answers as v6.16 to v6.18.46 do, and an older stable kernel
answers otherwise. A proof says nothing about those kernels. These are
the known cases.

- **`flock` with `LOCK_MAND`, or with an unrecognised operation, on a
  closed fd.** The model answers 0 for `LOCK_MAND` and `-EINVAL` for an
  unrecognised operation, both before the fd lookup
  (`SYSCALL_DEFINE2(flock)`, `fs/locks.c`: the `LOCK_MAND` test and
  `flock_translate_cmd` precede `CLASS(fd, f)(fd)`). Kernels v4.17 to
  v5.19 resolve the fd first. QEMU user mode passes the call through to
  the host, so it answers what its host kernel answers; it is not a
  difference of its own.
- **`readv` and `writev` on an fd of the wrong mode beside a base that
  `access_ok` refuses.** The model answers `-EBADF`: `vfs_readv` and
  `vfs_writev` test the mode before `import_iovec` reads the vector
  (`fs/read_write.c:999-1004`, `:1037-1042`; the same text in v6.16 and
  v6.17). An older kernel that imported first answers `-EFAULT`.
- **`openat` of `"."` or `".."` with `O_WRONLY|O_CREAT|O_EXCL|O_APPEND`.**
  The model answers `-EEXIST`: `do_open` tests `O_EXCL` against
  `FMODE_CREATED` first (`fs/namei.c:3931-3987`; the same text in v6.16
  and v6.17). An older kernel whose `do_last` skipped that test for a
  directory answers `-EISDIR`.
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
  separate limit, not a version difference: it is residual R-b below,
  whose hint half the model now answers `unmodeled` for.
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
- **A `read` or `pread64` of `/dev/urandom` for more than 0x1ffffff
  bytes.** The model answers the whole clamped count: `urandom_read_iter`
  loops in `get_random_bytes_user` until the iterator is empty
  (`drivers/char/random.c`). Kernels before v5.18, and the stable releases
  before the rewritten random driver reached them (v4.19.249, v5.4.200,
  v5.10.119, v5.15.44 and v5.17.12 are the first without the cap), cap one
  call at `INT_MAX >> 6`, 0x1ffffff bytes.
- **`getrandom` of 0 bytes at a buffer past `TASK_SIZE`.** The model
  answers `-EFAULT` (or `-EINTR`): `import_ubuf` range-tests the buffer
  at length 0 (`lib/iov_iter.c`). Kernels before v5.19 run no range test
  on a zero-length request and answer 0.
- **A file `write` or `pwrite64` from a source readable at its first byte
  and not throughout.** The model writes the readable prefix and returns
  its length (`generic_perform_write`, `mm/filemap.c`). Kernels v4.17 to
  v5.17 fault each page-sized chunk in before the copy and answer the
  prefix cut back to a chunk boundary, or `-EFAULT` with the file
  untouched when that leaves nothing.
- **`prctl(PR_CAPBSET_READ)` of capability 38, 39 or 40.** The model
  answers 1: `CAP_LAST_CAP` is 40 (`include/uapi/linux/capability.h`). It
  was 39 at v5.8 and 37 before, so those kernels answer `-EINVAL`.
- **`clone3` and `faccessat2`.** The model answers both. A kernel from
  before riscv64 wired them (`clone3` entered the generic table at v5.3,
  `faccessat2` at v5.8) answers `-ENOSYS` (`sys_ni_syscall`,
  `kernel/sys_ni.c`).
- **A vector with a negative `iov_len` before an unreadable
  descriptor.** The model answers `-EINVAL`: `copy_iovec_from_user` reads
  and tests the descriptors in index order (`lib/iov_iter.c`). Kernels
  before v6.4 copied the whole array first and answer `-EFAULT`.
- **`setsockopt` with a negative `optlen` on a closed or non-socket fd,
  and `getsockopt` at an unknown level.** The model answers the fd's
  `-EBADF` or `-ENOTSOCK`, because `__sys_setsockopt` resolves the fd
  before `do_sock_setsockopt` tests the length, and records the read of
  `*optlen` that `do_sock_getsockopt` makes on every call
  (`net/socket.c`). Kernels before v6.7 test the length first and answer
  `-EINVAL`; kernels before v6.11, except v6.6.51 and later and v6.10.10
  and later, read `*optlen` only while a cgroup getsockopt program is
  attached.
- **A range between `TASK_SIZE` and 2^63 that `access_ok` tests.** The
  model answers `-EFAULT` for it (`__access_ok`,
  `include/asm-generic/access_ok.h`, against riscv64's `TASK_SIZE`).
  From v6.10 until the revert
  `890ba5be6335` (first in v6.16-rc4), and on v6.12.y before .36 and
  v6.15.y before .5, riscv64's `TASK_SIZE_MAX` was `LONG_MAX` and such a
  range passed, so for example `read(0, 2^60, 0)` answered 0.
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
| Signals | The model does not run signal handlers. It has two signals and both are fatal: `SIGABRT`, raised by `tkill`/`tgkill` on the abort path, and `SIGPIPE`, raised by a write whose far end has no reader. Each is behind a declaration of the launch, and with the declaration off the call that would raise it declines: `State.in_abort_terminal` for `SIGABRT` and `State.in_sigpipe_terminal` for `SIGPIPE`, both pinned off by `Run.valid_input`, so no run under the ordinary statements dies by a signal. With the declaration on (`Run.valid_input_abort`; `Run.valid_input_sigpipe_kills` and `Run.valid_input_channel_closed`), each ends the run with a death that is not an exit (`State.KillEv`), or, where the launch mask blocks it, returns the errno and leaves the signal pending until a `rt_sigprocmask` uncovers it. `rt_sigaction` declines every install that would change `SIGABRT`'s disposition. For `SIGPIPE` it answers an install of `SIG_DFL` or `SIG_IGN`, with any flags, and a read of the old action (`Kernel.Signal.rt_sigaction_sigpipe`, `State.procst_sigpipe_action`); an install of a handler address is declined, and so is an install of `SIG_DFL` while the handler is `SIG_IGN` and signal 13 is blocked, because Linux may then hold a pending `SIGPIPE` that the model does not record (the note above `ReadWrite.raise_sigpipe`). For `SIGABRT` the model assumes the launch left the disposition at `SIG_DFL`. For `SIGPIPE` it does not assume, and it does not pin either: the launch declares the starting handler (`State.in_sigpipe_default`) and `Run.valid_input` leaves that declaration FREE, so a statement over it covers both the `SIG_DFL` start and the start whose launcher ran `signal(SIGPIPE, SIG_IGN)` before `execve` — a disposition `execve` preserves (`fs/exec.c`, `begin_new_exec`'s `flush_signal_handlers` with `force_default = 0`, Linux v6.18.46). That is possible because the write that would raise the signal declines under BOTH dispositions while the death is undeclared; where the launch DOES declare the death, `SIG_DFL` kills and `SIG_IGN` returns `-EPIPE` with the program running on. `Run.valid_input_sigpipe_ignored` names the `SIG_IGN` start for a statement that wants to say which start it means. No other signal is modeled: `SIGSEGV` is reported as the error transition rather than as a death, `SIGCHLD`'s default action is to ignore it, `SIGXFSZ` needs an `RLIMIT_FSIZE` the model does not carry, and nothing outside the process can send one. |
| Address-space size | The system call specifications use Sv48. Thus you cannot prove the Sv39 and Sv57 statements for an image that can run. |
| Stack limit | The stack limit is 8 MiB. A larger or unlimited `RLIMIT_STACK`, which selects the legacy mmap layout, is outside the model. The model counts the whole entry block against this limit, from the stack VMA's end `StackLayout.ed_top` down, as Linux counts it. |
| Arguments | `Run.valid_input` requires that the arguments after `argv[0]` do not contain `/` and are not `..`. Thus a proof about `cp src dst` does not apply to `cp /tmp/src dst`. It also bounds the lists (`Run.valid_argv`, `Run.valid_envp`): 1 to 1024 arguments and at most 2 MiB of argument bytes, at most 256 environment variables and at most 128 KiB of environment bytes, and at most 131071 bytes in each string. Each count of bytes includes the terminating NUL of each string. These are the model's own per-list bounds. Linux's own bound is joint, and `Run.valid_launch` carries it: the exec file name, the envp strings and the argv strings with their NULs, plus 8 bytes for each argv and envp pointer, are at most 2 MiB together at the 8 MiB stack limit (`bprm_stack_limits`, `fs/exec.c`). Linux answers `E2BIG` for a larger launch. `Run.valid_launch` also says which exec file names `execve` can present (`State.in_execfn`): a path of 1 to 4095 bytes without a NUL, or `/dev/fd/N`, or `/dev/fd/N/` and such a path that does not start with `/` (`getname_flags` in `fs/namei.c`, `alloc_bprm` in `fs/exec.c`). Both binaries of a pair run under the same exec file name, as they run on the same input. A launch outside these bounds is outside the model. |
| Standard input and output | The fds 0, 1 and 2 are external channels, and their direction is fixed: 0 is read-only, 1 and 2 are write-only (`State.FdChannel`). The model answers `-EBADF` for the other direction. Thus a proof says nothing about a program that is handed a connected socket on fd 0, as an inetd-style server is. |
| Network | The list of connections is never empty. Thus the model does not include an environment where no peer ever connects. |
| Memory budgets | The source can allocate 16 GiB and the target 512 GiB (`State.source_alloc_limit`, `State.target_alloc_limit`). The `*_budgets` statements change this premise. The `*_budgets_only` statements have a finer premise for the source: it excludes a first-touch or a cumulative refusal, but not a single request that is larger than the whole budget (`Run.alloc_refuse_reason`). |
| Files | The file model is a tree of folders, regular files, symbolic links and the two devices `/dev/null` and `/dev/urandom`, and every pathname is walked by its full path from `/` or from the working folder (`Fs.resolve`). The walk follows symbolic links as Linux v6.18.46 does: 40 follows and then `-ELOOP`, every follow also admitting `-ELOOP`, `..` taken from the folder the walk stands on, and a trailing `/` forcing the follow; `openat`, `newfstatat`, `faccessat2` and `readlinkat` follow or not as their flags say, and `unlinkat`, `rmdir` and `mkdirat` act on the link itself. A regular file is an inode: two names of the image may hold one, its link count is its names (`Fs.fs_ino_nlink`), and `st_ino` and `st_dev` are chosen at the first stat of a file, a folder or a device node and then kept for it. A component over 255 bytes admits `-ENAMETOOLONG` beside the answer of a file system with a longer limit, which no supported kernel gives ("Known gaps in precision"). The model answers `getcwd`, `mkdirat` and `rmdir` (`unlinkat` with `AT_REMOVEDIR`). It declines: a pathname whose walk reaches `/proc` or `/sys` (except `/proc/self/fd/N`), through a symbolic link too; `rmdir` of the working folder, of an ancestor of it, or of a folder an open descriptor holds; `rename`, `linkat` and `symlinkat`. It has no file modes or permissions, and no FIFOs or sockets in the image. |
| Shared memory | The model has no shared mapping. `mmap` with `MAP_SHARED` is `unmodeled`, anonymous requests included. Linux builds an anonymous shared mapping on a shmem file (`mm/vma.c`, `__mmap_new_vma` calls `shmem_zero_setup`), so `vma_is_anonymous` is false for it, its pages survive the zap that `MADV_DONTNEED` performs, and a `fork` shares them instead of copying them. `Sys/Mm/Mmap.v` gives the full reason and what an arm would take. |
| The vDSO | The model maps the vDSO text and the four vvar pages that `execve` installs, and answers a call to an exported entry with the system call's own specification (`Run.sstep`'s vDSO arm). It does not run the vDSO's instructions. Four cases are `unmodeled`, and a proof says nothing about a program that reaches one: a load from the vvar pages; a fetch at any text address that is not an exported entry; a call to `__vdso_getrandom` or `__vdso_rt_sigreturn`; and an outcome of a call that returns `-EFAULT`. A store to the text or to vvar is a fault, as on Linux: the kernel maps neither with `VM_WRITE`. The text mapping carries no `x` flag in the model, although Linux maps it `PROT_READ\|PROT_EXEC`: the flag says "the model fetches and executes these bytes", and of the vDSO's bytes it does not. |
| Datagram sockets and eventfds | `socket(AF_INET6 or AF_UNIX, SOCK_DGRAM, 0)` gives a socket (`State.FdDgram`) on which the model answers `close`, `F_GETFL`, an empty `F_SETFL`, the terminal ioctls, `SIOCGIFINDEX` for `lo`, and the errnos of calls that stop before the socket (`-ESPIPE` from `pread64`, `pwrite64` and `lseek`, `-EINVAL` from `fsync` and `ftruncate`, `-ENOTDIR` from `getdents64`); every call that would read or change socket state, and every other protocol or flag of these two families, is `unmodeled`. An eventfd answers `read`, `write`, `select`/`poll`, `fcntl`, the terminal ioctls, `lseek` and `close`; a nonempty `readv` or `writev` on it is `unmodeled`. |
| Unnamed files | A file whose last name `unlinkat` removes while descriptors hold it stays an inode with no name: its descriptors answer every call a named file's descriptors answer, its `fstat` reports `st_nlink` 0, and `openat("/proc/self/fd/N")` opens it again, on the same inode, under `O_RDONLY`, `O_WRONLY\|O_CREAT\|O_TRUNC` and `O_WRONLY\|O_CREAT\|O_APPEND`. |

The entry premises also limit the launches that a statement covers, and
they limit them to Linux's own. For one input and one kernel build
(`State.KernelBuild`), `Run.entry_launch_ok_va` admits exactly the
stack VMA ends, entry stack pointers and mmap bases that a Linux
v6.18.46 launch gives, and `StackLayout.build_stack_bytes` lays Linux's
bytes between the stack pointer and that end, except one word on the
launches R-a below names: there AT_SYSINFO_EHDR is the text base of the
pair the model maps, which is below Linux's. There is no other band. The
three rules are `randomize_stack_top` (`mm/util.c`) and
`setup_arg_pages` (`fs/exec.c`) for the end, `create_elf_tables`
(`fs/binfmt_elf.c`) for the stack pointer, and `mmap_base` with
`arch_mmap_rnd` (`mm/util.c`) for the base. This closes the residual
R-d that earlier revisions named, where `sp` and the base were drawn
apart: `Checks/Cases/EntryLaunch.v`'s `a1_kind1_pair_refused` refutes
its example pair, `sp` = 0x7fffe0000000 with the base at 0x7ffff8000000.

The launch's own facts are therefore premises of each statement:
whether the launch randomises, the `stack_guard_gap` boot parameter,
`vm.mmap_rnd_bits`, the vector unit's `VLENB`, the
machine's four cache leaves, which vDSO image the build carries, and
the socket-buffer numbers: `sizeof(struct sk_buff)` and the
`net.core.wmem_default`, `rmem_default`, `wmem_max` and `rmem_max`
sysctls. They are fields of `State.KernelBuild`, which is part of the
input, so both binaries of a pair are launched on one machine by one
launcher. `State.KernelBuild` also says whether the build has
`CONFIG_RSEQ` (`kb_rseq`) and `CONFIG_TRANSPARENT_HUGEPAGE` (`kb_thp`),
which are not facts a supported launch can vary: the configuration of
record has the first and not the second. A build whose `struct
sk_buff` is larger than 1 KiB is outside the model
(`State.skb_head_bytes`).

`Run.valid_input`, and every named launch beside it, leaves five of
those fields free and fixes the other eight (`Run.recorded_kernel`).
Free: whether the launch randomises, the guard gap, `vm.mmap_rnd_bits`,
`kb_thp` and `kb_rseq`. The published statements
covered a range of each, and a fixed value would narrow them. For
`kb_thp` and `kb_rseq` that is the whole reason: the released placement
took any free address, the 2 MiB-aligned ones a
`CONFIG_TRANSPARENT_HUGEPAGE` build gives included, and the released
entry-stack window admitted the entry stack pointers of both auxv
layouts, where a build without `CONFIG_RSEQ` has a 27-pair auxiliary
vector instead of 29, so its entry stack pointer sits 32 bytes higher.
No supported kernel is either build ("Known gaps in precision"). Fixed at `State.default_kernel`'s
values: vDSO image 1, `kb_vlenb` 0, no cache leaves, a 224-byte
`struct sk_buff` and the default socket sysctls. The published
statements had one answer for each of these. (`kb_vlenb` 0 is the
smallest vector unit, VLENB = 16, on a hart whose `AT_HWCAP` carries
V, and no vector unit otherwise: `State.launch_vlenb`.) The model's
functions accept any build, so a statement about another value of a
fixed field is one that names it; none does yet. Each fixed field has
an accessor per predicate (`Run.valid_input_vdso`,
`Run.valid_input_vlenb`, `Run.valid_input_cache_words` and the like).

These cases stay outside the model:

- QEMU user mode, which is not a supported implementation. It builds
  another entry block entirely; "Where QEMU user mode differs" above
  gives it.
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
- The launch leaves `RLIMIT_FSIZE` at `RLIM_INFINITY`, its initial value
  (`INIT_RLIMITS`, `include/asm-generic/resource.h:14`, Linux v6.18.46),
  and a run cannot lower it: the model answers `prlimit64` for
  `RLIMIT_CORE` only and does not model `setrlimit`. A finite limit makes
  `generic_write_check_limits` (`fs/read_write.c:1713-1721`, Linux
  v6.18.46) send `SIGXFSZ` and answer `-EFBIG` at it, or cut the count to
  it, and the model does neither at such a limit. The other two limits
  there are facts, not assumptions. Every regular-file descriptor has `O_LARGEFILE`: a run
  gets one only from an `openat` the model answers, which is never an
  `O_PATH` one, and a 64-bit kernel sets the flag on every such open
  (`force_o_largefile`, `include/linux/fcntl.h:25`, applied in
  `fs/open.c:1466-1467`, Linux v6.18.46), and `F_SETFL` cannot clear it
  (`SETFL_MASK`, `fs/fcntl.c:37`, Linux v6.18.46), so the 2^31 - 1 limit
  of `generic_write_check_limits` (`fs/read_write.c:1723-1724`, Linux
  v6.18.46) never applies. A pipe's descriptors and a socket's have no
  `O_LARGEFILE` (`create_pipe_files`, `fs/pipe.c:944-946`, and
  `sock_alloc_file`, `net/socket.c:483-485`, Linux v6.18.46), and no
  write to either reaches that function. And no smaller `s_maxbytes` occurs: the
  regular files of a run are on tmpfs or ramfs ("The configuration of
  record"), and both set it to `MAX_LFS_FILESIZE`, `shmem_fill_super`
  (`mm/shmem.c:5118`, Linux v6.18.46) and `ramfs_fill_super`
  (`fs/ramfs/inode.c:267`, Linux v6.18.46).
- The launch image has the standard root (`Fs.standard_root_present`,
  which `Run.valid_input` requires): `/`, `/dev` and `/tmp` are folders,
  and `/dev/null` and `/dev/urandom` are the two devices.
- No regular file of the launch image holds more than 2^63 - 1 bytes
  (`Fs.files_cappedb`, a clause of `Run.valid_image`). Linux
  guarantees it for every file. The clause narrows the statement in two
  cases, both rows of the inode table that no run reaches, since it reads
  every row: a row that `Fs.itab_find` never returns (a later row for an
  inode number that an earlier row already has), and a row whose inode
  number no name of the tree holds (an orphan row: at launch no
  descriptor holds a regular file, since `State.init_model` opens fds 0,
  1 and 2 only, a file the run creates gets a number above every row,
  `Fs.fs_fresh_ino`, and `Fs.fs_observe` drops the row). So it refuses an
  image whose hidden or orphan row is longer than the limit, although no
  lookup reaches that row. Neither row is a file in Linux. A file's size is a
  signed 64-bit `loff_t`, and so is a file system's size limit, the
  `s_maxbytes` (`include/linux/fs.h:1451`, Linux v6.18.46) of its
  superblock. No file system sets that limit above `MAX_LFS_FILESIZE`
  (`include/linux/fs.h:1277-1279`, Linux v6.18.46), which is `LLONG_MAX`
  on 64-bit. `alloc_super` (`fs/super.c:372`, Linux v6.18.46) starts the
  limit at `MAX_NON_LFS`, and `vfs_get_tree` (`fs/super.c:1796-1803`,
  Linux v6.18.46) warns when a file system leaves it negative; its comment
  states the rule. A file grows only up to the limit: a write stops at it
  (`generic_write_check_limits`, `fs/read_write.c:1709-1732`, Linux
  v6.18.46), and so do a truncate (`inode_newsize_ok`, `fs/attr.c:254`,
  Linux v6.18.46) and an `fallocate` (`vfs_fallocate`, `fs/open.c:335`,
  Linux v6.18.46). The regular files of a launch image are on tmpfs or
  ramfs ("The configuration of record"), and rootfs and devtmpfs are each
  one of the two (`rootfs_init_fs_context`, `init/do_mounts.c:499-505`,
  and `devtmpfs_init_fs_context`, `drivers/base/devtmpfs.c:91-98`, Linux
  v6.18.46). Both set the limit to `MAX_LFS_FILESIZE`: `shmem_fill_super`
  (`mm/shmem.c:5118`, Linux v6.18.46) and `ramfs_fill_super`
  (`fs/ramfs/inode.c:267`, Linux v6.18.46).
- Every row of the launch image's folder table holds link counts a kernel
  gives (`Fs.dir_rows_okb`, the last clause of `Run.valid_image`): the row
  names a folder of the tree, its counting count is at least two plus one
  per subfolder the tree shows, and its fixed count is 1. On tmpfs and
  ramfs a folder starts at 2, the 1 of `inode_init_always_gfp`
  (`fs/inode.c:242`, Linux v6.18.46) and the `inc_nlink` of
  `__shmem_get_inode` (`mm/shmem.c:3133-3134`, Linux v6.18.46) or of
  `ramfs_get_inode` (`fs/ramfs/inode.c:77-82`, Linux v6.18.46), and each
  subfolder adds one (`shmem_mkdir`, `mm/shmem.c:3952`, and `ramfs_mkdir`,
  `fs/ramfs/inode.c:122-127`, Linux v6.18.46); a name the image leaves
  out can only add more. `generic_fillattr` reports the count
  (`fs/stat.c:91`, Linux v6.18.46). Without the clause a row could give
  an empty folder the counts 0 and 0, and `stat` of it would answer an
  `st_nlink` of 0. The clause narrows the statement in two cases, both
  rows no lookup reaches: a later row for a key an earlier row already
  has, and a row at a key that is no folder.
- The image describes `/dev` completely at launch, and no device node is
  made during the run. A name under `/dev` that the image does not hold
  is therefore `-ENOENT`. In Linux v6.18.46 devtmpfs makes a node when a
  driver-core device is registered (`devtmpfs_create_node`,
  `drivers/base/devtmpfs.c:129-154`), and a pty open makes one under
  `/dev/pts` (`devpts_pty_new`, `fs/devpts/inode.c:512-547`). A run in
  which a device appears makes this assumption false.
- No inode of the launch file system carries the append-only or the
  immutable attribute (`FS_APPEND_FL`, `FS_IMMUTABLE_FL`, which
  `chattr +a` and `chattr +i` set; with tmpfs built in, devtmpfs is a
  shmem mount, `drivers/base/devtmpfs.c:68-69`, and shmem turns both into
  `S_APPEND` and `S_IMMUTABLE`, `mm/shmem.c:3050-3053`).
  The model has no such attribute, so it never gives the refusals they
  cause in Linux v6.18.46: `may_open`'s `-EPERM` on a write open without
  `O_APPEND`, or an `O_TRUNC` open, of an append-only inode
  (`fs/namei.c:3572-3577`); `inode_permission`'s `-EPERM` on a write open
  of an immutable inode (`fs/namei.c:577-582`); and `kiocb_set_rw_flags`'
  `-EPERM` on a `pwritev2` with `RWF_NOAPPEND` through an `O_APPEND`
  descriptor of an append-only inode (`include/linux/fs.h:3890-3894`,
  reached from `fs/read_write.c:819-821`). A run on such an inode makes
  this assumption false.
- The image holds no `/etc/localtime` (`Run.localtime_absent`): the walk
  of `/etc/localtime` from `/`, following links as an open without
  `O_NOFOLLOW` does, ends at a name the folder it reaches does not hold
  or at a folder that is absent (`Fs.RMissing`, `Fs.RAbsent`). A
  dangling link at `/etc/localtime` or at `/etc` is inside the premise;
  a regular file at `/etc`, or a file or folder at `/etc/localtime`, is
  outside it. So every open of it without `O_CREAT` that follows a link
  at its last name is `-ENOENT`. Under `O_NOFOLLOW` a dangling link at
  `/etc/localtime` is `-ELOOP` (`may_open`, `fs/namei.c:3538-3539`), or
  `-ENOTDIR` with `O_DIRECTORY` (`do_open`, `fs/namei.c:3958-3959`).
- The working folder is outside `/proc` and `/sys` (`Run.outside_proc_sysb`,
  which `Run.valid_input` requires): it is neither folder and lies below
  neither. The model declines `proc` and `sys` only where a walk looks them
  up at `/`, and a relative walk starts at the working folder (`path_init`,
  `fs/namei.c:2590-2604`), so from a working folder inside `/proc` the image
  would answer for procfs (`proc_root_lookup`, `fs/proc/root.c:409-415`). A
  process started in `/proc` or `/sys` is outside the statements.
- The launch file system is one tree, with no bind mount inside it, of a
  folder or of a regular file. So a folder has one name and `..` of a
  folder is the folder whose key is its key's parent, after a symbolic
  link as anywhere else (`follow_dotdot`'s `dget_parent`,
  `fs/namei.c:2083`); and two keys the image shows for one inode are two
  hard links, each counted in the `st_nlink` a stat asserts
  (`Fs.fs_ino_nlink`). A bind mount of a file shows it under a second
  name without raising its link count (`setup_mnt`,
  `fs/namespace.c:1156-1160`, takes the existing dentry;
  `generic_fillattr` reports the unchanged `i_nlink`, `fs/stat.c:91`), so
  a stat of it there would answer a count the model rejects.
- Every folder of the launch tree outside `/proc` and `/sys` is on tmpfs
  or ramfs: no other file system is mounted on a folder of the tree there.
  devtmpfs at `/dev` counts as tmpfs, since it is a shmem mount
  (`drivers/base/devtmpfs.c:68-69`). The model has no file-system type,
  and its arms answer with the operations tmpfs and ramfs install. Another
  file system installs other operations, and the answers change:
  - An mqueue folder has no `->mkdir` (`mqueue_dir_inode_operations`,
    `ipc/mqueue.c:1613-1617`), so `mkdirat` there is `vfs_mkdir`'s
    `-EPERM` (`fs/namei.c:4444-4446`).
  - A name created in an mqueue folder is a queue (`mqueue_create`,
    `ipc/mqueue.c:612-616`), not an empty regular file. Its `i_size` is 80
    (`mqueue_get_inode`, `:307-312`; `FILENT_SIZE`, `:53`), which `fstat`
    reports (`generic_fillattr`, `fs/stat.c:95`), and its
    `mqueue_file_operations` have no `.write` (`:1619-1624`), so a write
    through it is `-EINVAL` (`do_dentry_open`, `fs/open.c:973-975`;
    `vfs_write`, `fs/read_write.c:672-673`).
  - A second procfs instance can be mounted anywhere (`proc_get_tree`,
    `fs/proc/root.c:310-313`). Mounted with `hidepid=1`, it answers
    `-EPERM` for the folder of a process the caller may not inspect, an
    F_OK `faccessat` included (`proc_pid_permission`,
    `fs/proc/base.c:745-771`).
  - A procfs, sysfs or kernfs folder has no `.fsync`
    (`proc_dir_operations`, `fs/proc/generic.c:346-350`; `kernfs_dir_fops`,
    `fs/kernfs/dir.c:1924-1929`), so `fsync` of it is `-EINVAL`
    (`vfs_fsync_range`, `fs/sync.c:183-184`).

  The walk declines the NAMES `proc` and `sys` at `/` (`Fs.at_outside`),
  not a file system, so this premise is what keeps such a mount anywhere
  else out of the statements. The launch environment of the agreement
  checks meets it. The initramfs gives the rootfs, which is tmpfs or ramfs
  (`init_rootfs`, `init/do_mounts.c`), the folders `cases`, `dev`, `proc`,
  `sys`, `tmp` and `work` (`testing/vm/mkinitramfs.py:19`). At boot the
  tracer mounts procfs on `/proc`, sysfs on `/sys` and devtmpfs on `/dev`
  (`testing/vm/tracer.c:2312-2314`). For each case it mounts a fresh tmpfs
  on `/work` and `/tmp` (`:935-936`) and on each top-level folder a seed
  names (`:1287`), and in the case's own mount namespace a tmpfs on `/dev`
  (`:978-979`). It mounts nothing else. A run with any other file system
  mounted on a folder of the tree outside `/proc` and `/sys`, such as an
  mqueue mount at `/dev/mqueue`, makes this assumption false.
- Every mount point of the launch tree is a top-level folder, a child of
  `/`. The model holds no mount table, and a mount point answers `rmdir`
  with `-EBUSY` where the same folder unmounted is removed or answers
  `-ENOTEMPTY`: `do_rmdir` looks the last name up in its parent without
  following the mount (`fs/namei.c:4600-4607`), and `vfs_rmdir` tests
  `is_local_mountpoint` before it calls `->rmdir`
  (`fs/namei.c:4543-4546`, `:4552`). So `unlinkat` with `AT_REMOVEDIR`
  declines a top-level folder (`Fs.Namei.rmdir_spec`). Below the top
  level the premise leaves no mount point, and the bind-mount premise
  above leaves no file or link one, so no other `unlinkat` answers that
  `-EBUSY` (`vfs_unlink`, `fs/namei.c:4669`). `rmdir("/")` is still the
  `-EBUSY` `do_rmdir` gives `LAST_ROOT` (`fs/namei.c:4590-4592`). The
  launch of the agreement checks meets it: each mount the previous
  premise lists is on a top-level folder, `/proc`, `/sys`, `/dev`,
  `/work`, `/tmp`, or a seed root, which `write_seed` mounts only for a
  seed folder whose name has one component (`testing/vm/tracer.c:1306`,
  `:1318`). A run with a mount lower in the tree, such as `/dev/pts`,
  makes this assumption false.
- A write to `/dev/urandom` changes nothing the model holds. Linux mixes
  the bytes into the input pool and credits no entropy
  (`write_pool_user`, `drivers/char/random.c:1420-1446`). The bytes a
  later read takes are the run's declared stream
  (`State.in_urandom`), which is an input over all byte
  streams, so a stream that the write changed in Linux is still one of
  the launches the statements cover.
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
- An in-process stream pair (`socketpair(AF_UNIX, SOCK_STREAM, 0)`,
  `State.FdStream`) is used by this one thread only. Both ends are in
  this process and no modeled call shares one: `dup`, `dup3`, `F_DUPFD`
  and a `clone` holding one are declined, and `sendmsg` on one is
  declined, so no descriptor travels by `SCM_RIGHTS`. A blocking read of
  an empty queue whose peer is open, and a blocking send that might
  wait for room, are declined: on Linux such a call never returns,
  because the only task that could act on the peer is the one that
  waits. A program that reaches either is outside the model. After one
  end is closed, Linux answers the other end's empty read with end of
  file, or first with one `-ECONNRESET` when the closed end left bytes
  unread, and `ppoll` on that end shows `POLLERR` while that error is
  pending. The model's `close` does not record which of the two the
  closed end left, because a `close` that changed another descriptor's
  entry would make false the published lemmas that say a `close` only
  removes its own entry (`theories/Common/FileSim.v`, `tfo_close`). The
  open end's first call that shows the error chooses instead, and the
  end keeps to that choice (`State.se_reset`; see "Known gaps in
  precision"). The empty read is the only call that consumes the error
  in the model, because `getsockopt(SO_ERROR)`, which also consumes it
  in Linux, is declined on a pair end.
- The `net.core` sysctls `wmem_default`, `rmem_default`, `wmem_max` and
  `rmem_max` do not change while the program runs. The model reads them
  from `State.KernelBuild`, which a launch states once; `Run.valid_input`
  fixes them at `State.default_kernel`'s values. Another process that writes
  `/proc/sys/net/core/*` during the run makes this assumption false.
- A send on a stream-pair end never fails with `-ENOBUFS`. Linux's
  `sock_alloc_send_pskb` returns it when the kernel cannot allocate an
  skb, under memory pressure; the model leaves that answer out of
  `Fs.ReadWrite.stream_send`. On the datagram socket kind
  (`State.FdDgram`) no send is answered at all, and its creation admits
  `-ENOBUFS` for `AF_INET6`.
- An eventfd (`eventfd2`, `State.FdEventfd`) is used by this one thread
  only, and no kernel subsystem signals it. `dup`, `dup3`, `F_DUPFD` and
  a `clone` holding one are declined. A blocking read of a zero counter,
  and a blocking write that would take the counter to `ULLONG_MAX`, are
  declined: on Linux such a call never returns, because the only task
  that could change the counter is the one that waits. A program that
  reaches either is outside the model.
- procfs is mounted at `/proc` for the process's own pid namespace, so
  `/proc/self` names this process. The model answers
  `openat(AT_FDCWD, "/proc/self/fd/N", ...)` on that assumption
  (`Fs.Open.openat_procfd_spec`); with no procfs there, Linux answers
  `-ENOENT` where the model opens the file again.
- A hard link of a regular file that the image does not show, a name in
  a folder of the same file system that only another mount of it
  reaches, still counts in the file's link count, and the image says
  how many there are (`Fs.ino_outside`). A bind mount is not such a
  name: it shows a name that exists already and raises no count
  (`setup_mnt`, `fs/namespace.c:1156-1160`; `generic_fillattr` reports
  the unchanged `i_nlink`, `fs/stat.c:91`), and the launch tree holds
  none (the premise on bind mounts above). The model has no `link` or
  `linkat` arm, so the run makes no new name for a file; the names the
  image holds are the only ones it removes.
- The network namespace's loopback device is named `lo`. The model
  answers `ioctl(fd, SIOCGIFINDEX, &ifr)` on an `AF_UNIX` or `AF_INET6`
  datagram socket only for the name `lo`, and answers it with index 1
  (`Fs.Ioctl.siocgifindex_spec`). Linux gives the loopback device the name
  `lo` and the index 1 in every namespace (`loopback_net_init`,
  `drivers/net/loopback.c`; `LOOPBACK_IFINDEX`, `include/net/flow.h`), but
  a privileged process can rename it afterwards, and another device can
  then take the name. Every other name is declined.
- The kernel was booted without `ipv6.disable=1`. With it, `inet6_init`
  returns before it registers the `AF_INET6` family
  (`net/ipv6/af_inet6.c`), and `socket(AF_INET6, ...)` is
  `-EAFNOSUPPORT` where the model answers a descriptor.
- `SIGPIPE`'s start-up disposition is left free, and the
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
  raise `SIGPIPE` declines, at either disposition and whatever the
  mask, so no run
  under the ordinary statements ends by signal 13 and every error-free
  statement keeps the meaning it had before the write arms could raise
  the signal; the declined write is an error. The start-up disposition
  is a declared field too, `State.in_sigpipe_default`, and
  `Run.valid_input` LEAVES IT FREE: a launcher that ran
  `signal(SIGPIPE, SIG_IGN)` before `execve` starts an ordinary Linux
  process — `execve` preserves the disposition (`begin_new_exec` calls
  `flush_signal_handlers` with `force_default = 0`, `fs/exec.c`) — so
  a statement over `Run.valid_input` covers both starts.
  `Run.valid_input_sigpipe_ignored` names the `SIG_IGN` one for a task
  that wants to say which start it means, and on a launch that DOES
  declare the death the disposition is what decides: `SIG_DFL` kills,
  `SIG_IGN` returns `-EPIPE` and the program runs on. **The
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
  `update_mmap_min_addr`). The configuration of record has no such
  option, since it builds no LSM, so the value is the sysctl's, which
  boots at `CONFIG_DEFAULT_MMAP_MIN_ADDR`, 4096 in
  `testing/vm/kernel.fragment`. A run after a writer with
  `CAP_SYS_RAWIO` raised the sysctl (`mmap_min_addr_handler`,
  `security/min_addr.c`) is outside this assumption. The same
  setting moves one length bound: a `MAP_FIXED` call at an error-valued
  address (`2^64-4095` and up) returns that address unless the rounded
  length exceeds `TASK_SIZE - mmap_min_addr` (`mm/mmap.c`,
  `generic_get_unmapped_area`), so with a larger setting Linux answers
  `-ENOMEM` for some lengths where the model returns the address.
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
  the run (`mi_alloc_limit`, a variable of `Run.WithMemImage`) and not a
  reading of any of those settings. Each refusal the budget forces is also
  admissible under the errno `alt` of its arm, so the budget narrows which
  runs a statement covers rather than claiming an answer Linux does not give.
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
  secure mode: `cap_bprm_creds_from_file` (`security/commoncap.c`) is
  the only hook the configuration of record builds, which has no LSM.
  `AT_SECURE` is therefore 0. The model
  also cannot express such a launch: `State.ProcInput` has no effective
  id, so `State.init_model` derives the effective and saved ids from
  the real ones.
- The machine has one view of its caches. `get_cacheinfo`
  (`arch/riscv/kernel/cacheinfo.c`) reads the CPU that runs the
  `execve`, and `State.KernelBuild` holds one `State.CacheView`. The
  kernel's own comment says the interface assumes a homogeneous view.
- No component of the exec file name is longer than 255 bytes
  (`NAME_MAX`). tmpfs and ramfs, the file systems of the configuration
  of record whose regular files hold the bytes written to them ("The
  configuration of record"), refuse a longer component at
  `simple_lookup` (`fs/libfs.c`), so no supported launch's exec file
  there has one. `Run.valid_execfn` bounds the whole name and does not
  look at components, so it admits such a name.
- The file that `AT_EXECFN` names holds the image. On Linux the name
  resolves to the file `execve` loaded. The model holds the image's
  segments, not its file, so `State.in_fs` need not hold a file at that
  name and a program that opens its own `AT_EXECFN` gets the file
  system's answer. `execve` denies write access to that file
  (`exe_file_deny_write_access`, `fs/exec.c:798`), so a write open of it
  is `-ETXTBSY` (`get_write_access` in `do_dentry_open`,
  `fs/open.c:925-928`) and empties nothing. The model cannot tell which
  file of the image that is, so it admits `-ETXTBSY` beside every write
  open of an existing regular file no descriptor of the model already
  writes (`Sys.Fs.Open.open_write_existing`; a writer keeps the inode's
  write count positive, which no deny can then be taken against,
  `include/linux/fs.h:3217-3222`): the real answer is admitted, and on
  files nothing executes the admission is a trace no supported kernel
  gives.
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

## Soundness gaps

Design priority 1 asks that every behavior Linux v6.18.46 can give, in a
case the model covers, is a behavior of the model (README.md). The model
does not meet it in the cases below. In the first two, R-a and R-b, **the
model can NAME A DIFFERENT ADDRESS from the one Linux gives for a
placement above `State.alloc_top`; wherever it still can, a proof does
not cover
them.** They are priority-1 gaps. They break priority 2 as well, since
the model then gives an address Linux does not give in that state, so
each is both kinds of gap and the entry is here because the priority-1
half is the serious one. A statement that
a proof can establish in the model — "a non-fixed `mmap` returns an
address below `sp`" — is then false of Linux. There are two fixes: to
answer `unmodeled` for such a placement, which the model now does for a
hint (`Sys/Mm/Mmap.v`, `place_declined_b`), or to raise the ceiling,
which is open and is what R-a needs. One word throughout this document:
a call the model DECLINES is one it answers `unmodeled` for. Naming a
different address from Linux's is not a decline — it is the defect R-a
and R-b record.

- **R-a, an mmap base above `State.alloc_top`.** The model's zero-mapped
  stack window now counts its 8 MiB from the end of the entry block
  (`Run.stack_window_lo`: `StackLayout.ed_top` less `stack_max_size`,
  against a guard-gap floor), as Linux counts RLIMIT_STACK from the stack
  VMA's `vm_end` (`expand_downwards` through `acct_stack_growth`,
  `mm/vma.c`). LPS pull request #25, which moved that count off `sp` and
  onto the entry block, is merged; `ed_top` and the guard-gap floor came
  after it. The gap stays open because the ALLOCATION ceiling was not
  moved with the window: `State.alloc_top` is still
  `vm_init_sp - stack_max_size`, that is `sp - 8 MiB` (`State.alloc_top`),
  while `sp` sits below the stack VMA's end by the entry image. The model
  admits exactly Linux's bases (`Run.valid_launch_base`, which mirrors
  `mmap_base`, `mm/util.c`: `STACK_TOP` less a gap of the stack rlimit,
  the guard gap and the stack randomization maximum, less a base draw),
  and with a large stack draw and an entry image of more than about 1 MiB
  — the guard-gap pad in that gap, at the default `stack_guard_gap`, which
  `State.kb_guard` leaves free — an admitted `mm->mmap_base` lies above
  `State.alloc_top`, below which the model searches.
  The model's top-down addresses are then lower than Linux's by at most
  the entry image size less that pad, so until this is fixed a proof does
  not cover a run whose mapping Linux puts above `State.alloc_top`. The
  vDSO moves with it: the model maps the pair, and the ledger reserves
  it, below `page_round_down(min(mbase, sp - 8 MiB))` (`Run.vdso_pair_top`,
  `State.vdso_top`), and the auxv publishes that pair's own text base
  (`Run.vdso_text_base`), so a C library finds the vDSO where the model
  mapped it. Where `mbase` is above `State.alloc_top` that is lower than
  Linux's pair, which sits directly below `mm->mmap_base`, so on those
  launches the entry block's AT_SYSINFO_EHDR is not the value Linux
  publishes either.
  The refusals differ only when no free
  range of the requested size is left, and the band is narrow: about the
  entry image less the guard-gap pad, and at most 2,109,440 bytes
  (`0x203000`) over the entries `Run.valid_entry` admits. That maximum
  is at a stack top (`StackLayout.ed_top`) of `0x7fffc0000000`, the
  lowest the stack draw admits, `sp` of `0x7fffbfdfedf0`, the entry
  block at `valid_launch`'s 2 MiB cap, and a base of `0x7fffbf801000`,
  with `kb_aslr` on, `kb_guard` zero and the mmap draw zero:
  `State.mmap_top` is `min(mbase, page_round_down(alloc_top))`, so the
  band is `mbase - page_round_down(sp - 8 MiB)` =
  `0x7fffbf801000 - 0x7fffbf5fe000` = `0x203000`. A nonzero `kb_guard`
  lowers `mbase` and narrows it, so the figure holds at
  `stack_guard_gap` zero and bounds every other launch.
  Answering `unmodeled` for each such `mmap` would NOT close R-a:
  `State.init_reserved` puts the vdso/vvar pair at
  `page_round_down(min(mbase, sp - 8 MiB))`, so for exactly those
  entries the model's START STATE already places the pair below where
  Linux's first `get_unmapped_area` places it, and declining every
  later `mmap` would leave that difference standing. Raising
  `State.alloc_top` to the
  floor `Run.stack_window_lo` already uses closes it.
- **R-b, a hint or a fallback above `State.alloc_top`: the hint half is
  answered `unmodeled` where R-a does not bite, the fallback half is
  open.** Linux honours a
  free address hint anywhere up to `STACK_TOP_MAX`, which is 2^47, the band
  above the stack included, and its bottom-up fallback searches up to the
  same limit, which reaches the guard gap below the stack
  (`mm/mmap.c:753-761`,
  `generic_get_unmapped_area_topdown`: the hint test is
  `mmap_end - len >= addr` with the two gap tests, and the fallback sets
  `info.high_limit = mmap_end`; `arch/riscv/include/asm/processor.h`,
  `arch_get_mmap_end`, which gives `STACK_TOP_MAX`). The model honours a
  hint, and searches, only below `State.alloc_top`: `Sys.Mm.Mmap.linux_place`
  tests the hint with `gap_fits maps page_size (alloc_top h) nZ g`, and
  `Sys.Mm.Mmap.topdown_search` uses `alloc_top` for `mmap_end`. So the
  defect is not only a difference in which free address is chosen: where
  Linux RETURNS a hint above `State.alloc_top`, the model would put the
  mapping somewhere else entirely, at a top-down address of its own, and
  so NAME A DIFFERENT ADDRESS FROM LINUX.
  **The hint half.** The model now DECLINES such a call — answers
  `unmodeled` for it — when the hinted range is free on the ledger,
  starts at or above `mmap_min_addr` and ends above `State.alloc_top`
  and at or below `State.TASK_SIZE` (`Sys/Mm/Mmap.v`,
  `place_declined_b`). That decline is complete only for the entries
  whose mmap base is at or below the page-rounded `State.alloc_top`. On
  the others R-a has already placed the model's vdso/vvar pair lower
  than Linux placed it, so a hinted range can meet the model's pair
  while Linux's lies elsewhere and Linux honours the hint: `region_free`
  is false, the decline does not fire, and the mismatch stands. That is
  R-a's defect and R-a's to close; it is named here so no reader takes
  the hint half as closed for every admitted launch. In the other
  direction the decline costs coverage and not soundness: "free on the
  ledger" above `State.alloc_top` does not mean free on Linux, since the
  band is where the stack grows, so some calls are declined at which the
  model and Linux would have agreed.
  **The fallback half** stays open. Reaching it needs a ledger with no
  free range of the requested size anywhere below `State.alloc_top` —
  about 2^47 bytes of address space — before Linux's extra band can hold
  an answer the model does not have. Deciding it needs an executable
  "no fit in either window" test inside the trusted layer, which
  `Sys/Mm/Mmap.v` does not have and which `Checks/Placement.v` may not
  supply, the dependency running the other way. It stays open for the
  reason it always did:
  the dynamic stack is a bound in this model and not an entry in the
  ledger, so the model cannot tell a free address above the stack from the
  stack itself. The stack VMA in the ledger closes it. Until then, a
  proof does not cover a run in which Linux falls
  back above `State.alloc_top`.
- **R-c, a hint inside the grown stack's guard gap: the hint half is
  answered `unmodeled`, the `brk` half is open**, whose full entry
  is under "Known gaps in precision" below. Linux's hint test respects
  `vm_start_gap` (`mm/mmap.c:758`, the hint arm of
  `generic_get_unmapped_area_topdown`; `include/linux/mm.h`,
  `vm_start_gap`), so with the stack grown to its limit Linux REFUSES a
  hint that ends inside `stack_guard_gap` below it and searches
  top-down instead. The model's ledger has no stack VMA and so no gap
  to keep: `Sys.Mm.Mmap.linux_place` returned that hint, and its
  placement is unique (`Checks.Placement.linux_place_unique`), so the
  address Linux returns was left out. The model now DECLINES such a
  call — answers `unmodeled` for it — so no proof claims that address
  any more; the `brk` side of the same gap is untouched by that gate
  and stays open, as its full entry says.
- **The stack floor after a later mapping**, under "Known gaps in
  precision" below. A program that maps a page just below its stack and
  then grows the stack into the guard gap above that mapping faults on
  Linux, and the model answers instead: that `SIGSEGV` is not a behavior
  of the model, so a proof does not cover such a run.
- **A failing store-conditional on a write-only segment**, whose full
  entry is under "Known gaps in precision" below. On a writable segment
  that lacks the `r` flag the model's failing `sc` takes a
  `MachineFault` — a death, and deliberately not `unmodeled` (`Run.v`
  excludes `MachineFault` from the unmodeled cases as "a faithful model
  of a process that really does die"). Where Linux instead lets that
  `sc` report failure and the program run on, that run is a behavior
  Linux gives and the model does not, so a proof does not cover it.
  **Whether Linux does is UNSETTLED**: a private write-only mapping
  takes a page table entry with no `_PAGE_READ`, so the hardware may
  fault there as the model does. The entry below says what would settle
  it.
- **A store-conditional the hart fails although the reservation holds.**
  The model's `Sc` arm (`theories/Riscv/Sem.v`) makes an `sc` whose
  address is the reserved one store and write 0 to `rd`, with no other
  outcome. The ISA gives success only necessary conditions ("An SC may
  succeed only if ...", Zalrsc), so a conforming hart may fail that `sc`
  and Linux passes the failure to the program. That run is a behavior a
  supported implementation can give and the model does not, so a proof
  does not cover it. Whether the model will admit the failure, or
  declare a premise about the hart instead, is open
  (`bugs/riscv-sc-never-fails-spuriously.md`).

## Known gaps in precision

Design priority 2 asks that the model include no behavior that Linux
v6.18.46 does not give. The model does not meet it in these cases. In each
case, a statement that compares sets of behaviors (for example,
equivalence) can be true of the model and false of Linux. Five entries
belong to both lists: R-a and R-b, recorded above under "Soundness
gaps", and R-c, "Stack floor" and the failing store-conditional, whose
full entries are here and which "Soundness gaps" names. Each also leaves
out something Linux does, which breaks priority 1, and that is the more
serious half.

- **No parameter for the Linux configuration.** The model does not choose
  between Linux configurations (for example, the two mmap layouts). Where
  they differ, the model lets each system call choose again. A real system
  makes the choice the same way each time. Also, the source and the target
  can make different choices, as if they ran on different machines.
  "Assumptions that the model does not check" above pins each
  configuration the model does fix. This holds for the system calls. It
  does not hold for the start state: the launch's randomisation mode, its
  guard gap, its `vm.mmap_rnd_bits`, its vector unit, its caches, its
  vDSO image and the `kb_thp` and `kb_rseq` flags (the next two
  entries) are fields of `State.KernelBuild`, which
  the two binaries of a pair share, so there the model does carry a
  parameter for the machine and both binaries read the same one.
  `Run.valid_input` fixes the vector unit, the caches, the vDSO image and
  the socket numbers, and leaves the other five free.
- **An auxiliary vector without the rseq pair.** `Run.valid_input`
  leaves `kb_rseq` free, so beside the 29-entry vector every supported
  kernel lays ("The configuration of record") the model admits the
  27-entry vector of a build without `CONFIG_RSEQ`, with its entry stack
  pointer 32 bytes higher (`StackLayout.auxv_count`). No supported kernel
  gives that block, so a statement that compares sets of behaviors can
  count a launch no supported kernel makes. Nothing Linux gives is left
  out, so the model stays sound; the flag stays free because the
  published statements' entry-stack window admitted both layouts
  (`Run.recorded_kernel`).
- **A 2 MiB-aligned anonymous placement.** `Run.valid_input` leaves
  `kb_thp` free, so beside the placement every supported kernel gives
  ("The configuration of record") the model admits the padded,
  2 MiB-aligned search a `CONFIG_TRANSPARENT_HUGEPAGE` build runs for an
  anonymous request with no hint whose length is a multiple of 2 MiB
  (`thp_get_unmapped_area_vmflags`, `mm/huge_memory.c`; `Sys/Mm/Mmap.v`,
  `thp_align`). No supported kernel runs that search, so the model can
  name an address no supported kernel gives. Nothing Linux gives is left
  out, so the model stays sound; the flag stays free because the
  published statements' placement admitted any free address
  (`Run.recorded_kernel`).
- **A folder whose link count stays 1.** Beside the counting rule of
  tmpfs and ramfs, the file systems of the configuration of record,
  under which a folder starts at 2 and gains one for each subfolder,
  `Fs.DirLinks` admits btrfs's fixed rule, under which every folder's
  `st_nlink` is 1 (`Sys/Fs/Stat.v`, `dir_nlink_ok`); the first `stat`
  that tells the two apart chooses one for the folder. No supported
  kernel builds btrfs, so the model can report a count no supported
  kernel gives. Nothing Linux gives is left out, so the model stays
  sound.
- **A component over 255 bytes.** `simple_lookup` (`fs/libfs.c`), the
  lookup of tmpfs and ramfs, answers `-ENAMETOOLONG` for a component
  longer than `NAME_MAX`. The walk admits that answer, and beside it
  the answer of a file system with a longer limit (`Fs.comp_too_long`,
  `Fs.wr_long`): an `-ENOENT`, a new descriptor or a removal that no
  supported kernel gives. Nothing Linux gives is left out, so the model
  stays sound.
- **Clock resolution.** For supported non-CPU clock IDs, `clock_getres`
  accepts any positive nanosecond value below one second. Linux returns
  1 ns or a tick-based resolution (`posix_get_hrtimer_res` and
  `posix_get_coarse_res`, `kernel/time/posix-timers.c`), and which of the
  two, and the value of `hrtimer_resolution`, follow the kernel build and
  the boot (`CONFIG_HIGH_RES_TIMERS`, `CONFIG_HZ`). The model does not
  constrain later calls to use the same resolution.
- **The count of a non-blocking send on a stream pair.** Linux cuts the
  send into skbs and stops at the first one that the sender's
  `sk_wmem_alloc`, counted in TRUESIZE, does not admit
  (`unix_stream_sendmsg`, `sock_alloc_send_pskb`). Truesize depends on
  kmalloc rounding, which the model does not carry. So
  `State.stream_send_ok` admits every count from the first skb's size
  to the bound the send buffer allows, and Linux gives only some of
  them; and a send onto a non-empty queue may answer `-EAGAIN` where
  Linux would admit one more skb. Readiness has the same cause: in the
  band where `unix_writable` turns on truesize, `ppoll` and `pselect6`
  admit both answers to a request for POLLOUT, writable and not
  writable, and Linux gives the one that truesize decides. The choice is
  made once for each end in a call, so two `ppoll` entries for one end
  get the same answer, as in Linux.
- **The open end's error after the peer of a stream pair closed.** Linux
  sets `sk_err` to `ECONNRESET` on the open end when the closing end
  left bytes unread (`unix_release_sock`, `net/unix/af_unix.c`). The
  first empty read returns it and clears it, and `ppoll` shows `POLLERR`
  while it is set. The model does not say which answer Linux gives,
  only that it gives one and keeps to it: the open end's first call
  that shows the error (an empty `read`, `readv` or `recvfrom`, or a
  `ppoll` that names the end) admits both answers, and records the
  answer that it gave in the end (`State.se_reset`). After that, every
  call on the end answers from the record: one `-ECONNRESET` at most,
  then end of file, and `POLLERR` set only until that `-ECONNRESET`.
  `pselect6` has one answer on that end and records nothing. A proof
  about such a run must cover both branches
  (`theories/LinuxProcessSem/Checks/StreamReset.v`).
- **The remaining time of `pselect6` and `ppoll`.** When a call with a
  real timeout returns before the timeout runs out, Linux writes the
  time left to `*tsp` (`poll_select_finish`, `fs/select.c`). The model
  admits every normalized time from 0 to the timeout. It does not tie
  that time to the clock: `State.m_clock` does not move, so a later
  `clock_gettime` is not bounded by the time that the call took, as it
  is on Linux.
- **R-c, the stack guard gap: the hint half is CLOSED by a decline, the
  `brk` half is open.** When the stack has grown to its limit, Linux
  keeps a mapping `stack_guard_gap` below it: the hint test and the
  search subtract that gap from the start of a `VM_GROWSDOWN` VMA
  (`mm/mmap.c:758`, `addr + len <= vm_start_gap(vma)` in
  `generic_get_unmapped_area_topdown`; `include/linux/mm.h`,
  `vm_start_gap`, through `stack_guard_start_gap`; `vm_end_gap` is the
  matching rule above a `VM_GROWSUP` VMA). The gap is 256 pages by
  default and any page count the `stack_guard_gap=` boot parameter
  names (`mm/mmap.c:941-954`), which the model carries as
  `State.stack_guard_gap_bytes` of the run's `State.KernelBuild`.
  The HINT half was a soundness break of the same shape as R-b's:
  Linux refuses a hint whose range ends inside the gap and answers a
  lower address from its top-down search, while `Sys/Mm/Mmap.v`,
  `linux_place` honoured the hint, the ledger having no stack VMA and
  so no gap to keep. The model now answers `unmodeled` for a hint
  whose range is free on the ledger, starts at or above
  `mmap_min_addr` and ends above
  `State.alloc_top - State.stack_guard_gap_bytes kb`
  (`Sys/Mm/Mmap.v`, `place_declined_b`), with the same limit R-b's
  decline has: it is complete only for the entries whose mmap base is
  at or below the page-rounded `State.alloc_top`.
  THE DECLINE IS WIDER THAN THE GAP, because the ledger cannot say
  where the stack starts. `State.VmMaps` has no stack entry and no
  stack extent; its only stack term is
  `State.alloc_top = vm_init_sp h - 8 MiB`, the deepest the stack may
  ever reach, while the start it has actually reached is
  `Run.stack_window_lo`, a function of the launch and not of the
  ledger. So "the stack has grown to its limit" is not expressible
  here, and the model declines every hint ending in the gap-wide band
  below `State.alloc_top` — 1 MiB on `State.default_kernel`. On a run
  whose stack has not grown that far, Linux honours such a hint and
  the model declines: coverage lost, not soundness. The stack VMA, and
  the extent it has reached, in the ledger is what tightens it.
  The SEARCH needs no decline for the gap: `State.mmap_top` bounds it
  by the recorded mmap base, which Linux put at least
  `RLIMIT_STACK + stack_guard_gap` below the stack top (`mm/util.c`,
  `mmap_base`), so neither rule's search reaches the gap — except
  where the page-rounded `State.alloc_top` is the smaller bound, which
  is R-a.
  The `brk` half stays OPEN: Linux refuses a grow to within a page and
  `stack_guard_gap` of the stack's start, because the `vma_find` at
  `SYSCALL_DEFINE1(brk)` (`mm/mmap.c:183-190`) searches up to
  `newbrk + PAGE_SIZE + stack_guard_gap` and compares against
  `vm_start_gap(next)`. `Sys/Mm/Mmap.v`, `brk_grow_ok` tests only the
  installed pages and the one page above them, against a ledger with no
  stack VMA in it, so `State.alloc_top` stands in for that refusal — and
  stands in for it only while the stack has not grown to within
  `stack_guard_gap` and a page of that bound. `brk` does not take the
  placement path's gate, so the decline above does not reach it. The
  stack VMA in the ledger closes this too.
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
  (`State.in_urandom`): the source and the target see the same
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
  (`State.in_channel_reader`). `Run.valid_input` pins that
  field present, so every ordinary statement is about the run whose
  standard output is read; the writing end of `prog | head -1` is
  `Run.valid_input_channel_closed`, named the way
  `Run.valid_input_abort` names the aborting launch, and a statement
  that means both readings asks for `Run.valid_input_channel_either`:
  the model pins the reader, and names the reader-gone launch so a
  proof can ask for it.
  What is left is NOT the
  SIGPIPE disposition: that was an unstated premise and is now a
  declaration (`State.in_sigpipe_default`), which
  `Run.valid_input` leaves FREE — both starts are covered, because the
  write that would raise the signal declines under each while the
  death is undeclared — with
  `Run.valid_input_sigpipe_ignored` for a statement that wants to name
  the launch that ignored the
  signal; see "Signals". What is left is that the model has ONE answer
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
  the same bytes, so on a writable segment that lacks the `r` flag the
  load half fails (`RiscvSemantics.memory_read` gives `None` when
  `seg_readable` is false) and the run takes a `MachineFault`. That is a
  death, not `unmodeled`, which is why "Soundness gaps" above names this
  entry too: where Linux lets the `sc` report failure and the program
  run on, the model leaves out a behavior Linux gives, and that is the
  more serious half.
  **What Linux does here is unsettled, and it decides whether this is a
  gap at all.** `access_error`'s "Write implies read"
  (`arch/riscv/mm/fault.c`) is a test on the VMA flags, but the page
  table entry comes from `protection_map`, and a PRIVATE write-only
  mapping takes `PAGE_SHADOWSTACK` (`arch/riscv/mm/init.c`,
  `protection_map[VM_WRITE]`), which is `_PAGE_BASE | _PAGE_WRITE` with
  no `_PAGE_READ` (`arch/riscv/include/asm/pgtable.h`). A SHARED
  write-only mapping takes `PAGE_SHARED`, which is `PAGE_WRITE` and does
  carry `_PAGE_READ`. So in the private case the hardware may fault on
  the load exactly as the model does, and the model may be right.
  **What would settle it:** run a failing `sc` against a private
  write-only `mmap` on riscv hardware, or on an emulator that honours
  the page table bits, and record whether it faults or the `sc` reports
  failure.

## What the proofs do not check

- The executable checker of each system call is proved to agree with its
  specification. This does not show that the specification agrees with
  Linux. An error in both gives a correct proof of the wrong thing.
- Comments that state kernel behavior name the file and the function in
  Linux v6.18.46. No tool checks that these comments are correct.
- No recorded trace reaches the `SIG_IGN` arm of the `SIGPIPE` write. The
  replay corpus (`reports/corpus-replay.md`, 4,291 traces) records no
  start-up disposition at all, and the replay starts every trace at
  `SIG_DFL`; the two installs of `SIG_IGN` for signal 13 anywhere in it,
  `rt_sigaction_spec/039` and `rt_sigaction_spec/040`, each have that
  call as the trace's only record, and no `-EPIPE` record follows an
  install of a signal-13 disposition.
  So what the model answers at `SIG_IGN` on a launch that DOES declare the
  death (`State.in_sigpipe_terminal`, the launches
  `Run.valid_input_sigpipe_kills` and `Run.valid_input_channel_closed`
  name) — the write returns `-EPIPE` and the program runs on — is
  exercised only by the fixtures in
  `theories/LinuxProcessSem/Checks/Cases/Fs/ReadWrite.v:2977-3065`, and by
  no recorded run, until a re-recorded corpus holds such a trace.
  Under `Run.valid_input` the death is undeclared and the write declines
  at either disposition, so that arm is not reached there at all.
