# The riscv64 vDSO image of Linux v6.18.46

This directory holds the measurement of the riscv64 vDSO image of Linux
v6.18.46. The real deliverable is `vdso-measurements.json`.

## Result in one view

| Item | Value |
| --- | --- |
| Kernel commit | `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5` (tag `v6.18.46`) |
| Distinct images | 1 |
| Size | 5704 bytes |
| Pages | 2 |
| SHA-256 | `0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36` |
| First 4 bytes | `7f 45 4c 46` |
| Symbol hash | `DT_GNU_HASH`. `DT_HASH` is absent. |
| Dynamic symbols | 11 |
| Exported functions | 8, all with version `LINUX_4.15` |
| `F`, the largest frame | 240 bytes |

Three configurations were built. All three give the same bytes. Read
"Configurations" below.

## Files

| File | Content |
| --- | --- |
| `vdso-defconfig.so` | The image from the `defconfig` build. |
| `vdso-defconfig-thp.so` | The image from the `CONFIG_TRANSPARENT_HUGEPAGE=y` build. |
| `vdso-defconfig-norandom.so` | The image from the no-randomisation build. |
| `measure_vdso.py` | The measurement script. It uses the standard library only. |
| `vdso-measurements.json` | The measurement, one JSON object per image. |
| `vdso_images.v.in` | A plain-text dump of the page count, the hex chunks and the symbols. |
| `crosscheck/` | The `readelf` output, the `objdump` output, the three `.config` files and the toolchain versions. |

## The machine and the container

The build ran on the GCE VM `ossv-lpsrev-vdso`. It has 32 vCPUs. No build
ran on sami-rocqperf.

The toolchain ran in a Docker container. The image is `vdsobuild:1`. Its id
is
`sha256:b2a3aaad7a485cbd9a372bd4aa068ce0ecc60e92125c195b6a39af95a8dfade7`.
The `Dockerfile` is:

```dockerfile
FROM debian:trixie
RUN apt-get update && apt-get install -y --no-install-recommends \
    gcc-riscv64-linux-gnu binutils-riscv64-linux-gnu \
    build-essential python3 bc flex bison libelf-dev libssl-dev make \
    rsync kmod cpio xz-utils \
 && rm -rf /var/lib/apt/lists/*
```

The toolchain versions are:

```
riscv64-linux-gnu-gcc (Debian 14.2.0-19) 14.2.0
GNU ld (GNU Binutils for Debian) 2.44
GNU objdump (GNU Binutils for Debian) 2.44
GNU readelf (GNU Binutils for Debian) 2.44
```

## Get the source

```bash
git clone --depth 1 --branch v6.18.46 \
  https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git
cd linux && git rev-parse HEAD
```

`git rev-parse HEAD` printed
`1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`. The tag resolves to the
commit the task names.

## Which file the kernel maps

The kernel maps the **stripped** file `arch/riscv/kernel/vdso/vdso.so`.
Three facts show this:

1. `arch/riscv/kernel/vdso/Makefile` runs `OBJCOPY -S` from `vdso.so.dbg`
   into `vdso.so`.
2. `arch/riscv/kernel/vdso/vdso.S` does `.incbin "arch/riscv/kernel/vdso/vdso.so"`
   between the labels `vdso_start` and `vdso_end`.
3. `arch/riscv/kernel/vdso.c` builds `vdso_pagelist` from the pages between
   `vdso_start` and `vdso_end`.

The measurement reads `vdso.so`. It does not read `vdso.so.dbg`.

## Configurations

### Configuration 1, defconfig

```bash
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 defconfig
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 olddefconfig
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 -j32 prepare
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 -j32 arch/riscv/kernel/vdso/
```

The last command builds the directory. The target
`arch/riscv/kernel/vdso/vdso.so` has no rule in an `O=` build. The
directory target builds `vdso.so`, because `vdso.o` depends on it.

### Configuration 2, defconfig and CONFIG_TRANSPARENT_HUGEPAGE=y

```bash
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 defconfig
./scripts/config --file /out/c1/.config -e TRANSPARENT_HUGEPAGE
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 olddefconfig
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 -j32 prepare
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 -j32 arch/riscv/kernel/vdso/
```

The `.config` differs from defconfig in 14 lines. `crosscheck/config-diff-thp.txt`
holds the difference.

### Configuration 3, defconfig and no randomisation

```bash
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 defconfig
./scripts/config --file /out/c2/.config -e COMPAT_BRK -d RANDOMIZE_BASE -d RANDOMIZE_KSTACK_OFFSET
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 olddefconfig
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 -j32 prepare
make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 -j32 arch/riscv/kernel/vdso/
```

The `.config` of this configuration is byte-identical to the defconfig
`.config`. `crosscheck/config-diff-norandom.txt` is empty. Three reasons:

1. riscv defconfig already sets `CONFIG_COMPAT_BRK=y`. The brk is not
   randomised.
2. riscv defconfig already leaves `CONFIG_RANDOMIZE_BASE` unset.
3. `arch/riscv/Kconfig` selects `CONFIG_RANDOMIZE_KSTACK_OFFSET`, so
   `olddefconfig` sets it again.

Kconfig has no option for vDSO or mmap randomisation. `norandmaps` is a boot
parameter.

### The three images are one image

```
0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36  vdso-c0.so
0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36  vdso-c1.so
0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36  vdso-c2.so
```

The vDSO image does not depend on `CONFIG_TRANSPARENT_HUGEPAGE`. Report one
distinct image, not three. `vdso-measurements.json` still holds three
objects, one per delivered file.

## How to read the measurement

Run the script on sami-rocqperf:

```bash
python3 measure/measure_vdso.py measure/vdso-defconfig.so > out.json
```

The script needs Python 3 and no other package. It does not call `readelf`
or `objdump`.

The script reads the ELF header with `struct`. It finds `PT_DYNAMIC`. It
reads `DT_SYMTAB`, `DT_STRTAB` and `DT_VERSYM` from it. It maps each
virtual address to a file offset through the `PT_LOAD` header. This is the
path musl's `__vdsosym` takes.

The script counts the dynamic symbols as musl does. musl reads the count
from `DT_HASH` when `DT_HASH` is present. This image has no `DT_HASH`, so
the count comes from `DT_GNU_HASH`. The count is 11.

## The ELF facts

| Field | Value |
| --- | --- |
| `e_phoff` | 64 |
| `e_phnum` | 4 |
| `e_phentsize` | 56 |
| `e_machine` | 243 (`EM_RISCV`) |

| Program header | `p_offset` | `p_vaddr` | `p_filesz` | `p_memsz` | `p_flags` |
| --- | --- | --- | --- | --- | --- |
| `PT_LOAD` | 0x0 | 0x0 | 4646 | 4646 | R+X |
| `PT_DYNAMIC` | 0x378 | 0x378 | 288 | 288 | R |
| `PT_NOTE` | 0x4a0 | 0x4a0 | 60 | 60 | R |
| `PT_GNU_EH_FRAME` | 0x4dc | 0x4dc | 44 | 44 | R |

`PT_LOAD` covers 4646 of the 5704 bytes. The bytes above 4646 are the
section headers and the section name table. The kernel maps all 5704 bytes,
because it maps whole pages from `vdso_start` to `vdso_end`.

The dynamic entries are:

| Tag | Value |
| --- | --- |
| `DT_SONAME` | 0x9a |
| `DT_GNU_HASH` | 0x120 |
| `DT_SYMTAB` | 0x168 |
| `DT_STRTAB` | 0x270 |
| `DT_STRSZ` | 0xb5 |
| `DT_SYMENT` | 0x18 |
| `DT_RELA` | 0x0 |
| `DT_RELASZ` | 0x0 |
| `DT_RELAENT` | 0x18 |
| `DT_VERSYM` | 0x326 |
| `DT_VERDEF` | 0x340 |
| `DT_VERDEFNUM` | 2 |

`DT_HASH` is absent. `DT_GNU_HASH` is present.

## The exported symbols

| Name | Offset | Size | Version |
| --- | --- | --- | --- |
| `__vdso_rt_sigreturn` | 0x0590 | 8 | `LINUX_4.15` |
| `__vdso_clock_gettime` | 0x05b4 | 698 | `LINUX_4.15` |
| `__vdso_gettimeofday` | 0x0870 | 500 | `LINUX_4.15` |
| `__vdso_clock_getres` | 0x0a64 | 144 | `LINUX_4.15` |
| `__vdso_getcpu` | 0x0af8 | 10 | `LINUX_4.15` |
| `__vdso_flush_icache` | 0x0b04 | 10 | `LINUX_4.15` |
| `__vdso_riscv_hwprobe` | 0x0b10 | 284 | `LINUX_4.15` |
| `__vdso_getrandom` | 0x0c3c | 552 | `LINUX_4.15` |

`__vdso_getrandom` is exported. riscv defconfig sets
`CONFIG_VDSO_GETRANDOM=y`, because `arch/riscv/Kconfig` line 226 selects it
for a 64-bit build.

## The cross-check

The cross-check command is:

```bash
riscv64-linux-gnu-readelf -W --dyn-syms -V vdso.so
```

Its output is in `crosscheck/readelf-dyn-syms-defconfig.txt`. The script
holds the same text and compares its own result against it. The script
agrees with `readelf` on the offset, the size and the version of all 8
exported symbols. The JSON field `crosscheck_readelf.agree` is `true`.
`crosscheck/measure-stderr.txt` holds the printed comparison.

## F, the largest frame

`F` is 240 bytes.

The script decodes every RV64GC instruction of every function that an
exported entry can reach by a direct call. It adds the `sp` decrements
along each call chain. The deepest chain is `__vdso_getrandom` into
`__arch_chacha20_blocks_nostack` at 0xe68.

```
 c3c: addi sp,sp,-144    <__vdso_getrandom>
 d0c: jal  e68           <__arch_chacha20_blocks_nostack>
 e68: addi sp,sp,-96     <__arch_chacha20_blocks_nostack>
```

144 + 96 = 240.

The frame of each exported entry is:

| Entry | Own frame | With its callees | Chain |
| --- | --- | --- | --- |
| `__vdso_rt_sigreturn` | 0 | 0 | — |
| `__vdso_clock_gettime` | 64 | 80 | `cpu_relax` at 0x59c adds 16 |
| `__vdso_gettimeofday` | 48 | 64 | `cpu_relax` at 0x59c adds 16 |
| `__vdso_clock_getres` | 16 | 16 | — |
| `__vdso_getcpu` | 0 | 0 | — |
| `__vdso_flush_icache` | 0 | 0 | — |
| `__vdso_riscv_hwprobe` | 16 | 16 | `riscv_hwprobe` at 0xc30 adds 0 |
| `__vdso_getrandom` | 144 | 240 | `__arch_chacha20_blocks_nostack` at 0xe68 adds 96 |

Every bound is exact. No call is indirect. No call chain has a cycle. Each
function moves `sp` one time, with one `addi sp,sp,-N`. The JSON field
`stack.per_function` holds the instruction of each one.

## The callee-saved registers and the memory writes

The script walks the control-flow graph of each exported function. It tracks
`sp`, the callee-saved registers and the base register of every store.

Result for all 8 exported functions:

- No function leaves a callee-saved register changed at a `ret`. A function
  that uses `s0` to `s11` saves them into its own frame. It loads them back
  before each `ret`.
- `sp` has its entry value at every `ret`.
- No function writes `gp` or `tp`. No instruction in the image has `gp` or
  `tp` as its destination register.
- Every store goes to the function's own frame, or to a buffer that an
  argument points at. The frame stores stay inside `[sp-F, sp)`.
- `__vdso_rt_sigreturn` has no `ret`. It makes an `ecall` that does not
  come back. It writes no memory.

| Function | Writes a callee-saved register without restoring it | Writes only the frame and the argument buffers | Frame write range from the caller's `sp` |
| --- | --- | --- | --- |
| `__vdso_rt_sigreturn` | no | yes | none |
| `__vdso_clock_gettime` | no | yes | `[-80, 0)` |
| `__vdso_gettimeofday` | no | yes | `[-64, 0)` |
| `__vdso_clock_getres` | no | yes | `[-16, 0)` |
| `__vdso_getcpu` | no | yes | none |
| `__vdso_flush_icache` | no | yes | none |
| `__vdso_riscv_hwprobe` | no | yes | `[-16, 0)` |
| `__vdso_getrandom` | no | yes | `[-240, 0)` |

`__vdso_clock_gettime`, `__vdso_gettimeofday`, `__vdso_clock_getres`,
`__vdso_riscv_hwprobe` and `__vdso_getrandom` read the vDSO data pages below
the image. No function writes a vDSO data page. Each function can make an
`ecall`. The `ecall` writes what the syscall's specification says it writes.
The JSON field `callee_saved_and_memory_writes` holds the `ecall` sites of
each function.

This result supports the spec's decision "A vDSO call is one step with the
syscall's specification". A vDSO call changes the caller's state in two
ways only. It writes `[sp-240, sp)`, and it writes the buffers the
arguments point at.

## The JSON fields

`vdso-measurements.json` is a list. Each object holds:

- `file`, `configuration`, `size`, `pages`, `sha256`, `elf_magic`.
- `bytes_hex_chunks`: the whole image as lowercase hex, in chunks of at most
  1024 hex characters.
- `elf_header`, `program_headers`, `pt_load`, `pt_dynamic`.
- `dynamic_entries` and `dynamic`, with the symbol count and its source.
- `dynamic_symbols` and `exported_symbols`.
- `stack`, with `F_largest_frame_bytes` and the per-function evidence.
- `callee_saved_and_memory_writes`.
- `crosscheck_readelf`.
- `build`, with the commit, the toolchain, the container id and the make
  commands.
