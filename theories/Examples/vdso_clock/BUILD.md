# vdso_clock: how the binary was built

The program `vdso_clock.c` reads the monotonic clock one time. musl gets
the time through the vDSO. The program writes the 8 bytes of `tv_sec` to
file descriptor 1. Then it exits with code 0.

## The toolchain

The binary comes from the OSS Verify pipeline's own toolchain image:

    us-central1-docker.pkg.dev/autoformalization/ossv/asis-toolchain:f3560954-oft
    manifest digest sha256:9bd7cba4916fef18d5813dbd2cfadc944ee538d688ea6c1fdbb0123911fd4fc9

The image holds clang 20.1.8, lld 20.1.8 and a musl sysroot at
`/opt/musl-sysroot`. It holds the musl source at `/musl-src`.

Why this image is the pipeline's toolchain:

1. `docs/building.md:4` of theorem-labs/oss-verify-proofs-internal says
   that every binary is "a static riscv64 Linux program, compiled for
   RV64G (`-march=rv64g -mabi=lp64d`) by clang 20.1.8 against musl, and
   linked with lld".
2. The toolchain is built by `toolchain/Dockerfile` of
   theorem-labs/static-asan. That file pins musl to `f21a9653` and
   llvm-project to `87f0227cb` (`ARG MUSL_BASE`, `ARG LLVM_BASE`, lines
   57-59 and 298-299 of the file in the clone
   `/mnt/nvme/sami/oss-verifier/agents/repro/static-asan`, commit
   `f48ae5b1`).
3. The tag `f3560954-oft` names asan-static commit `f3560954`.
   `notes/archana-TODO.md:218` of `/home/sami/src/oss-verifier` says that
   static-asan `f48ae5b1` is a snapshot of asan-static `f3560954`, and
   that `f3560954` built the example binaries.
   `notes/R4-rebuild-pipeline.md:128-129` says the same.

Measured proof that the image holds musl 1.2.6 at `f21a9653`:

- `/musl-src/VERSION` contains `1.2.6`.
- A fresh clone of musl was made on the build VM. The tree of
  `f21a96538f78fa8e2040831b4209b35f2fb581da` was extracted. The two musl
  patches of static-asan (`patches/musl/0001-export-pthread-struct-size.patch`
  and `patches/musl/0002-init-tls-check-mmap.patch`) were applied.
  `diff -r -q` against `/musl-src` reported no difference.

The build clang is `/opt/asan-static/musl.cfg`, the plain static musl
configuration with no sanitizer. The configuration file contains:

    --target=riscv64-unknown-linux-musl
    --sysroot=/opt/musl-sysroot
    -march=rv64g -mabi=lp64d -ffunction-sections -fdata-sections
    -resource-dir=/opt/asan-rt/lib/clang/20
    --rtlib=compiler-rt
    --unwindlib=libunwind
    -fuse-ld=lld
    -static
    -Wl,--gc-sections

## The compile command

Run this command in the directory that holds `vdso_clock.c`:

    docker run --rm -v $PWD:/w -w /w \
      us-central1-docker.pkg.dev/autoformalization/ossv/asis-toolchain:f3560954-oft \
      clang --config=/opt/asan-static/musl.cfg \
        -Os -no-pie -fno-stack-protector -std=gnu17 \
        vdso_clock.c -o vdso_clock

clang prints one warning: `-no-pie` is unused, because `musl.cfg` already
links static and lld makes a non-PIE executable. The ELF type is `EXEC`.

The program uses musl's usual start-up code (`crt1.o` and
`__libc_start_main`). Do not use `-nostartfiles`. musl's vDSO lookup reads
the auxv that `__init_libc` saved. A program with its own `_start` must do
that work itself.

## The binary

| Fact | Value |
| --- | --- |
| sha256 | `f38732982c92f1ccfb5344bfcbac1f3706aba8489081220d1bfa8b24d61cca11` |
| File size | 13640 bytes |
| Entry point (`e_entry`) | `0x11370` (`_start`) |
| `e_phoff` | 64 |
| `e_phentsize` | 56 |
| `e_phnum` | 10 |
| `.text` size | 5087 bytes |
| `.data` size | 160 bytes |
| `.bss` size | 2960 bytes |
| Machine | RISC-V, ELF64, little endian |
| `e_flags` | `0x4`, double-float ABI, no compressed instructions |
| Instruction words in `.text` | 1209 (counted by `tools/gen_fd_lemmas.py`) |

The four `PT_LOAD` segments:

| Offset | Virtual address | FileSiz | MemSiz | Permissions |
| --- | --- | --- | --- | --- |
| `0x000000` | `0x10000` | `0x370` | `0x370` | `R` |
| `0x000370` | `0x11370` | `0x12e4` | `0x12e4` | `R E` |
| `0x001658` | `0x13658` | `0x088` | `0x9a8` | `RW` |
| `0x0016e0` | `0x146e0` | `0x018` | `0x288` | `RW` |

The other program headers are `PHDR`, `GNU_RELRO`, `GNU_EH_FRAME`,
`GNU_STACK`, `NOTE` and `RISCV_ATTRIBUTES`.

`tools/elf_snapshot.py` rounds each `PT_LOAD` to whole pages. The snapshot
`VdsoClockMemImage.v` holds four segments:

| Base | Size | Permissions |
| --- | --- | --- |
| `0x10000` | `0x1000` | `r--` |
| `0x11000` | `0x2000` | `r-x` |
| `0x13000` | `0x1000` | `rw-` |
| `0x14000` | `0x1000` | `rw-` |

`VdsoClockMemImage_init_pc` is `0x11370`. `VdsoClockMemImage_phdrs` is
`ph_addr := 0x10040`, `ph_ent := 56`, `ph_num := 10`. Those three values
are what the kernel publishes as `AT_PHDR`, `AT_PHENT` and `AT_PHNUM`.
`python3 tools/elf_snapshot.py --print-phdrs vdso_clock` prints the same
three values.

## Where the program reaches the vDSO

These addresses come from `llvm-objdump -d vdso_clock`.

| Symbol | Address |
| --- | --- |
| `_start` | `0x11370` |
| `main` | `0x114bc` |
| `__init_libc` | `0x114f0` |
| `__libc_start_main` | `0x11768` |
| `clock_gettime` (`__clock_gettime`) | `0x120b4` |
| `cgt_init` | `0x1216c` |
| `__vdsosym` | `0x12238` |

The path of the one `clock_gettime` call, instruction by instruction:

1. `0x114cc`: `main` calls `clock_gettime` with `a0 = 1`
   (`CLOCK_MONOTONIC`) and `a1 = &ts`.
2. `0x120c8`-`0x120cc`: `clock_gettime` loads the static variable
   `vdso_func`. Its initial value is the address of `cgt_init`, so the
   value is not zero.
3. `0x120e0`: `jalr a2` calls that value. On the first call it calls
   `cgt_init`. The link register `ra` becomes `0x120e4`.
4. `0x12194`: `cgt_init` calls `__vdsosym` with `jal`.
5. `0x121d8`: `cgt_init` ends with `jr t1`, a TAIL JUMP to the address
   `__vdsosym` returned. This is `jalr x0, 0(t1)`: it does not write
   `ra`. `ra` still holds `0x120e4` from step 3, because `0x121c8`
   reloaded it from the stack frame.
6. The vDSO entry therefore returns to `0x120e4`, inside
   `clock_gettime`. There is NO `jalr` that links the vDSO entry.
   `0x121d8` is the instruction that enters the vDSO, and `0x120e4` is
   the instruction the program runs after the vDSO entry returns.
7. `0x120e4`: `beqz a0, 0x12124` tests the result. A result of 0 goes to
   the return path of `clock_gettime` at `0x12124`.

`0x120f8`-`0x12104` is the fall-back path. It makes the
`clock_gettime` system call (`a7 = 0x71`, that is 113) when the vDSO
lookup failed or when the vDSO entry returned an error.

The vDSO path is live in this binary. It is not compiled out:

- `arch/riscv64/syscall_arch.h` of musl `f21a9653` defines
  `VDSO_USEFUL`, `VDSO_CGT_SYM` as `"__vdso_clock_gettime"` and
  `VDSO_CGT_VER` as `"LINUX_4.15"` (lines 73-75). So
  `src/time/clock_gettime.c` compiles its `#ifdef VDSO_CGT_SYM` blocks.
- `__vdsosym` is present at `0x12238` and `cgt_init` calls it at
  `0x12194`.
- There is no `CLOCK_MONOTONIC` fast path in musl that bypasses the
  vDSO. The only two ways out of `clock_gettime` are the vDSO entry and
  the system call.

`libc.auxv` is filled before the call:

- `__init_libc` (`0x114f0`) gets `envp` in `a0`. At `0x11528`-`0x11530`
  it walks `envp` to its null entry. At `0x1153c` it stores the address
  after that null into `libc.auxv` with `sd s1, 0x8(s2)`.
  `/musl-src/src/env/__libc_start_main.c` holds the same code as
  `libc.auxv = auxv = (void *)(envp+i+1);`.
- `__vdsosym` (`0x12270`-`0x12284`) loads `libc.auxv` and scans the pairs
  for the key `0x21`, that is 33, `AT_SYSINFO_EHDR`.

## The auxv entries musl reads

These come from the musl source in the toolchain image, at the commit
checked above.

`__init_libc` (`src/env/__libc_start_main.c`) copies every auxv pair
whose key is below 38 into a local array. It then reads:

| Key | Number | Use |
| --- | --- | --- |
| `AT_HWCAP` | 16 | sets `__hwcap` |
| `AT_SYSINFO` | 32 | sets `__sysinfo` when not zero |
| `AT_PAGESZ` | 6 | sets `libc.page_size` |
| `AT_EXECFN` | 31 | the program name, when `argv[0]` is absent |
| `AT_RANDOM` | 25 | given to `__init_ssp` |
| `AT_UID` | 11 | compared with `AT_EUID` |
| `AT_EUID` | 12 | compared with `AT_UID` |
| `AT_GID` | 13 | compared with `AT_EGID` |
| `AT_EGID` | 14 | compared with `AT_GID` |
| `AT_SECURE` | 23 | selects the secure start-up path |

`__init_tls` (`src/env/__init_tls.c`), called by `__init_libc`, reads
`AT_PHDR` (3), `AT_PHNUM` (5) and `AT_PHENT` (4) from the same array. It
walks the program headers to find `PT_TLS`.

`__vdsosym` (`src/internal/vdso.c`) does NOT use that array. It walks the
raw auxv through `libc.auxv` and looks for `AT_SYSINFO_EHDR` (33). The
value is the address of the vDSO ELF header. `__vdsosym` then reads, from
the vDSO image only:

1. the ELF header fields `e_phoff`, `e_phnum` and `e_phentsize`;
2. every program header, to find `PT_LOAD` (for the load bias) and
   `PT_DYNAMIC`;
3. the dynamic entries `DT_STRTAB`, `DT_SYMTAB`, `DT_HASH`,
   `DT_GNU_HASH`, `DT_VERSYM` and `DT_VERDEF`;
4. the symbol table, the string table and the version records, to find
   `__vdso_clock_gettime` with version `LINUX_4.15`.

A zero `AT_SYSINFO_EHDR` value, or no `AT_SYSINFO_EHDR` entry, makes
`__vdsosym` return 0. Then `cgt_init` returns `-ENOSYS` and
`clock_gettime` makes the system call.

## The QEMU run

The binary ran under QEMU user mode on the build VM:

    qemu-riscv64 version 10.0.13 (Debian 1:10.0.13+ds-0+deb13u1)
    qemu-riscv64 ./vdso_clock > out.bin

It wrote 8 bytes: `6a 09 00 00 00 00 00 00`. That is 2410 seconds, the
monotonic clock of the build VM. The exit code was 0.

A second run counted the instructions:

    qemu-riscv64 -one-insn-per-tb -d exec -D trace.log ./vdso_clock

The log holds 1705 lines, so the run executed 1705 instructions.

What this run does NOT show. QEMU user mode maps its OWN vDSO. It builds
that image itself in `load_elf_vdso` (`linux-user/elfload.c`), and the
image is not Linux's. So the 8 bytes show that the program works. They
say nothing about which entry Linux's vDSO image would give, nor about
the instructions inside that entry. The instruction count is the count
for QEMU's vDSO, not for Linux's.

## The files of this example

| File | Contents |
| --- | --- |
| `vdso_clock.c` | the program |
| `vdso_clock` | the built binary |
| `VdsoClockMemImage.v` | the snapshot, made by `tools/elf_snapshot.py` |
| `VdsoClockMemImage_seg_00{0,1,2,3}.hex` | the segment bytes |
| `dune` | the rule that makes `vdso_clock_code.v` |
| `BUILD.md` | this file |

Remake the snapshot with this command, from the repository root:

    python3 tools/elf_snapshot.py \
      theories/Examples/vdso_clock/vdso_clock \
      theories/Examples/vdso_clock/VdsoClockMemImage.v \
      --prefix VdsoClockMemImage --module-name Image \
      --namespace LinuxProcessSemantics.Examples.vdso_clock

The module `Image` makes the three definitions available as
`VdsoClockMemImage.Image.loaded_segments`,
`VdsoClockMemImage.Image.init_pc` and `VdsoClockMemImage.Image.phdrs`.
`rwx_flag_ns` gives no `mkImage` record, so this example gives none
either.

This example has one binary, so there is no `Checker.v` rule.
`tools/gen_checker.py` renders the equivalence checker, which needs a
source image and a target image. `python3 tools/gen_checker.py --check`
reads `theories/Examples/dune` alone, so this directory does not change
its result. Note that `gen_checker.py --check` fails if a `Proof.v`
appears here and `theories/Examples/dune` has no `Checker.v` rule for
`vdso_clock`.

## Checks that passed

Both commands ran in the release checker image
`us-central1-docker.pkg.dev/autoformalization/ossv/oss-fuzz-theorems-checker@sha256:cc9ae43a9f4b…`
on the build VM, over a copy of this tree that holds the files above:

    python3 tools/gen_checker.py --check      # exit 0
    python3 tools/test_elf_snapshot.py        # exit 0, 16 assertion groups
