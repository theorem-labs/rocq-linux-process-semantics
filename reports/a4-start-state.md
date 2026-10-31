# A4: LPS's start state against a booted Linux v6.18.46 riscv64 kernel

Acceptance check A4 of [OSSV-257](https://dispatch.tail12ec1c.ts.net/issues/OSSV-257).
The model is `rocq-linux-process-semantics` branch `revision/entry`
(`theories/LinuxProcessSem/StackLayout.v`, `State.v`, `Run.v`).  The harness
is `tools/placement_conformance/` of `rocq-linux-process-semantics` branch
`revision/place`, which OSSV-231 built and this check extends.

Five kernels boot the probe twice each, and the ten records are read against
the model by `tools/placement_conformance/check_start_state.py`.  All three
sub-checks pass on all ten records, with no disagreement between the model
and the kernel.  What the boots do NOT exercise is listed under "What this
does not check".

## The boots

Every boot: Linux v6.18.46, commit `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`,
riscv64, built by `riscv64-linux-gnu-gcc (Debian 14.2.0-19) 14.2.0`, booted
under `QEMU emulator version 10.0.11 (Debian 1:10.0.11+ds-0+deb13u1)` with
`-M virt -cpu rv64,sv57=off -m 2G`.  The probe binary is one file in all five:
sha256 `799ba847c935d381de8e34d4a5e9df22a1b4a36fc36168625401b21ce0fd0c0a`,
built from `probe.c` sha256
`88eb949aac9f18d10444578d5243a0a3c56bff1eea07624e78d9988d9e98a5d0` (clang
20.1.8, musl 1.2.6, `-march=rv64g -mabi=lp64d -static -no-pie -nostartfiles`).

| Boot | qemu | command line | devicetree |
| --- | --- | --- | --- |
| `defconfig-seed1` | `-seed 1` | `console=ttyS0 no5lvl rdinit=/probe pc_mode=startstate` | qemu's |
| `defconfig-seed2` | `-seed 2` | the same | qemu's |
| `defconfig-cache-seed1` | `-seed 1` | the same | qemu's, with a cache hierarchy added (`patch_dtb.py`) |
| `thp-seed1` | `-seed 1` | the same | qemu's |
| `norandmaps-seed1` | `-seed 1` | `console=ttyS0 no5lvl rdinit=/probe norandmaps pc_mode=startstate` | qemu's |

Four of the five randomize; `norandmaps-seed1` does not.  `-seed` fixes
qemu's own generator, not the kernel's: two boots with the same seed give
different draws, because the kernel's randomness does not come from the
devicetree seed alone.  The four randomizing boots therefore give four
different draws, which is what A4 asks for; the seed is recorded for
provenance, not for determinism.

Each boot runs the probe twice, as PID 1 forks and `execve`s `a` (a second
name for the probe in the initramfs):

- `fixture`: exec name `a`, argv `["a"]`, envp `[]` — the fixture of A1.
- `long`: exec name `a`, argv of 33 strings, envp of 16 strings, L = 3468.

Ten logs, under `tests/placement/` of the `revision/place` clone:
`linux-6.18.46-<boot>-fixture.log` and `linux-6.18.46-<boot>-long.log`.

## The launch facts

Read from the kernel, not from the auxiliary vector:

| Fact | Value | Source |
| --- | --- | --- |
| `CONFIG_RSEQ` | `y` | `.config`, merged into the log by `run-kernel.sh` |
| `CONFIG_TRANSPARENT_HUGEPAGE` | not set (`thp-seed1`: set) | `.config` |
| `CONFIG_COMPAT_BRK` | `y` | `.config` |
| `CONFIG_RISCV_ISA_V` | `y` | `.config` |
| `CONFIG_ARCH_MMAP_RND_BITS` | 18, `MIN` 18, `MAX` 24 | `.config` |
| `CONFIG_MSEAL_SYSTEM_MAPPINGS` | absent from this `.config` | `.config` |
| `CONFIG_LSM_MMAP_MIN_ADDR` | 4096 | `.config` |
| `vm.mmap_rnd_bits` | 18 | `/proc/sys/vm/mmap_rnd_bits` |
| the ceiling on `vm.mmap_rnd_bits` | **33** | measured: the largest value the sysctl accepts, then the launch's value written back |
| `kernel.randomize_va_space` | 1, and 0 under `norandmaps` | `/proc/sys/kernel/randomize_va_space` |
| `stack_guard_gap` | not on the command line, so 256 pages | the whole `-append` string, recorded |
| `vlenb` | `null`: AT_HWCAP is `0x112d`, no V bit, so the CSR was not read | the probe |
| devicetree cache | `/cpus/cpu@0` carries no cache property (`defconfig-cache-seed1`: it carries one) | `qemu -M virt,dumpdtb`, parsed by `merge_launch.py` |
| mmu | `sv48` | `/proc/cpuinfo` |
| `dac_mmap_min_addr` | 4096 | `/proc/sys/vm/mmap_min_addr` |
| initial break | `0x25000` | `brk(0)` |

Two of these are worth naming:

- **The `.config` line is not the ceiling.** `CONFIG_ARCH_MMAP_RND_BITS_MAX`
  is 24 in this build, but the running kernel accepts `vm.mmap_rnd_bits` = 33
  and refuses 34, because `arch/riscv/mm/init.c` `set_mmap_rnd_bits_max`
  raises the ceiling from the address-space size at boot.  The model's
  `State.mmap_rnd_bits_max Sv48 = 33` is therefore right, and a reviewer who
  reads only the `.config` would call it wrong.  There is no
  `/proc/sys/vm/mmap_rnd_bits_max` file, so the probe measures the ceiling by
  writing candidates and writing the launch's value back.
- **`randomize_va_space` is 1, not 2**, because `CONFIG_COMPAT_BRK=y` in the
  riscv defconfig.  1 still randomizes the stack top and the mmap base; it
  leaves the break unrandomized.  The model's `kb_aslr` reads "not 0", so 1
  is `kb_aslr = true`, and the records confirm that the stack top and the
  base are drawn.

## The records

`base` is the top of the `[vdso]` mapping, which is where
`__setup_additional_pages` puts the first mapping below `mmap_base`
(OSSV-231's `log_to_rocq.py` reads the base the same way).  Under
`norandmaps` it is exactly `0x7ffff8000000`, the value
`Run.mmap_base_of Sv48 kb 0` gives, which is the independent confirmation
that this reading of the base is Linux's base.

| Boot | run | `stack_end` | `sp_at_start` | mmap base | `argv[0] - sp` | auxv entries | AT_MINSIGSTKSZ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| defconfig-seed1 | fixture | 0x7fffd31f6000 | 0x7fffd31f5290 | 0x7fffbcdad000 | 3428 | 29 | 1088 |
| defconfig-seed1 | long | 0x7ffffd337000 | 0x7ffffd335990 | 0x7fff9ae94000 | 2268 | 29 | 1088 |
| defconfig-seed2 | fixture | 0x7fffdf6b2000 | 0x7fffdf6b1c10 | 0x7fff899c8000 | 996 | 29 | 1088 |
| defconfig-seed2 | long | 0x7ffff5f2c000 | 0x7ffff5f2a100 | 0x7fffa1e66000 | 4460 | 29 | 1088 |
| defconfig-cache-seed1 | fixture | 0x7fffdc244000 | 0x7fffdc243cd0 | 0x7fffa96b7000 | 804 | 29 | 1088 |
| defconfig-cache-seed1 | long | 0x7ffff5a30000 | 0x7ffff5a2e270 | 0x7fff9fff9000 | 4092 | 29 | 1088 |
| thp-seed1 | fixture | 0x7fffcfe37000 | 0x7fffcfe368e0 | 0x7fffad8ef000 | 1812 | 29 | 1088 |
| thp-seed1 | long | 0x7fffe75e3000 | 0x7fffe75e1810 | 0x7fff9102f000 | 2652 | 29 | 1088 |
| norandmaps-seed1 | fixture | 0x800000000000 | 0x7ffffffffdf0 | 0x7ffff8000000 | 516 | 29 | 1088 |
| norandmaps-seed1 | long | 0x800000000000 | 0x7fffffffeee0 | 0x7ffff8000000 | 908 | 29 | 1088 |

`mm->start_stack` (field 28 of `/proc/self/stat`) equals `sp_at_start` in all
ten records, so the sp the kernel chose is the sp the process starts with.

### 1. `Run.entry_launch_ok_va`

Holds of (`stack_end`, `sp_at_start`, base) under the recorded facts in all
ten records, with `v = Sv48` (`/proc/cpuinfo` reports `sv48`).

- `valid_stack_top_va`: every `stack_end` is page-aligned, at or below
  `0x800000000000`, and at most `0x3ffff000 + 4096` below it with
  randomization (the deepest draw seen is 47,135 pages, within the 262,144 +
  1 the rule allows), and exactly `0x800000000000` without it.
- `valid_launch_sp`: every sp is 16-aligned and inside
  `[align_down16(top - 8 - L - 4095) - C, align_down16(top - 8 - L) - C]`.
  The pads the ten records show are 4, 12, 484, 804 (as `argv[0] - sp - 512`),
  1300, 1372, 1756, 2916, 3564 bytes — the whole 0..4095 width of
  `arch_align_stack` is exercised, not one corner of it.
- `valid_launch_base`: each base is `page_round_up(T0 - gap - 4096 r)` with
  `gap = 0x408ff000` (8 MiB + 256 pages + `0x3ffff000`) and
  `r < 2^18`: r = 154,632 and r = 3,330 and so on for the randomizing boots,
  and r = 0 with `gap = 128 MiB` for `norandmaps`.

The fixture of A1 and the witness of A2 (a) appear verbatim in
`linux-6.18.46-norandmaps-seed1-fixture.log`: `ed_top = 0x800000000000`,
sp = `0x7ffffffffdf0`, base = `0x7ffff8000000`, `argv[0] - sp = 516`, and the
8 bytes at sp + 8 hold `0x7ffffffffff4`.  Those are the numbers the spec
computes by hand; a real kernel gives them.

### 2. The block and the auxiliary vector

`StackLayout.build_stack_bytes`, applied to the recorded facts and to the
recorded sixteen AT_RANDOM bytes, equals the recorded bytes from
`sp_at_start` to `stack_end` BYTE FOR BYTE in all ten records, 528 to 5,904
bytes each.  The model's length is `stack_end - sp` in every record, so the
block ends exactly at the stack VMA's `vm_end`, with the eight-byte slot
`create_init_stack_vma` skips.

The recorded auxiliary vector equals `StackLayout.auxv_entries` entry for
entry, in order, 29 entries in every record (`CONFIG_RSEQ=y`).  The kernel's
order, from `/proc/self/auxv`, is exactly the model's: AT_SYSINFO_EHDR, the
eight cache words, AT_MINSIGSTKSZ, AT_HWCAP, AT_PAGESZ, AT_CLKTCK, AT_PHDR,
AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS, AT_ENTRY, AT_UID, AT_EUID, AT_GID,
AT_EGID, AT_SECURE, AT_RANDOM, AT_EXECFN, AT_RSEQ_FEATURE_SIZE,
AT_RSEQ_ALIGN, AT_NULL.  The kernel emits no entry the model does not: no
AT_PLATFORM, no AT_HWCAP2, no AT_EXECFD.  AT_PAGESZ is 4096, AT_CLKTCK is
100, AT_BASE, AT_FLAGS and AT_SECURE are 0, AT_PHENT is 56, as the model
says.

- **AT_MINSIGSTKSZ**: `State.min_sigframe_size` gives 1088 and the kernel
  gives 1088 in all ten records.  `rt_sigframe` is therefore 1088 bytes on
  this kernel, and the model's literal is right.
- **The eight cache words**: with qemu's own devicetree the CPU node carries
  no cache property, both the model and the kernel give eight zeros, and the
  comparison says nothing about the formulas.  `defconfig-cache-seed1` closes
  that: its devicetree gives `cpu@0` i-cache 32 KiB/64 sets/64-byte line,
  d-cache 32 KiB/128 sets/32-byte line, and an L2 of 512 KiB/1024
  sets/64-byte line.  The kernel then publishes
  `0x8000, 0x80040, 0x8000, 0x80020, 0x80000, 0x80040, 0, 0`, and
  `State.cache_size_word` and `State.cache_geometry_word` over that
  devicetree give the same eight words.  So the devicetree branch of
  `State.cache_ways` (ways = size/sets/line) and the `ways << 16 | line`
  packing are read against a kernel, not only against the source.

### 3. The vDSO image and the vvar mapping

- The bytes at the AT_SYSINFO_EHDR value start `7f 45 4c 46` and, for their
  first 5,704 bytes, are byte for byte the `vdso.so` the kernel build
  carries (`$PC_WORK/kernels/<cfg>/vdso.so`, sha256
  `0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36`); the
  mapped two pages (8,192 bytes, sha256
  `732e4b22e3a3912a221d57b3ed4c22bbaccf372998fa05a1f72a138651d369dd`) are
  that file zero-padded to a page boundary.  Both the defconfig and the thp
  build produce the same image.
- The `[vdso]` mapping is 2 pages in all ten records, and it ends at the mmap
  base, so AT_SYSINFO_EHDR = base − 2 pages, which is
  `Run.vdso_text_base` with `vdso_text_pages = 2`.  The model's encoding
  (`1 + kb_vdso mod 16`) can name 2.
- The `[vvar]` mapping starts exactly four pages below AT_SYSINFO_EHDR in all
  ten records, and there is no second vvar mapping in the maps text.  The
  model's `State.vdso_vvar_pages = 4` is right for this build.

## Disagreements between the model and the kernel

**None.**  The checker reports no disagreement on any of the ten records: the
block matches byte for byte, the auxiliary vector matches entry for entry,
AT_MINSIGSTKSZ and the eight cache words match, and all three rules of
`entry_launch_ok_va` hold.

Two places where a reader might expect one, and why there is none:

- `CONFIG_ARCH_MMAP_RND_BITS_MAX=24` against the model's 33: the running
  kernel's ceiling is 33 (measured), so the model agrees with the kernel and
  disagrees only with the Kconfig default, which `set_mmap_rnd_bits_max`
  overrides.
- `randomize_va_space = 1` against a reading that randomization means 2: the
  model's `kb_aslr` is "not 0", and the records with the value 1 draw a stack
  top and an mmap base, so `kb_aslr = true` is the right reading.

## What this does not check

- **The vDSO image is not in the model.** `State.vdso_images` does not exist
  on `revision/entry`; the model holds only a text size in pages
  (`State.vdso_text_pages`).  So sub-check 3 compares the recorded image with
  the kernel build's own `vdso.so`, and checks the size, the placement and
  the vvar distance against the model.  The claim "the image LPS holds is the
  image the kernel maps" cannot be checked until the table of measured images
  that the spec's Design "The vDSO pages" asks for exists.
- **No vector unit.** `-cpu rv64` has no V, so AT_HWCAP is `0x112d`
  (`hwcap_rv64gc`), `vlenb` was never read, and the vector branch of
  `State.min_sigframe_size` (`8 + 48 + 32 vlenb`) is not exercised.  Only the
  1088 branch is.
- **One L3-less cache view.** `defconfig-cache-seed1` gives L1I, L1D and L2;
  the L3 words stay zero, and the ACPI branch of `State.cache_ways` is not
  exercised, because this machine boots from a devicetree.
- **Sv48 only, 8 MiB stack limit only, `ET_EXEC` static binary only**, as
  SCOPE.md assumes.  `no5lvl` pins Sv48; `/proc/cpuinfo` confirms it.
- **The mmap base is read off the `[vdso]` mapping**, not from a kernel
  interface that names `mm->mmap_base`.  Under `norandmaps` the value is
  exactly the model's `mmap_base_of ... 0`, which is the evidence that the
  reading is right; for the randomizing boots the check is that some r in
  range gives the value.
- **`stack_guard_gap` is the default in every boot.** No boot passes
  `stack_guard_gap=` on the command line, so the model's `kb_guard` encoding
  is exercised at 256 pages only.  The whole command line is in each log, so
  the value is recorded rather than assumed.

## Verdicts, one line per A4 sub-check

- A4 sub-check 1, `Run.entry_launch_ok_va` of the recorded stack end, stack
  pointer and mmap base under the recorded launch facts: **passed**, 10 of 10
  records.
- A4 sub-check 2, LPS's block equal to the recorded bytes apart from the
  sixteen AT_RANDOM bytes, and the recorded auxv equal to
  `StackLayout.auxv_entries` entry for entry, with AT_MINSIGSTKSZ against
  `State.min_sigframe_size` and the eight cache words against
  `State.cache_size_word` and `State.cache_geometry_word`: **passed**, 10 of
  10 records.
- A4 sub-check 3, the recorded vDSO image the one the kernel build carries,
  and the vvar mapping four pages below AT_SYSINFO_EHDR: **passed**, 10 of 10
  records, with the limit above (the model carries no image bytes).

## How to reproduce

```bash
cd <revision/place clone>
export PC_WORK=$HOME/pc
tools/placement_conformance/run-kernel.sh image
tools/placement_conformance/run-kernel.sh source
tools/placement_conformance/run-kernel.sh probe
tools/placement_conformance/run-kernel.sh kernel defconfig
tools/placement_conformance/run-kernel.sh kernel thp
tools/placement_conformance/run-kernel.sh startstate defconfig 1
tools/placement_conformance/run-kernel.sh startstate defconfig 2
tools/placement_conformance/run-kernel.sh startstate defconfig 1 cache
tools/placement_conformance/run-kernel.sh startstate thp 1
tools/placement_conformance/run-kernel.sh startstate norandmaps 1
cp $PC_WORK/out/linux-6.18.46-*-{fixture,long}.log tests/placement/
python3 tools/placement_conformance/check_start_state.py \
    tests/placement/linux-6.18.46-defconfig-*.log \
    tests/placement/linux-6.18.46-norandmaps-*.log \
    --vdso $PC_WORK/kernels/defconfig/vdso.so
python3 tools/placement_conformance/check_start_state.py \
    tests/placement/linux-6.18.46-thp-*.log --vdso $PC_WORK/kernels/thp/vdso.so
```

The checker exits 0 when every sub-check of every log passes.  The model's
transcription that A6 has to read is the block of `check_start_state.py`
between the markers `MODEL TRANSCRIPTION BEGINS` and
`MODEL TRANSCRIPTION ENDS`: one Python function per Rocq definition, each
naming its definition.
