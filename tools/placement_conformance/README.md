# Placement conformance: replay a real kernel through the checker

LPS says where Linux puts a new mapping. This directory holds the tool that
reads that answer against a real Linux kernel, and not against a reading of
the kernel's source.

A probe program asks a kernel to place mappings and writes what the kernel
answered. A generator turns the log into a Rocq file. The Rocq file walks
every call of the log through the LPS checker and demands `CheckOk` at each
step. The file compiles only if LPS puts each mapping where the kernel put
it.

## The files

| File | What it is |
| --- | --- |
| `probe.c` | The program that makes the calls and writes the log. |
| `run-kernel.sh` | Builds the kernel, the probe and the initramfs; boots the kernel; writes the log. |
| `log_to_rocq.py` | Makes a Rocq replay from a placement log. |
| `start_state_to_rocq.py` | Makes the Rocq A4 check from a start-state log (acceptance item A4 of the start-state specification). |
| `merge_launch.py` | Puts the `.config` lines, the devicetree cache properties and the command line into the launch object. |
| `patch_dtb.py` | Writes a devicetree in which the boot CPU has caches, which qemu's has not. |
| `check_start_state.py` | EVIDENCE, not the check: reads a start-state log against a Python transcription of the entry model. |
| `../../tests/placement/*.log` | The logs this tree keeps: four placement logs and ten start-state logs. |
| `../../tests/dune` | The rules that make `PlacementReplay*.v` from the placement logs, and `StartState*.v` from the start-state logs. |

## The replay is compiled by the ordinary build

The generated files are part of the test theory. `tests/dune` declares

```
(rocq.theory
 (name LinuxProcessSemantics.Tests)
 (theories Stdlib stdpp ReadFile LinuxProcessSemantics LinuxProcessSemantics.Common))
```

with no `modules` field, so `:standard` takes every module the rules above
generate: `PlacementReplayDefconfig`, `PlacementReplayThp`,
`PlacementReplayNorandmaps`, `PlacementReplayQemuUser` and
`PlacementReplayOffByOnePage`. There is no line keeping them out of the
theory, and there is nothing to turn on.

So `dune build` — the first thing CI runs — compiles the five files, and a
placement that LPS does not reproduce breaks the build. The last two are the
negatives: they demand a REJECT, so a model that started accepting what the
kernel did not do breaks the build just as loudly.

## How to make a log

Use a machine with docker, git and about 20 GB of disk. The script installs
nothing on the host: every compile and every boot runs in a container.

```bash
export PC_WORK=$HOME/pc                   # the work directory
tools/placement_conformance/run-kernel.sh image        # the build container
tools/placement_conformance/run-kernel.sh source       # Linux v6.18.46
tools/placement_conformance/run-kernel.sh probe        # the probe and the initramfs
tools/placement_conformance/run-kernel.sh kernel defconfig
tools/placement_conformance/run-kernel.sh kernel thp
tools/placement_conformance/run-kernel.sh boot defconfig
tools/placement_conformance/run-kernel.sh boot thp
tools/placement_conformance/run-kernel.sh boot norandmaps
tools/placement_conformance/run-kernel.sh qemu-user
```

Each log is written to `$PC_WORK/out/<name>.log`. Copy it into
`tests/placement/`.

Every input is pinned:

- the kernel is commit `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`, the tag
  `v6.18.46`, and the script stops if the clone is a different commit;
- the build container is a Debian image by digest, and qemu 10.0.11 by the
  SHA-256 of its four packages. 10.0.11 is the version in the collection's
  runner image, and the `qemu-user` package is the same file;
- the probe is built in the collection's builder image, by digest.

### The three kernel configurations

| Name | What it is |
| --- | --- |
| `defconfig` | `make ARCH=riscv defconfig`, then `CONFIG_LSM_MMAP_MIN_ADDR=4096`. |
| `thp` | The same, plus `CONFIG_TRANSPARENT_HUGEPAGE`. |
| `norandmaps` | The `defconfig` kernel, booted with `norandmaps`. |

`CONFIG_LSM_MMAP_MIN_ADDR` is lowered to 4096 because the riscv defconfig
turns SELinux on, whose default is 65536. `mmap_min_addr` is the larger of
that value and `dac_mmap_min_addr` (Linux v6.18.46, `security/min_addr.c`,
`update_mmap_min_addr`). SCOPE.md assumes 4096. The script runs `make ARCH=riscv
olddefconfig` after each `scripts/config` call, so the values hold.

`norandmaps` turns the address-space randomization off. Linux's mmap base is
then `STACK_TOP - MIN_GAP`, which is 2^47 - 128 MiB = `0x7ffff8000000` (Linux
v6.18.46, `mm/util.c`, `mmap_base`).

## The probe

`probe.c` is a static, non-PIE rv64g program, built against musl 1.2.6. It
makes every call with a raw `ecall`, so no libc wrapper can add a flag, round
a length or retry. It allocates nothing: every buffer is static.

On a kernel it runs as init (`rdinit=/probe`) in an initramfs that holds the
probe, `/proc` and `/dev/console`. It mounts `/proc`, reads its own maps,
makes its calls and powers the machine off.

The calls, in order:

1. 64 one-page `PROT_NONE` grants. They pack down from the vDSO pair.
2. A 2 MiB and an 8 MiB grant. Both lengths are PMD multiples, so a THP
   kernel aligns them.
3. `munmap` of a middle page of the packed block, and of 4 MiB.
4. A one-page grant, which must land in the 4 KiB hole.
5. Six hints: 1, 0x1001, 0x8000, 0x80000000, an occupied address, and
   2^64-1.
6. `MAP_FIXED_NOREPLACE` over the first page of the vvar mapping.
7. Three `mremap` grows: of the mapping below the vDSO pair, of one with a
   free page above it, and of one with a neighbour above it.
8. Two `brk` grows: one page, and 1 MiB.

### The log

The first line is the launch: the whole of `/proc/self/maps`, the initial
stack pointer (field 28 of `/proc/self/stat`), the initial break, the mmu, and
`/proc/sys/vm/mmap_min_addr`. That last value is `dac_mmap_min_addr` only, not
the effective minimum (Linux v6.18.46, `security/min_addr.c`,
`mmap_min_addr_handler`). Read the effective minimum off the 0x8000 hint: a
grant at 0x8000 means 4096, and a grant at 0x10000 means 65536.

Every other line is one call: `{"sysno":…,"args":[…],"ret":…}`. Each number is
the 64-bit register value as a signed decimal, so a hint of 2^64-1 reads -1
and an error reads -17. Lines that start with `#` are the provenance header
that `run-kernel.sh` writes; the generator ignores them.

## What the four logs show

Two of these are the only measured evidence in this tree for two things the
model asserts. Each is given with the line of the log that shows it.

### The effective `mmap_min_addr` is 4096

The model assumes `mmap_min_addr` is 4096 (SCOPE.md). A hint below that value
is raised; a hint at or above it is granted where it asks. The probe asks for
0x8000, which is 32768. Line 83 of `tests/placement/linux-6.18.46-defconfig.log`,
and the same line of the other two kernel logs, reads:

```
{"sysno":222,"args":[32768,4096,3,34,-1,0],"ret":32768}
```

The hint is granted at 0x8000. With the SELinux default of 65536 the grant
would be at 0x10000 instead (Linux v6.18.46, `security/min_addr.c`,
`update_mmap_min_addr`). `/proc/sys/vm/mmap_min_addr` cannot show this: it
reports `dac_mmap_min_addr` only.

### The vDSO pair is the run's FIRST search

The model puts the vvar and the text at the top of the search window, below
the mmap base, because `__setup_additional_pages` asks for the pair before
anything else is mapped below the base. Under `norandmaps` Linux's base is a
known constant, `STACK_TOP - MIN_GAP` = 2^47 - 128 MiB = `0x7ffff8000000`
(Linux v6.18.46, `mm/util.c`, `mmap_base`). The maps text in the first line
of `tests/placement/linux-6.18.46-norandmaps.log` reads:

```
7ffff7ffa000-7ffff7ffe000 r--p 00000000 00:00 0    [vvar]
7ffff7ffe000-7ffff8000000 r-xp 00000000 00:00 0    [vdso]
```

The pair ends exactly at the base, so nothing was placed below the base
before it. `log_to_rocq.py --expect-base 0x7ffff8000000` passes on this log
and stops with status 2 on either randomized log.

### The rest

All three kernel runs report `mmu: sv48`. Every run has a vvar mapping of 4
pages and a vDSO text of 2 pages, so V = 6 pages. The vDSO file is the same
bytes in all three builds.

- `linux-6.18.46-defconfig.log` — the first grant lands one page below the
  vvar mapping (vvar at `0x7fffad3a2000`, grant at `0x7fffad3a1000`), and the
  next 63 pack down from it with no gap.
- `linux-6.18.46-thp.log` — the same, but the 2 MiB and 8 MiB grants are 2
  MiB aligned, and so is the 2 MiB grant that carries the hint 1:
  `{"sysno":222,"args":[1,2097152,3,34,-1,0],"ret":140735724650496}`, which
  is `0x7fff96e00000`. A hint of 1 rounds down to 0, so it is no hint at all,
  and the request reaches the THP path (Linux v6.18.46, `mm/mmap.c`,
  `round_hint_to_min` and `__get_unmapped_area`). On the `defconfig` kernel
  the same call answers `0x7fffacf62000`, which is not 2 MiB aligned.
- `qemu-user-10.0.11.log` — the same probe under `qemu-riscv64`. QEMU places
  the mappings where its own allocator puts them, and maps no vvar at all.
  This log is the evidence for SCOPE.md: qemu-user placement is not Linux's.

Three runs of `defconfig` and three of `thp` were made, to see three
randomization draws of each. The tree keeps one log of each.

## The generator

```bash
python3 tools/placement_conformance/log_to_rocq.py LOG --out F.v --kb-thp {0,1} \
    [--expect-base ADDR] [--expect {ok,reject}] [--perturb K --perturb-pages N]
```

- `--kb-thp` says whether the kernel had `CONFIG_TRANSPARENT_HUGEPAGE`. No
  line of a log reports it, so the caller states it.
- `--expect-base` fails unless the mmap base the log shows is that address.
- `--expect reject` writes `replay … = false`, which is what the qemu-user log
  needs.
- `--perturb K --perturb-pages N` moves the return value of call `K` by `N`
  pages. A replay of a moved log must fail.

The launch state comes from the first line of the log:

- the reserved ledger is every mapping of the maps text except the stack, the
  heap and the vDSO pair. The pair is not in the list, because
  `State.init_model` appends it from the kernel build;
- the mmap base is the top of the vDSO pair. `__setup_additional_pages` asks
  for the whole pair before anything is mapped below the base (Linux
  v6.18.46, `fs/binfmt_elf.c`, `ARCH_SETUP_ADDITIONAL_PAGES`, and
  `arch/riscv/kernel/vdso.c`);
- the vDSO text size is the size of the `[vdso]` mapping;
- the stack pointer and the break are the two values the first line reports.

The effects are what Linux did, in the model's vocabulary: a `PROT_NONE` grant
unmaps its range and a readable or writable grant zero-fills it; `munmap`
unmaps; an `mremap` grow in place zero-fills the new tail; a move zero-fills
the new tail, unmaps the old range and copies the old bytes; a `brk` grow
zero-fills the pages it adds.

## Why no PROT_READ-only mapping

The probe asks for `PROT_NONE` or for `PROT_READ|PROT_WRITE`, never for
`PROT_READ` alone. The model covers those two shapes only:
`Sys/Mm/Mmap.v`'s `mmap_modeled_b` takes `PROT_READ + PROT_WRITE` and
`mmap_noaccess_b` takes `PROT_NONE`; every other protection answers
`unmodeled`, which is the fail-closed answer, because the machine model has
no mutable page permissions. That limit is older than this harness and it is
deliberate.

One call was changed for it: `MAP_FIXED_NOREPLACE` over the first page of the
vvar mapping asked with `PROT_READ` at first, and the checker answered
`CheckUnmodeled` on all three kernel logs. Linux answers `-EEXIST` whatever
the protection, so the call now asks with `PROT_READ|PROT_WRITE` and reads
the same kernel behaviour. Do not change it back: a read-only anonymous
mapping is a new modeled shape with its own fault behaviour, and it is not a
change to make behind a conformance harness.

## When a replay fails, find the one step

A failed replay says only `Unable to unify "true" with "false"`. Walk the
trace instead of reading 88 steps. Copy the generated file out of
`_build/default/tests/`, cut it at its last lemma, and add:

```coq
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
Fixpoint walk (m : Model) (steps : list (SyscallInput * SyscallEffect))
    (k : nat) : nat * Model :=
  match steps with
  | [] => (k, m)
  | (i, e) :: rest =>
      match check_syscall i e m with
      | CheckOk m2 _ => walk m2 rest (S k)
      | _ => (k, m)
      end
  end.
Definition tag (r : check_result) : nat :=
  match r with CheckOk _ _ => 0 | CheckReject => 1 | CheckUnmodeled => 2 end.
Definition bad := walk replay_init replay_steps 0.
Eval vm_compute in (fst bad,
  match nth_error replay_steps (fst bad) with
  | Some (i, e) => (bv_unsigned (in_sysno i), map bv_unsigned (in_args i),
                    bv_unsigned (eff_ret e))
  | None => (0%Z, nil, 0%Z) end,
  match nth_error replay_steps (fst bad) with
  | Some (i, e) => tag (check_syscall i e (snd bad)) | None => 9%nat end).
Definition steps2 :=
  firstn (fst bad) replay_steps ++ skipn (S (fst bad)) replay_steps.
Eval vm_compute in (fst (walk replay_init steps2 0), length steps2).
```

Compile it in the build tree:

```bash
cd _build/default && <the checker image> rocq compile -q -R theories LinuxProcessSemantics diag.v
```

The first value is the index of the first step the checker does not accept,
with the call and the kernel's answer, and the verdict (0 `CheckOk`,
1 `CheckReject`, 2 `CheckUnmodeled`). The last pair walks the trace with that
one step removed: when the two numbers are equal, every other step passed and
the disagreement is that step alone. A `CheckReject` with an address is a
placement disagreement and a finding; a `CheckUnmodeled` is the model
declining to answer, which is a scope question, not a wrong answer.

## What this harness does not cover

- The probe runs with one argument and no environment, so its entry block is
  far below 1 MiB. The residual R-a of the plan (a base above `alloc_top`)
  cannot occur in these logs.
- The probe's image is ET_EXEC. A static PIE is mapped below the base before
  the vDSO, so its first search is not the vDSO pair's.
- The replay reads placement. It does not read the entry stack, the auxiliary
  vector or any file-backed mapping.

## The start state (acceptance item A4 of the start-state specification)

The same probe also records the start state Linux gave it: the entry block,
the auxiliary vector, the stack end, the vvar start and the vDSO bytes. That
is a different call sequence, so it has its own mode and its own logs; the
placement logs above are unchanged by it.

```bash
tools/placement_conformance/run-kernel.sh startstate defconfig 1
tools/placement_conformance/run-kernel.sh startstate defconfig 2
tools/placement_conformance/run-kernel.sh startstate defconfig 1 cache
tools/placement_conformance/run-kernel.sh startstate thp 1
tools/placement_conformance/run-kernel.sh startstate norandmaps 1
```

Each boot puts `pc_mode=startstate` on the command line. The kernel hands an
unknown `key=value` to init in its environment (Linux v6.18.46, commit
1f99e9ab748f, `init/main.c`, `unknown_bootoption`), so the probe reads it
there. In that mode the probe makes no placement call. As init it forks twice
and execs `a`, a second name for the probe in the initramfs: once with argv
`["a"]` and an empty environment, once with a long argv and a long envp. Each
child writes ONE launch line and exits; the parent powers the machine off.
`run-kernel.sh` writes one log per run, `linux-6.18.46-<tag>-fixture.log` and
`linux-6.18.46-<tag>-long.log`, because a generator takes one launch object
per file.

The fourth argument `cache` patches the devicetree qemu dumped, so the boot
CPU carries an L1I, an L1D and an L2 (`patch_dtb.py`). qemu's own `-M virt`
devicetree has no cache property, so without it every `AT_L*_CACHE*` word is
zero and a check of those words shows nothing.

A start-state launch object holds, besides the five keys of a placement log:
`config`, `dt_cache` and `cmdline`, which `run-kernel.sh` merges in because
the probe cannot read them, and `run`, `argv`, `envp`, `execfn`,
`mmap_rnd_bits`, `mmap_rnd_bits_max`, `randomize_va_space`, `vlenb`, `elf`,
`sp_at_start`, `stack_end`, `vvar_start`, `auxv`, `stack_bytes` and
`vdso_image`. `sp_at_start` is the x2 the kernel chose: the probe is built
`-nostartfiles`, and its own `_start` stores x2 before anything else runs.
`mmap_rnd_bits_max` is measured, not read: there is no such file, so the probe
writes candidates to `vm.mmap_rnd_bits` and writes the launch's value back.
`vlenb` is read with `csrr` only when AT_HWCAP carries the V bit, because the
CSR traps without it and a trap in init panics the kernel. `elf` is the
probe's own ELF header — `{"base", "phoff", "phdr", "phentsize", "phnum",
"entry"}`, with `phdr` = `base + phoff` — read out of its own mapped image
(`read_elf_facts`), so that the four auxv entries the kernel copies out of
that header are checked against the header instead of being fed back in. It
is `null` when the first mapping carries no ELF magic. The key is written by
the start-state run, so the ten start-state logs carry it and the four
placement logs do not; all fourteen in the tree were re-captured from the
probe that writes it, so the four auxv entries are a check and not an input.

### The check: a Rocq term, computed against the model

```bash
python3 tools/placement_conformance/start_state_to_rocq.py LOG --out F.v \
    [--name NAME] [--va {Sv39,Sv48,Sv57}]
```

This writes a Rocq file that states the recorded launch as LPS terms — the
`ProcInput` with its `KernelBuild`, the `ExecEntry` with the recorded stack
end and the sixteen AT_RANDOM bytes in its draw, the recorded block and the
recorded auxiliary vector — and closes three lemmas:

| Lemma | What it says |
| --- | --- |
| `launch_ok` | `Run.entry_launch_ok_va` holds of the recorded stack end, stack pointer and mmap base. |
| `block_ok` | `Run.entry_stack_image` equals the bytes the kernel wrote, every byte of them. |
| `auxv_ok` | `StackLayout.auxv_entries` equals the recorded `/proc/self/auxv`. |

Nothing in the generator states what the model says: the block is computed
by Rocq from `StackLayout.v` itself. `launch_ok` names one number the
generator works out — the page draw `arch_mmap_rnd` made, which
`Run.valid_launch_base` quantifies over — and the proof recomputes
`Run.mmap_base_of` at that draw, so a wrong number makes the file fail to
compile rather than makes a wrong lemma pass. `block_ok` excludes nothing:
the sixteen AT_RANDOM bytes are the record's own, carried in the draw.

`../../tests/dune` of the entry tree has one rule per log, so `dune build`
compiles all ten and a start state LPS does not reproduce breaks the build.
Each file costs 0.9 to 2.5 seconds of `rocq compile`, 15.7 seconds for the
ten: a block of a few kilobytes is cheap for `vm_compute`.

Ten passing equalities would also pass if `block_ok` had stopped computing
anything, so two more rules run the generator with `--perturb-byte K`. Each
moves one byte of the kernel's block, states the DISAGREEMENT, and compiles
only if the model refuses the moved block; each names its admitted
neighbour in its own header, so the refusal and the case still admitted come
as a pair. One is on the shortest record (byte 0, the low byte of `argc`),
one on the longest (byte 7,000, in the string area). They cost 1.00 s and
4.08 s, and bring the set to 20.8 seconds.

### The evidence: the Python checker

```bash
python3 tools/placement_conformance/check_start_state.py LOG [LOG ...] \
    [--vdso $PC_WORK/kernels/<cfg>/vdso.so]
```

`check_start_state.py` is no longer the check. It compares the record with a
PYTHON TRANSCRIPTION of the model, between the markers
`MODEL TRANSCRIPTION BEGINS` and `MODEL TRANSCRIPTION ENDS`: a second model
of the entry block that nothing proves agrees with the first. Its run stands
as evidence — 100 verdicts over 10 records, 0 failures on the re-captured
logs, and 110 of 110 on the first capture, where the kernel's `vdso.so` was
to hand for the ten extra verdicts — and it
reads two things the Rocq files do not: the recorded vDSO image against the
kernel build's own `vdso.so`, and the distance from the `[vvar]` mapping to
AT_SYSINFO_EHDR. It exits 0 when every sub-check of every log passes. Both
sets of results are in `reports/a4-start-state.md` of the entry lane's clone.
