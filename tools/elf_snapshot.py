#!/usr/bin/env python3
"""
elf_snapshot.py -- Static ELF-based snapshot for RISC-V binaries.

Parses LOAD segments directly from the ELF program header table.
No debugger, no ptrace, no QEMU required.  Works on any host architecture.

Usage:
    python3 tools/elf_snapshot.py <binary> [output_dir_or_MemImage.v]
    python3 tools/elf_snapshot.py --rebuild <MemImage.v> <out-binary>

Every mode honours one whole-image byte cap, taken from --max-total-bytes if
given, else the ELF_SNAPSHOT_MAX_TOTAL_BYTES environment variable, else the
MAX_TOTAL_BYTES constant below -- and never above MAX_TOTAL_BYTES_CEILING,
the largest image this toolchain can coqchk.  So the --verify build gate
checks binaries against the very cap the snapshot will later run under,
and reports on every run which cap that was and which of the three
sources set it.

init_pc is always the ELF header's e_entry: that is where the kernel
transfers control (load_elf_binary), regardless of any symbol-table
entries (which can be stripped, or point elsewhere).

--rebuild runs the other way: from a committed snapshot back to an ELF the
kernel loads to exactly that image.  See rebuild_elf for what it recovers,
what it cannot, and the check that holds it to the snapshot.
"""

from __future__ import annotations

import argparse
import os
import re
import struct
import sys

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# Primitive-string chunk and whole-snapshot size caps.
#
# The whole-image cap is a budget limit, not a soundness one: an oversized
# image is rejected outright rather than truncated.  Individual logical
# segments are not capped; their byte payload is divided into bounded
# primitive strings without changing the modeled mapping.
#
# WHAT AN IMAGE COSTS, measured on Rocq 9.2, per byte
# of snapshotted image: about 4.1 MB of snapshot-time RSS per MiB, two
# bytes of .hex, and four bytes of compiled .vo.  At this cap that is
# about 1.6 s to snapshot and 5.5 s to compile, a 2.1 GB .vo, and about
# 17 s and 1.2 GB of RSS to coqchk.
#
# HARD CEILING on the whole-image cap, measured: just under 2 GiB of
# image.  Past it the .vo's two Marshal segments cross 2^32 bytes and are
# written with OCaml's 64-bit big header, which coqchk's
# checker/analyze.ml asserts against.  An image of
# MAX_TOTAL_BYTES_CEILING still passes coqchk; 2048 MiB of image dies
# inside coqchk with an anomaly, while `rocq compile` reads that same .vo
# fine.  The rule behind the number: twice the image bytes, plus roughly
# 200 KB for everything else in the file, must stay below 2^32.  An image
# admitted above the ceiling is one the checker cannot check, so an effective
# cap over it is refused rather than honoured -- see
# resolve_max_total_bytes.
MAX_TOTAL_BYTES = 512 * 1024 * 1024
MAX_TOTAL_BYTES_CEILING = 2040 * 1024 * 1024

# Environment override for the whole-image cap, outranked by the
# --max-total-bytes flag.  See resolve_max_total_bytes for the precedence
# and for what each source is checked against.
MAX_TOTAL_BYTES_ENV = "ELF_SNAPSHOT_MAX_TOTAL_BYTES"

# HARD CEILING on MAX_CHUNK_BYTES: each chunk is emitted as a hex text file
# and read back with rocq-read-file's ReadFileString, whose result must
# inhabit the [seg_bytes] string list
# (theories/LinuxProcessSem/MemImageType.v).  Hex costs two characters per
# byte, and a file over
# PrimString.max_length (0xfffffb) comes back as `NestedArray 1 string`
# instead, which does not typecheck there -- so a chunk can hold at most
# 0xfffffb // 2 = 8388605 bytes.  Larger logical segments are represented by
# several chunks; their address range and permissions are not split.
#
# The cost of raising it is small: the bytes land in a .hex file rather
# than in the Rocq term, and the image checks index that string instead of
# scanning it, so a 1.07 MiB segment costs well under a second to check.
#
# Largest chunk rocq-read-file can hand back as a PrimString.  Not a
# tunable: it is fixed by PrimString.max_length.
PRIMSTRING_MAX_CHUNK_BYTES = 0xFFFFFB // 2
MAX_CHUNK_BYTES = PRIMSTRING_MAX_CHUNK_BYTES

# The kernel maps LOAD segments in whole pages: the mapped extent of a
# segment is [round_down(p_vaddr), round_up(p_vaddr + p_memsz)), and it is
# a FILE mapping of those pages, so the in-page slack around the segment's
# own bytes holds the file's neighboring bytes — see the mapping rule at
# the seg_data computation below.  Everything past p_vaddr + p_filesz of a
# bss-carrying segment reads as zeros (musl's brk heap starts in that
# writable tail slack).  The snapshot mirrors that so the model's
# memory map has kernel page granularity — see also Run.segment_reservation,
# which reserves exactly these page-rounded extents.
PAGE_SIZE = 4096

# Hard ceiling on LOAD segment end addresses (p_vaddr + p_memsz).
#
# The Rocq syscall model grants allocator memory (anonymous mmap, brk
# grow) anywhere below `alloc_top`, 8 MiB under the run's initial stack
# pointer -- see theories/LinuxProcessSem/State.v and the brk/mmap
# specs in Specs.v.  Successful brk/mmap zero-fills write `Some 0` into
# the machine-state memory overlay, which SHADOWS loaded-segment bytes on
# data reads.  Keeping every snapshotted segment below this conservative
# ceiling keeps loaded segments well clear of where grants land.
SEGMENT_END_CEILING = 0x100000000
EXCLUDE_STACK_BY_DEFAULT = True

# The ELF supplies exactly three things the model needs: the entry point
# (init_pc), the loadable segments, and where the PROGRAM HEADER TABLE
# lands in memory (phdrs, published to the process as
# AT_PHDR/AT_PHENT/AT_PHNUM -- see below).  The initial register file is NOT
# snapshot data — at Linux RISC-V process entry the kernel zeroes every GPR
# except sp, which points at the argv/envp/auxv block; a0 is 0 (argc lives
# on the stack).  The process model encodes that directly
# (Run.init_machine_state): sp is quantified over the ASLR window
# (Run.valid_sp) and every other register, a0 included, starts at 0.
#
# AT_PHDR and thread-local storage.  A statically linked libc reads its own
# program headers to find the segments the kernel describes no other way —
# above all PT_TLS, the initialization image for thread-local storage.
# musl's __init_tls walks [AT_PHDR, AT_PHDR + AT_PHNUM*AT_PHENT), sizes the
# thread block from PT_TLS's p_memsz/p_align, copies p_filesz bytes of
# initialized TLS data out of it, and only then sets tp.  So the phdr
# table's location is process-startup data exactly like the entry point,
# and this loader derives it the way the kernel does (see _phdr_info).

# ELF constants
EI_MAG = b"\x7fELF"
ELFCLASS64 = 2
ELFDATA2LSB = 1
EM_RISCV = 243
PT_LOAD = 1
PT_TLS = 7
# Size of an ELF64 program header (Elf64_Phdr).  Linux's execve refuses any
# other e_phentsize, and a table larger than 64 KiB: load_elf_phdrs
# (fs/binfmt_elf.c, v6.18.46) returns NULL for both, and load_elf_binary
# then fails with ENOEXEC.
PHDR_ENTSIZE = 56
PHDR_TABLE_MAX = 65536
PF_X = 1
PF_W = 2
PF_R = 4

# ---------------------------------------------------------------------------
# The effective whole-image cap
# ---------------------------------------------------------------------------


def _checked_cap(raw, source: str) -> int:
    """Parse *raw* as a whole-image byte cap, naming *source* on refusal."""
    if isinstance(raw, bool):
        raise ValueError("%s: %r is not a byte count" % (source, raw))
    try:
        value = int(raw, 0) if isinstance(raw, str) else int(raw)
    except (TypeError, ValueError):
        raise ValueError(
            "%s: %r is not an integer number of bytes" % (source, raw)
        ) from None
    if value <= 0:
        raise ValueError(
            "%s: %d is not a positive number of bytes" % (source, value)
        )
    if value > MAX_TOTAL_BYTES_CEILING:
        raise ValueError(
            "%s: %d bytes is above MAX_TOTAL_BYTES_CEILING=%d, the largest "
            "image this toolchain can check -- past that the snapshot's .vo "
            "crosses the Marshal 2^32 header switch and coqchk dies on it, "
            "so setup would admit an image the checker never checks"
            % (source, value, MAX_TOTAL_BYTES_CEILING)
        )
    return value


# How each source is named wherever a run reports which one supplied its
# cap.  The three are distinct phrases, not overlapping substrings, so a
# report can be read back unambiguously -- note that MAX_TOTAL_BYTES is
# itself a substring of MAX_TOTAL_BYTES_ENV.
CAP_SOURCE_FLAG = "the --max-total-bytes flag"
CAP_SOURCE_ENV = "the %s environment variable" % MAX_TOTAL_BYTES_ENV
CAP_SOURCE_CONSTANT = "the MAX_TOTAL_BYTES constant"
CAP_SOURCE_ARGUMENT = "the max_total_bytes argument"


def resolve_max_total_bytes_with_source(flag_value=None, env=None):
    """Return ``(cap, source)``: the whole-image byte cap this run must
    honour, and the phrase naming where it came from.

    Precedence: the ``--max-total-bytes`` flag, then the
    ELF_SNAPSHOT_MAX_TOTAL_BYTES environment variable, then the
    MAX_TOTAL_BYTES constant.  An environment variable that is unset, empty
    or blank is no setting at all; every source that IS set is checked even
    when an outranking one supplies the value, so a mistyped override is an
    error here rather than a setting silently ignored all the way through
    the run.  No source may name a cap above MAX_TOTAL_BYTES_CEILING.

    The source travels with the number because a cap is only meaningful
    alongside what set it: a run reporting a bare figure leaves a reader
    unable to tell an intended override from a stale variable in the
    environment.

    Raises:
        ValueError: if any source that is set is unparsable, non-positive,
            or above the ceiling.  The message names the source.
    """
    if env is None:
        env = os.environ
    raw_env = env.get(MAX_TOTAL_BYTES_ENV)
    env_source = "environment variable %s" % MAX_TOTAL_BYTES_ENV
    from_env = None
    if isinstance(raw_env, str):
        # A blank setting is no setting at all, matching shell idiom.
        if raw_env.strip():
            from_env = _checked_cap(raw_env.strip(), env_source)
    elif raw_env is not None:
        # A real environment yields only strings, so a value of any other
        # type came from a mapping a caller built by hand.  Check it rather
        # than trip over it: a bare .strip() would raise AttributeError,
        # which names neither the variable nor what was wrong with it.
        from_env = _checked_cap(raw_env, env_source)
    if flag_value is not None:
        return _checked_cap(flag_value, "--max-total-bytes"), CAP_SOURCE_FLAG
    if from_env is not None:
        return from_env, CAP_SOURCE_ENV
    return MAX_TOTAL_BYTES, CAP_SOURCE_CONSTANT


def resolve_max_total_bytes(flag_value=None, env=None) -> int:
    """The cap alone, for callers with nothing to report it to.

    See resolve_max_total_bytes_with_source for the precedence and the
    checks; this discards only the source phrase.
    """
    return resolve_max_total_bytes_with_source(flag_value, env)[0]


def _take_max_total_bytes_flag(argv):
    """Pull ``--max-total-bytes N`` / ``--max-total-bytes=N`` out of *argv*.

    The three alternate modes below are dispatched by scanning argv before
    argparse ever runs, so they need the flag lifted out by hand to honour
    it the way the default mode does.

    Returns:
        (remaining argv, the flag's raw value or None).

    Raises:
        ValueError: if the flag is given without a value.
    """
    rest = []
    value = None
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--max-total-bytes":
            if i + 1 >= len(argv):
                raise ValueError("--max-total-bytes: missing its value")
            value = argv[i + 1]
            i += 2
            continue
        if a.startswith("--max-total-bytes="):
            value = a.split("=", 1)[1]
            i += 1
            continue
        rest.append(a)
        i += 1
    return rest, value


# ---------------------------------------------------------------------------
# ELF parser
# ---------------------------------------------------------------------------


def _parse_elf(path: str, max_total_bytes=None) -> dict:
    """Parse a 64-bit little-endian RISC-V ELF and return segments + entry.

    Args:
        path: the ELF to parse.
        max_total_bytes: whole-image byte cap for this parse.  None resolves
            it the way the command line does (resolve_max_total_bytes): the
            environment variable, else the MAX_TOTAL_BYTES constant.  A value
            given here outranks both and is held to the same ceiling.

    Returns dict with keys:
        entry: int (e_entry)
        segments: list of {base, size, perms, hex_bytes}
        phdrs: {addr, ent, num} -- the auxv's AT_PHDR/AT_PHENT/AT_PHNUM
    """
    if max_total_bytes is None:
        max_total_bytes = resolve_max_total_bytes()
    else:
        max_total_bytes = _checked_cap(max_total_bytes, "max_total_bytes")

    with open(path, "rb") as f:
        data = f.read()

    if len(data) < 64:
        raise ValueError("File too small to be an ELF")

    magic = data[:4]
    if magic != EI_MAG:
        raise ValueError("Not an ELF file (bad magic)")

    ei_class = data[4]
    if ei_class != ELFCLASS64:
        raise ValueError("Not a 64-bit ELF (EI_CLASS=%d)" % ei_class)

    ei_data = data[5]
    if ei_data != ELFDATA2LSB:
        raise ValueError("Not little-endian (EI_DATA=%d)" % ei_data)

    e_machine = struct.unpack_from("<H", data, 18)[0]
    if e_machine != EM_RISCV:
        raise ValueError(
            "Not RISC-V (e_machine=0x%x, expected 0x%x)" % (e_machine, EM_RISCV)
        )

    e_entry = struct.unpack_from("<Q", data, 24)[0]
    e_phoff = struct.unpack_from("<Q", data, 32)[0]
    e_phentsize = struct.unpack_from("<H", data, 54)[0]
    e_phnum = struct.unpack_from("<H", data, 56)[0]

    if e_phentsize != PHDR_ENTSIZE:
        raise ValueError(
            "e_phentsize=%d is not the size of an ELF64 program header (%d "
            "bytes): Linux's execve refuses the file (load_elf_phdrs, "
            "fs/binfmt_elf.c)" % (e_phentsize, PHDR_ENTSIZE)
        )
    if e_phnum * PHDR_ENTSIZE > PHDR_TABLE_MAX:
        raise ValueError(
            "e_phnum=%d: Linux's execve refuses a program header table "
            "larger than %d bytes (load_elf_phdrs, fs/binfmt_elf.c)"
            % (e_phnum, PHDR_TABLE_MAX)
        )
    if e_phoff + e_phnum * e_phentsize > len(data):
        raise ValueError(
            "program header table [0x%x, 0x%x) runs past the end of the "
            "0x%x-byte ELF (truncated or crafted file)"
            % (e_phoff, e_phoff + e_phnum * e_phentsize, len(data))
        )

    # Parse LOAD segments (noting PT_TLS along the way)
    segments = []
    tls_ranges = []
    total_bytes = 0
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        p_type = struct.unpack_from("<I", data, off)[0]
        if p_type == PT_TLS:
            # The TLS initialization image.  It needs no segment of its own:
            # PT_TLS always overlays a PT_LOAD (the .tdata/.tbss tail of the
            # writable one), so its bytes are snapshotted with that segment.
            # What libc needs beyond the bytes is the ability to FIND this
            # header, which is what the auxv's AT_PHDR provides; recorded
            # here only so the containment check below can confirm the init
            # image really is in the snapshot.
            tls_ranges.append(
                (
                    struct.unpack_from("<Q", data, off + 16)[0],  # p_vaddr
                    struct.unpack_from("<Q", data, off + 32)[0],  # p_filesz
                )
            )
            continue
        if p_type != PT_LOAD:
            continue

        p_flags = struct.unpack_from("<I", data, off + 4)[0]
        p_offset = struct.unpack_from("<Q", data, off + 8)[0]
        p_vaddr = struct.unpack_from("<Q", data, off + 16)[0]
        p_filesz = struct.unpack_from("<Q", data, off + 32)[0]
        p_memsz = struct.unpack_from("<Q", data, off + 40)[0]

        # The kernel maps whole pages: [round_down(vaddr), round_up(vaddr +
        # memsz)).  How the slack inside those pages reads is fixed by
        # fs/binfmt_elf.c's elf_load(), mirrored at the seg_data
        # computation below.  A zero-memsz segment maps nothing at all.
        if p_memsz == 0:
            continue

        # A w+x (RWX) segment is snapshotted like any other: instruction
        # fetch reads a writable executable segment through the writable
        # overlay with the image bytes underneath (code_read_ov in
        # theories/LinuxProcessSem/RiscvSemantics.v), so an RWX text
        # segment — GNU ld's default -z noseparate-code merges .text with
        # the initialized writable sections whenever they fit — executes
        # faithfully.

        ext_lo = p_vaddr - (p_vaddr % PAGE_SIZE)
        ext_hi = ((p_vaddr + p_memsz + PAGE_SIZE - 1) // PAGE_SIZE) * PAGE_SIZE
        ext_size = ext_hi - ext_lo

        if ext_hi > SEGMENT_END_CEILING:
            raise ValueError(
                "LOAD segment at vaddr=0x%x memsz=0x%x maps pages up to 0x%x, "
                "above the 0x%x ceiling: segments must stay clear of the "
                "syscall model's allocator grants (alloc_top in "
                "theories/LinuxProcessSem/State.v) so that "
                "model-forced brk/mmap zero-fills cannot shadow "
                "loaded-segment bytes"
                % (p_vaddr, p_memsz, ext_hi, SEGMENT_END_CEILING)
            )

        if total_bytes + ext_size > max_total_bytes:
            raise ValueError(
                "LOAD segment at vaddr=0x%x memsz=0x%x (page-rounded to 0x%x "
                "bytes) pushes the snapshot past the whole-image cap of 0x%x "
                "bytes (MAX_TOTAL_BYTES, overridable with --max-total-bytes "
                "or %s); 0x%x bytes already loaded; refusing to drop it from "
                "the snapshot"
                % (p_vaddr, p_memsz, ext_size, max_total_bytes,
                   MAX_TOTAL_BYTES_ENV, total_bytes)
            )

        # A truncated or crafted ELF can claim more file-backed bytes than
        # the file actually holds; Python slicing would silently shorten the
        # segment and the zero-padding below would fabricate the missing
        # bytes.  Fail hard instead of snapshotting bytes the file lacks.
        if p_offset + p_filesz > len(data):
            raise ValueError(
                "LOAD segment at vaddr=0x%x claims file extent "
                "[0x%x, 0x%x) but the ELF is only 0x%x bytes long "
                "(truncated or crafted file)"
                % (p_vaddr, p_offset, p_offset + p_filesz, len(data))
            )

        # A file-backed segment can only be mapped if p_vaddr and p_offset
        # are congruent mod the page size: the kernel's elf_map passes
        # vm_mmap the file offset p_offset - (p_vaddr % PAGE), and vm_mmap
        # refuses a non-page-aligned offset, failing the execve outright.
        # A binary the kernel cannot start has no process semantics to
        # snapshot, so fail closed (no real linker emits this shape).
        if p_filesz > 0 and (p_offset - p_vaddr) % PAGE_SIZE != 0:
            raise ValueError(
                "LOAD segment has p_vaddr=0x%x and p_offset=0x%x, which are "
                "not congruent mod the 0x%x page size: the kernel's elf_map "
                "passes vm_mmap a non-page-aligned file offset and the "
                "execve fails, so this binary cannot be started at all"
                % (p_vaddr, p_offset, PAGE_SIZE)
            )

        # The segment's pages are a FILE mapping, not the segment's bytes
        # padded with zeros: elf_load() (fs/binfmt_elf.c) mmaps
        # [ext_lo, round_up(p_vaddr + p_filesz)) from file offset
        # p_offset - delta.  So the head slack [ext_lo, p_vaddr) holds the
        # delta file bytes BEFORE p_offset (for an lld/zig layout whose
        # first section starts mid-page, that is the ELF header and program
        # header table — mapped memory a real process can read), and the
        # tail of the last file page holds the bytes AFTER
        # p_offset + p_filesz.  Only a bss-carrying segment
        # (p_memsz > p_filesz) is zeroed past p_vaddr + p_filesz: elf_load
        # memsets the rest of that page and maps the remaining pages
        # anonymous.  Bytes the mapping asks for beyond EOF read as zeros
        # (the last file page's zero fill).  A p_filesz == 0 segment maps
        # only anonymous pages.
        delta = p_vaddr - ext_lo
        if p_filesz == 0:
            seg_data = b"\x00" * ext_size
        else:
            file_lo = p_offset - delta
            file_span = (
                (delta + p_filesz + PAGE_SIZE - 1) // PAGE_SIZE
            ) * PAGE_SIZE
            mapped = data[file_lo : file_lo + file_span]
            mapped += b"\x00" * (file_span - len(mapped))
            if p_memsz > p_filesz:
                mapped = mapped[: delta + p_filesz]
            seg_data = mapped + b"\x00" * (ext_size - len(mapped))

        r = "r" if (p_flags & PF_R) else "-"
        w = "w" if (p_flags & PF_W) else "-"
        x = "x" if (p_flags & PF_X) else "-"

        segments.append(
            {
                "base": ext_lo,
                "size": ext_size,
                "perms": r + w + x,
                "hex_bytes": seg_data.hex(),
                # The segment's own file extent, kept for the AT_PHDR
                # computation in _phdr_info (dropped before emission).
                "p_offset": p_offset,
                "p_filesz": p_filesz,
                "p_vaddr": p_vaddr,
            }
        )
        total_bytes += ext_size

    # Reject overlapping LOAD segments.  The kernel mmaps segments in phdr
    # order, so on overlap the LAST mapping wins; the model's find_segment
    # (theories/LinuxProcessSem/RiscvSemantics.v) is a
    # first-match scan, so it would resolve the overlap the other way.
    # Real toolchain output never overlaps (the ELF spec requires PT_LOAD
    # entries sorted and non-overlapping in vaddr), so instead of teaching
    # the loader/model kernel overlap semantics, fail closed on the crafted
    # case.  Zero-memsz segments map nothing and cannot overlap.
    by_base = sorted(
        (s for s in segments if s["size"] > 0), key=lambda s: s["base"]
    )
    for prev, cur in zip(by_base, by_base[1:]):
        if prev["base"] + prev["size"] > cur["base"]:
            raise ValueError(
                "overlapping LOAD segments: [0x%x, 0x%x) and [0x%x, 0x%x); "
                "the kernel resolves overlaps last-mapping-wins while the "
                "model's find_segment scan is first-match, so overlapping "
                "segments cannot be snapshotted faithfully (and no real "
                "toolchain emits them)"
                % (
                    prev["base"],
                    prev["base"] + prev["size"],
                    cur["base"],
                    cur["base"] + cur["size"],
                )
            )

    # Reject an image with NO mapped LOAD segment (e_phnum == 0, no PT_LOAD
    # entry, or only p_memsz == 0 ones).  This is the MAXIMALLY vacuous
    # image: find_segment always returns None on an empty segment list, so
    # the very first instruction fetch fails, [Run.all_traces_error] holds
    # of the initial configuration, and [Equivalence.equiv]'s bh_all_errors
    # escape admits ANY target.  The Rocq-side check is
    # [Equivalence.image_entry_fetchable], asserted per example in
    # Checker.v; this is the same check one layer earlier, at the point
    # where the image is built.  No linker emits such an executable, so this
    # only ever fires on a crafted or truncated file — same class as the
    # overlap and truncation rejections above.
    if not segments:
        raise ValueError(
            "ELF has no mapped PT_LOAD segment (no PT_LOAD entry, or only "
            "p_memsz == 0 ones): the resulting image maps nothing, so "
            "find_segment fails for every address and the process faults on "
            "its very first instruction fetch.  As a source image that is "
            "vacuous — every execution errors, and Equivalence.equiv's "
            "bh_all_errors escape then accepts any target "
            "(Equivalence.image_entry_fetchable is the Rocq-side check "
            "that rejects this).  No real toolchain emits such an "
            "executable, so this file is crafted or truncated."
        )

    phdrs = _phdr_info(segments, e_phoff, e_phentsize, e_phnum)

    # PT_TLS's initialization image must be readable in the snapshot: musl's
    # __copy_tls memcpy's p_filesz bytes out of it on every startup.  It
    # always overlays a PT_LOAD in real toolchain output, so a miss here
    # means a crafted or unusual ELF, not a modeling gap.
    for tls_vaddr, tls_filesz in tls_ranges:
        if not _range_readable(segments, tls_vaddr, tls_filesz):
            raise ValueError(
                "PT_TLS initialization image [0x%x, 0x%x) is not covered by "
                "a readable LOAD segment, so the snapshot cannot supply the "
                "bytes libc copies into each thread's TLS block"
                % (tls_vaddr, tls_vaddr + tls_filesz)
            )

    for seg in segments:
        for k in ("p_offset", "p_filesz", "p_vaddr"):
            del seg[k]

    return {
        "entry": e_entry,
        "segments": segments,
        "phdrs": phdrs,
    }


def _range_readable(segments, addr: int, size: int) -> bool:
    """Is [addr, addr+size) wholly inside one readable snapshotted segment?

    Zero-length ranges are vacuously fine.  Segments are page-rounded
    extents, which is exactly what the model maps, so this asks the
    question the model will ask at run time.
    """
    if size == 0:
        return True
    for seg in segments:
        if "r" not in seg["perms"]:
            continue
        if seg["base"] <= addr and addr + size <= seg["base"] + seg["size"]:
            return True
    return False


def _phdr_info(segments, e_phoff: int, e_phentsize: int, e_phnum: int) -> dict:
    """Where the program header table lands in memory: AT_PHDR/AT_PHENT/AT_PHNUM.

    The kernel reports the address the table got by virtue of lying inside a
    mapped LOAD segment: for the segment whose FILE extent covers e_phoff,
    p_vaddr + (e_phoff - p_offset)  (fs/binfmt_elf.c, load_elf_binary's
    phdr_addr).  Static non-PIE riscv64 binaries put the table in the first
    LOAD segment, which starts at file offset 0, so this is just e_phoff
    above the image base.

    The kernel's loop has no `break`: it assigns phdr_addr for EVERY PT_LOAD
    whose file extent covers e_phoff, so on the (crafted-only) ELF where
    several do, the LAST one in program-header order wins.  `segments` is
    built in that order, so scanning it and keeping the last match reproduces
    the kernel exactly.  Real toolchain output has exactly one covering
    PT_LOAD, at p_offset 0, where first and last coincide; taking the first
    would silently publish a different AT_PHDR than a real execve on the
    crafted case, and musl derives its load base from AT_PHDR
    (base = phdr - PT_PHDR's p_vaddr) before reading the PT_TLS init image
    through it, so a wrong AT_PHDR moves every TLS byte the process copies.

    Fails closed if the table is not covered by a mapped segment, or if the
    mapped range is not wholly readable in the snapshot: the model would
    then hand libc an AT_PHDR pointing at memory the process cannot read,
    and musl's __init_tls would fault (or, worse, read something else) while
    laying out thread-local storage.  The same containment is machine-checked
    inside Rocq, per example, by Checker.v's image_phdrs_readable
    (theories/EquivalenceDefinition/Equivalence.v) -- this check is one layer
    earlier, where the image is built, and outside the trust boundary.
    """
    covering = [
        seg
        for seg in segments
        if seg["p_offset"] <= e_phoff < seg["p_offset"] + seg["p_filesz"]
    ]
    if covering:
        seg = covering[-1]  # last mapping wins, as in load_elf_binary
        addr = seg["p_vaddr"] + (e_phoff - seg["p_offset"])
        size = e_phnum * e_phentsize
        if not _range_readable(segments, addr, size):
            raise ValueError(
                "program header table maps to [0x%x, 0x%x), which is not "
                "wholly covered by a readable LOAD segment: the model would "
                "publish an AT_PHDR the process cannot read, and libc's TLS "
                "setup walks exactly that range" % (addr, addr + size)
            )
        return {"addr": addr, "ent": e_phentsize, "num": e_phnum}

    raise ValueError(
        "the program header table at file offset 0x%x is not inside any "
        "PT_LOAD segment's file extent, so it is not mapped into the "
        "process and the model cannot publish AT_PHDR; a static libc needs "
        "it to find PT_TLS (thread-local storage)" % e_phoff
    )


# ---------------------------------------------------------------------------
# Coq emitter
# ---------------------------------------------------------------------------

MAIN_HEADER_TEMPLATE = """\
(** Auto-generated by elf-snapshot — do not edit.
    Loads segment bytes from .hex files via rocq-read-file. *)
From Stdlib Require Import NArith List String PrimString.
From ReadFile Require Import ReadFile.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Import ListNotations.
Local Open Scope string_scope.

"""

DEFAULT_NAMESPACE = "LinuxProcessSemantics.LinuxProcessSem"


def _hex_file_name(prefix, seg_idx, chunk_idx, chunk_count):
    if chunk_count == 1:
        return "%s_seg_%03d.hex" % (prefix, seg_idx)
    return "%s_seg_%03d_chunk_%03d.hex" % (prefix, seg_idx, chunk_idx)


def _hex_chunks(hex_bytes):
    """Split hex text at the exact largest size ReadFileString can return."""
    chars = 2 * MAX_CHUNK_BYTES
    return [hex_bytes[i : i + chars] for i in range(0, len(hex_bytes), chars)]


def _remove_stale_hex_files(out_dir, prefix, current_names):
    """Remove only obsolete chunks owned by this generated snapshot."""
    owned = re.compile(
        r"^%s_seg_[0-9]+(?:_chunk_[0-9]+)?\.hex$" % re.escape(prefix)
    )
    current = set(current_names)
    for name in os.listdir(out_dir):
        if owned.fullmatch(name) and name not in current:
            os.remove(os.path.join(out_dir, name))


def _emit_coq(
    segments,
    init_pc,
    phdrs,
    out_path,
    prefix="MemImage",
    namespace=DEFAULT_NAMESPACE,
    module_name=None,
):
    """Write <prefix>.v plus bounded .hex chunks for each logical segment.

    When ``module_name`` is given, the file ends with a
    ``Module <module_name> <: MemImage`` wrapper exposing
    ``loaded_segments``/``init_pc`` so the file can be fed directly to the
    ``Equivalence`` functor (see Equivalence.v)."""
    out_dir = os.path.dirname(os.path.abspath(out_path))
    os.makedirs(out_dir, exist_ok=True)

    segment_hex_files = []
    for seg_idx, seg in enumerate(segments):
        chunks = _hex_chunks(seg["hex_bytes"])
        hex_files = []
        for chunk_idx, chunk in enumerate(chunks):
            hex_name = _hex_file_name(
                prefix, seg_idx, chunk_idx, len(chunks)
            )
            hex_files.append(hex_name)
            hex_path = os.path.join(out_dir, hex_name)
            with open(hex_path, "w") as f:
                f.write(chunk)
        segment_hex_files.append(hex_files)

    lines = [MAIN_HEADER_TEMPLATE]

    segment_byte_defs = []
    for seg_idx, hex_files in enumerate(segment_hex_files):
        byte_defs = []
        for chunk_idx, hex_name in enumerate(hex_files):
            if len(hex_files) == 1:
                byte_def_name = "%s_seg_bytes_%03d" % (prefix, seg_idx)
                dep_ident = "%s_seg_dep_%03d" % (prefix, seg_idx)
            else:
                byte_def_name = "%s_seg_bytes_%03d_%03d" % (
                    prefix, seg_idx, chunk_idx
                )
                dep_ident = "%s_seg_dep_%03d_%03d" % (
                    prefix, seg_idx, chunk_idx
                )
            byte_defs.append(byte_def_name)
            lines.append(
                'From %s Extra Dependency "%s" as %s.\n'
                % (namespace, hex_name, dep_ident)
            )
            lines.append(
                "ReadFileString %s As %s.\n" % (dep_ident, byte_def_name)
            )
            lines.append("Global Strategy 200 [%s].\n" % byte_def_name)
        segment_byte_defs.append(byte_defs)
    if segment_byte_defs:
        lines.append("\n")

    seg_def_names = []
    for idx, (seg, byte_defs) in enumerate(zip(segments, segment_byte_defs)):
        name = "%s_segment_%03d" % (prefix, idx)
        seg_def_names.append(name)
        lines.append(
            "Definition %s : Segment := {|\n"
            "  seg_base  := 0x%x%%N;\n"
            "  seg_size  := 0x%x%%N;\n"
            '  seg_perms := "%s";\n'
            "  seg_bytes := [%s]\n"
            "|}.\n\n"
            % (
                name,
                seg["base"],
                seg["size"],
                seg["perms"],
                "; ".join(byte_defs),
            )
        )

    if seg_def_names:
        body = "[ " + ";\n  ".join(seg_def_names) + "\n]"
    else:
        body = "[]"
    lines.append(
        "Definition %s_loaded_segments : list Segment :=\n  %s.\n\n" % (prefix, body)
    )

    # The only register the ELF actually specifies: the entry point.
    lines.append("Definition %s_init_pc : N := 0x%x%%N.\n" % (prefix, init_pc))

    # Where the program header table is mapped, as the kernel publishes it
    # in the auxv (AT_PHDR/AT_PHENT/AT_PHNUM).  A static libc walks it to
    # find PT_TLS before laying out thread-local storage; see
    # MemImageType.PhdrInfo.
    lines.append(
        "Definition %s_phdrs : PhdrInfo := {|\n"
        "  ph_addr := 0x%x%%N;\n"
        "  ph_ent  := %d%%N;\n"
        "  ph_num  := %d%%N\n"
        "|}.\n" % (prefix, phdrs["addr"], phdrs["ent"], phdrs["num"])
    )

    strategy_names = seg_def_names + ["%s_loaded_segments" % prefix]
    lines.append("Global Strategy 200 [%s].\n" % " ".join(strategy_names))

    if module_name is not None:
        lines.append(
            "\n(* Packaged for the Equivalence functor (Equivalence.v). *)\n"
            "Module %s <: MemImage.\n"
            "  Definition loaded_segments := %s_loaded_segments.\n"
            "  Definition init_pc := %s_init_pc.\n"
            "  Definition phdrs := %s_phdrs.\n"
            "End %s.\n"
            % (module_name, prefix, prefix, prefix, module_name)
        )

    lines.append("\n")
    content = "".join(lines)

    with open(out_path, "w") as f:
        f.write(content)

    _remove_stale_hex_files(
        out_dir,
        prefix,
        [name for names in segment_hex_files for name in names],
    )


# ---------------------------------------------------------------------------
# Programmatic API
# ---------------------------------------------------------------------------


def snapshot_binary(
    binary_path: str,
    out_dir: str,
    prefix: str = "MemImage",
    namespace: str = DEFAULT_NAMESPACE,
    module_name: str | None = None,
    max_total_bytes=None,
) -> dict:
    """Snapshot a RISC-V ELF binary and emit Coq files.

    init_pc is the ELF header's e_entry — the address the kernel jumps to.

    Args:
        binary_path: Path to the RISC-V ELF binary.
        out_dir: Directory to write <prefix>.v and bounded .hex chunk files.
        prefix: Name prefix for generated files and definitions.
        namespace: Rocq logical namespace for shard imports — must match
            the logical path of out_dir (e.g.
            'LinuxProcessSemantics.Examples.grep_args_ns' for
            theories/Examples/grep_args_ns/).
        max_total_bytes: whole-image byte cap, as for _parse_elf.

    Returns:
        Dict with keys: init_pc, num_segments, files (list of paths).

    Raises:
        ValueError: If the binary is not a valid RISC-V ELF.
        FileNotFoundError: If binary_path does not exist.
    """
    if not os.path.isfile(binary_path):
        raise FileNotFoundError("binary not found: %s" % binary_path)

    elf = _parse_elf(binary_path, max_total_bytes=max_total_bytes)

    # The kernel always transfers control to e_entry (load_elf_binary);
    # symbol-table entries like `_start` are advisory metadata that may be
    # stripped or diverge from the real entry point.
    init_pc = elf["entry"]

    out_path = os.path.join(out_dir, "%s.v" % prefix)
    _emit_coq(
        elf["segments"],
        init_pc,
        elf["phdrs"],
        out_path,
        prefix=prefix,
        namespace=namespace,
        module_name=module_name,
    )

    files = [out_path]
    for seg_idx, seg in enumerate(elf["segments"]):
        chunk_count = len(_hex_chunks(seg["hex_bytes"]))
        for chunk_idx in range(chunk_count):
            files.append(
                os.path.join(
                    out_dir,
                    _hex_file_name(prefix, seg_idx, chunk_idx, chunk_count),
                )
            )

    return {
        "init_pc": init_pc,
        "phdrs": elf["phdrs"],
        "num_segments": len(elf["segments"]),
        "files": files,
    }


# ---------------------------------------------------------------------------
# Verify mode — parse-check binaries with the same loader used to build snapshots
# ---------------------------------------------------------------------------


def _is_elf(path: str) -> bool:
    try:
        with open(path, "rb") as f:
            return f.read(4) == b"\x7fELF"
    except OSError:
        return False


def _iter_elf_binaries(paths):
    """Yield ELF files under each path (recursing into directories)."""
    for p in paths:
        if os.path.isdir(p):
            for root, _dirs, files in os.walk(p):
                for name in sorted(files):
                    fp = os.path.join(root, name)
                    if _is_elf(fp):
                        yield fp
        elif os.path.isfile(p) and _is_elf(p):
            yield p


def verify_paths(paths, max_total_bytes=None, max_total_bytes_source=None) -> int:
    """Parse every ELF under *paths* with the SAME loader used to build
    snapshots (`_parse_elf`), so a binary that can't be faithfully snapshotted is
    caught at build time instead of at snapshot time (where it wastes a whole
    run). Returns a process exit code: 0 if all snapshottable, 1 otherwise.

    The gate must verify against the SAME cap the snapshot will run under,
    so *max_total_bytes* is resolved here (flag, else environment, else the
    constant) and handed to every parse.  A cap this run cannot honour is
    an error about the cap, not a verdict on any binary, so it is resolved
    once up front rather than per file.

    The report below names the cap and *max_total_bytes_source*, the phrase
    for where it came from, on every run -- a pass as much as a failure.
    A gate that passes silently tells a reader nothing about WHAT it
    admitted, and a bare number would not distinguish an intended override
    from a stale variable left in the environment.  A caller handing in a
    cap directly may name its own source; otherwise the argument itself is
    named.
    """
    if max_total_bytes is None:
        max_total_bytes, resolved_source = resolve_max_total_bytes_with_source()
        if max_total_bytes_source is None:
            max_total_bytes_source = resolved_source
    else:
        max_total_bytes = _checked_cap(max_total_bytes, "max_total_bytes")
        if max_total_bytes_source is None:
            max_total_bytes_source = CAP_SOURCE_ARGUMENT

    binaries = list(_iter_elf_binaries(paths))
    failures = []
    for b in binaries:
        try:
            _parse_elf(b, max_total_bytes=max_total_bytes)
        except ValueError as e:
            failures.append((b, str(e)))
    for b, e in failures:
        print("elf_snapshot --verify: UNSNAPSHOTTABLE %s: %s" % (b, e), file=sys.stderr)
    print(
        "elf_snapshot --verify: whole-image cap 0x%x bytes, from %s"
        % (max_total_bytes, max_total_bytes_source),
        file=sys.stderr,
    )
    print(
        "elf_snapshot --verify: checked %d ELF binaries, %d unsnapshottable"
        % (len(binaries), len(failures)),
        file=sys.stderr,
    )
    if not binaries:
        print("elf_snapshot --verify: no ELF binaries found under %s" % list(paths), file=sys.stderr)
        return 1
    return 1 if failures else 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Static ELF snapshot for RISC-V binaries (no debugger needed).",
        epilog=(
            "Three other modes are dispatched before these options are parsed:\n"
            "  elf_snapshot.py --rebuild <MemImage.v> <out-binary>\n"
            "      write an ELF the kernel loads to exactly that snapshot's image\n"
            "      (rebuild_elf says what is recovered; the result is held to a\n"
            "      round trip through the parser above)\n"
            "  elf_snapshot.py --print-phdrs <binary>\n"
            "      print the binary's AT_PHDR/AT_PHENT/AT_PHNUM as `KEY VALUE`\n"
            "      lines (compare them with what a real execve gives)\n"
            "  elf_snapshot.py --verify <path>...\n"
            "      parse-check every ELF under the given files/directories and\n"
            "      write nothing (build gate; nonzero exit if any is rejected).\n"
            "      Its report names the cap it applied and which source set it.\n"
            "\n"
            "--max-total-bytes and the %s environment\n"
            "variable apply to those three modes too, so the build gate\n"
            "verifies against the same cap the snapshot will run under.\n"
            % MAX_TOTAL_BYTES_ENV
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("binary", help="Path to the RISC-V ELF binary")
    parser.add_argument(
        "out_path",
        nargs="?",
        default=None,
        help="Output path for <prefix>.v (default: theories/LinuxProcessSem/<prefix>.v)",
    )
    parser.add_argument(
        "--prefix",
        default="MemImage",
        help="Prefix for generated file and definition names (default: MemImage). "
        "Use SourceMemImage / TargetMemImage for two-binary setups.",
    )
    parser.add_argument(
        "--namespace",
        default=DEFAULT_NAMESPACE,
        help="Rocq logical namespace for shard imports (default: %s)"
        % DEFAULT_NAMESPACE,
    )
    parser.add_argument(
        "--module-name",
        default=None,
        help="If set, append a `Module <name> <: MemImage` wrapper exposing "
        "loaded_segments/init_pc/phdrs for the Equivalence functor "
        "(e.g. Source or Target).",
    )
    parser.add_argument(
        "--max-total-bytes",
        default=None,
        metavar="N",
        help="Whole-image byte cap for this run (decimal, or 0x hex). "
        "Outranks the %s environment variable, which outranks the built-in "
        "MAX_TOTAL_BYTES (%d). Refused above MAX_TOTAL_BYTES_CEILING (%d), "
        "the largest image this toolchain can coqchk."
        % (MAX_TOTAL_BYTES_ENV, MAX_TOTAL_BYTES, MAX_TOTAL_BYTES_CEILING),
    )
    parser.add_argument(
        "--include-stack",
        action="store_true",
        default=False,
        help="Include a synthetic stack segment (not yet implemented)",
    )
    args = parser.parse_args()

    try:
        max_total_bytes = resolve_max_total_bytes(args.max_total_bytes)
    except ValueError as e:
        print("elf_snapshot: %s" % e, file=sys.stderr)
        sys.exit(2)

    if args.out_path is None:
        args.out_path = "theories/LinuxProcessSem/%s.v" % args.prefix

    if os.path.isdir(args.out_path):
        args.out_path = os.path.join(args.out_path, "%s.v" % args.prefix)

    if not os.path.isfile(args.binary):
        print("elf_snapshot: binary not found: %s" % args.binary, file=sys.stderr)
        sys.exit(1)

    try:
        elf = _parse_elf(args.binary, max_total_bytes=max_total_bytes)
    except ValueError as e:
        print("elf_snapshot: %s" % e, file=sys.stderr)
        sys.exit(1)

    # init_pc is always e_entry: the kernel jumps there (load_elf_binary).
    init_pc = elf["entry"]

    _emit_coq(
        elf["segments"],
        init_pc,
        elf["phdrs"],
        args.out_path,
        prefix=args.prefix,
        namespace=args.namespace,
        module_name=args.module_name,
    )

    print(
        "elf_snapshot: wrote %d segments to %s (prefix=%s). init_pc=0x%x "
        "phdr=0x%x/%d/%d"
        % (
            len(elf["segments"]),
            args.out_path,
            args.prefix,
            init_pc,
            elf["phdrs"]["addr"],
            elf["phdrs"]["ent"],
            elf["phdrs"]["num"],
        ),
        file=sys.stderr,
    )


def print_phdrs(path: str, max_total_bytes=None) -> int:
    """`--print-phdrs <binary>`: report the auxv's AT_PHDR/AT_PHENT/AT_PHNUM
    for one ELF, as `KEY VALUE` lines, so they can be compared with the
    values a real process reads from its auxv."""
    try:
        elf = _parse_elf(path, max_total_bytes=max_total_bytes)
    except ValueError as e:
        print("elf_snapshot: %s" % e, file=sys.stderr)
        return 1
    ph = elf["phdrs"]
    print("AT_PHDR 0x%x" % ph["addr"])
    print("AT_PHENT %d" % ph["ent"])
    print("AT_PHNUM %d" % ph["num"])
    return 0


# ---------------------------------------------------------------------------
# --rebuild: from a snapshot back to an ELF that loads to it
# ---------------------------------------------------------------------------

# The program header types load_elf_binary READS from the file rather than
# maps (fs/binfmt_elf.c, v6.18.46): PT_INTERP's path, and PT_GNU_PROPERTY's
# note through parse_elf_properties -- both by elf_read at the header's
# file offset.  A rebuilt file can only carry the bytes some LOAD mapped,
# so one of these outside every LOAD's file extent cannot be reproduced
# and the rebuild refuses rather than hand the kernel zeros there.  Every
# other type (PT_NOTE, PT_GNU_STACK, PT_RISCV_ATTRIBUTES, PT_PHDR, PT_TLS)
# is either unread by the kernel or read from the mapped image.
PT_INTERP = 3
PT_GNU_PROPERTY = 0x6474E553

_SEG_DEF_RE = re.compile(
    r"Definition (?P<prefix>\w+?)_segment_(?P<idx>\d{3}) : Segment := \{\|\n"
    r"  seg_base  := 0x(?P<base>[0-9a-f]+)%N;\n"
    r"  seg_size  := 0x(?P<size>[0-9a-f]+)%N;\n"
    r'  seg_perms := "(?P<perms>[r-][w-][x-])";\n'
    r"  seg_bytes := \[(?P<bytes>[^\]]*)\]\n"
    r"\|\}\."
)
_DEP_RE = re.compile(r'From \S+ Extra Dependency "(?P<hex>[^"]+)" as (?P<dep>\w+)\.')
_READ_RE = re.compile(r"ReadFileString (?P<dep>\w+) As (?P<name>\w+)\.")
_INIT_PC_RE = re.compile(r"Definition \w+_init_pc : N := 0x(?P<pc>[0-9a-f]+)%N\.")
_PHDRS_RE = re.compile(
    r"Definition \w+_phdrs : PhdrInfo := \{\|\n"
    r"  ph_addr := 0x(?P<addr>[0-9a-f]+)%N;\n"
    r"  ph_ent  := (?P<ent>\d+)%N;\n"
    r"  ph_num  := (?P<num>\d+)%N\n"
    r"\|\}\."
)
_LOADED_RE = re.compile(
    r"Definition \w+_loaded_segments : list Segment :=\n  \[ (?P<names>[^\]]*)\n\]\."
)


def read_snapshot(v_path: str) -> dict:
    """Read a <prefix>.v this tool emitted, with its .hex sidecars, back into
    the dict _parse_elf returns: entry, segments (base, size, perms,
    hex_bytes) in loaded_segments order, phdrs (addr, ent, num).

    The file is matched against _emit_coq's own template line for line --
    the same tool wrote it -- so a hand-edited snapshot that no longer has
    that shape is refused rather than half-read.  Every segment's bytes are
    the concatenation of its chunk files, checked to be hex of exactly
    seg_size bytes: a sidecar that has drifted from its definition is the
    one thing a reader of the .v alone would never notice."""
    with open(v_path) as f:
        text = f.read()
    v_dir = os.path.dirname(os.path.abspath(v_path))
    deps = {m.group("dep"): m.group("hex") for m in _DEP_RE.finditer(text)}
    hex_of_name = {}
    for m in _READ_RE.finditer(text):
        if m.group("dep") not in deps:
            raise ValueError(
                "%s: ReadFileString %s names no Extra Dependency"
                % (v_path, m.group("dep"))
            )
        hex_of_name[m.group("name")] = deps[m.group("dep")]
    segs_by_name = {}
    for m in _SEG_DEF_RE.finditer(text):
        name = "%s_segment_%s" % (m.group("prefix"), m.group("idx"))
        size = int(m.group("size"), 16)
        hex_bytes = ""
        for byte_def in [b.strip() for b in m.group("bytes").split(";") if b.strip()]:
            if byte_def not in hex_of_name:
                raise ValueError(
                    "%s: segment %s reads %s, which no ReadFileString defines"
                    % (v_path, name, byte_def)
                )
            hex_path = os.path.join(v_dir, hex_of_name[byte_def])
            with open(hex_path) as f:
                chunk = f.read().strip()
            if len(chunk) % 2 or not re.fullmatch(r"[0-9a-f]*", chunk):
                raise ValueError("%s: not the lowercase hex of whole bytes" % hex_path)
            hex_bytes += chunk
        if len(hex_bytes) != 2 * size:
            raise ValueError(
                "%s: segment %s declares 0x%x bytes but its chunk files hold 0x%x"
                % (v_path, name, size, len(hex_bytes) // 2)
            )
        segs_by_name[name] = {
            "base": int(m.group("base"), 16),
            "size": size,
            "perms": m.group("perms"),
            "hex_bytes": hex_bytes,
        }
    loaded = _LOADED_RE.search(text)
    pc = _INIT_PC_RE.search(text)
    ph = _PHDRS_RE.search(text)
    if loaded is None or pc is None or ph is None:
        raise ValueError(
            "%s: not a snapshot this tool emitted (no loaded_segments, init_pc "
            "or phdrs definition in the template's shape)" % v_path
        )
    segments = []
    for name in [n.strip() for n in loaded.group("names").split(";")]:
        if name not in segs_by_name:
            raise ValueError("%s: loaded_segments names %s, which is not defined" % (v_path, name))
        segments.append(segs_by_name[name])
    return {
        "entry": int(pc.group("pc"), 16),
        "segments": segments,
        "phdrs": {
            "addr": int(ph.group("addr"), 16),
            "ent": int(ph.group("ent")),
            "num": int(ph.group("num")),
        },
    }


def _image_read(segments, addr: int, size: int) -> bytes:
    """The image's bytes at [addr, addr+size), which must lie inside one
    segment (segments never overlap, so one is the only possibility)."""
    for seg in segments:
        if seg["base"] <= addr and addr + size <= seg["base"] + seg["size"]:
            off = addr - seg["base"]
            return bytes.fromhex(seg["hex_bytes"][2 * off : 2 * (off + size)])
    raise ValueError(
        "[0x%x, 0x%x) is not inside any snapshotted segment" % (addr, addr + size)
    )


def rebuild_elf(snap: dict) -> bytes:
    """An ELF file the kernel loads to exactly the snapshot's image.

    A snapshot is the only committed record of an example's binary (the
    binaries are .gitignore'd, and the two toolchains that built them --
    a musl-cross-make gcc for the sources, zig for the targets -- may not
    both be at hand).  Everything load_elf_binary consumes is in the image, because
    the loader maps it: the ELF header at file offset 0 lies in the first
    page of the LOAD that starts there, the program header table is where
    AT_PHDR says (ph_addr, and _phdr_info is why that is exactly where the
    kernel found it), and every byte the kernel maps from the file is some
    segment's bytes (the mapping rule at _parse_elf's seg_data).  So the
    file is put back together from those: the table is read out of the
    image, the header out of the LOAD covering offset 0, and each LOAD's
    file extent is written at its p_offset from the image at its p_vaddr,
    page-rounded exactly as the kernel maps it, minus the tail past
    p_filesz of a bss-carrying segment, which the image holds as the
    kernel's zeros and the file held as something else.

    What is NOT recovered, and why it does not matter: whatever no LOAD
    mapped -- section headers, symbols and debug info come back only
    where they lie inside a mapped file page (the committed examples'
    section tables do), and e_shoff is copied verbatim whether or not it
    points inside this file; the kernel reads none of them, and neither
    does _parse_elf -- and the file bytes under a bss tail, which the
    image holds as _parse_elf's mapping rule reads them (the kernel's
    padzero, whose failure on a segment that is not writable elf_load
    ignores: fs/binfmt_elf.c, v6.18.46).  What cannot be recovered is
    refused: a PT_INTERP, which load_elf_binary reads from the file at
    its p_offset, or a PT_GNU_PROPERTY, which parse_elf_properties reads
    the same way on an architecture selecting CONFIG_ARCH_USE_GNU_PROPERTY
    (arm64 today, not riscv, so the refusal is fail-closed for a header
    the guest never reads), outside every LOAD's file extent.

    The check that makes this trustworthy is the round trip: the result is
    parsed by _parse_elf -- the same code that made the snapshot -- and
    must come back as the snapshot's entry, segments and phdrs, byte for
    byte.  A file that passes loads to the snapshot's image by the
    definition of the snapshot, whatever toolchain made the original."""
    segments = snap["segments"]
    ph = snap["phdrs"]
    if ph["ent"] != PHDR_ENTSIZE:
        raise ValueError("ph_ent %d is not the size of an ELF64 program header" % ph["ent"])
    if ph["num"] * PHDR_ENTSIZE > PHDR_TABLE_MAX:
        raise ValueError("ph_num %d: a program header table larger than %d bytes"
                         % (ph["num"], PHDR_TABLE_MAX))
    table = _image_read(segments, ph["addr"], ph["ent"] * ph["num"])
    phdrs = []
    for i in range(ph["num"]):
        off = i * ph["ent"]
        phdrs.append({
            "type": struct.unpack_from("<I", table, off)[0],
            "offset": struct.unpack_from("<Q", table, off + 8)[0],
            "vaddr": struct.unpack_from("<Q", table, off + 16)[0],
            "filesz": struct.unpack_from("<Q", table, off + 32)[0],
            "memsz": struct.unpack_from("<Q", table, off + 40)[0],
        })
    loads = [p for p in phdrs if p["type"] == PT_LOAD and p["memsz"] > 0]

    def covering(offset: int, size: int):
        return [p for p in loads
                if p["offset"] <= offset and offset + size <= p["offset"] + p["filesz"]]

    # The ELF header: file offset 0, inside a LOAD's file extent, and so at
    # that LOAD's p_vaddr - p_offset in the image (p_offset is 0 there).
    hdr_loads = covering(0, 64)
    if not hdr_loads:
        raise ValueError(
            "no PT_LOAD's file extent covers the ELF header at file offset 0, "
            "so the snapshot does not carry the header the kernel reads"
        )
    hdr_load = hdr_loads[-1]
    ehdr = _image_read(segments, hdr_load["vaddr"] - hdr_load["offset"], 64)
    if ehdr[:4] != EI_MAG:
        raise ValueError("the bytes mapped from file offset 0 are not an ELF header")
    e_phoff = struct.unpack_from("<Q", ehdr, 32)[0]
    e_phentsize = struct.unpack_from("<H", ehdr, 54)[0]
    e_phnum = struct.unpack_from("<H", ehdr, 56)[0]
    if (e_phentsize, e_phnum) != (ph["ent"], ph["num"]):
        raise ValueError(
            "the header says e_phentsize=%d e_phnum=%d, the snapshot's phdrs say %d/%d"
            % (e_phentsize, e_phnum, ph["ent"], ph["num"])
        )
    for p in phdrs:
        if p["type"] in (PT_INTERP, PT_GNU_PROPERTY) and p["filesz"] > 0 \
                and not covering(p["offset"], p["filesz"]):
            raise ValueError(
                "program header of type 0x%x has file extent [0x%x, 0x%x) outside "
                "every LOAD: the kernel reads it from the file and the snapshot "
                "does not carry it" % (p["type"], p["offset"], p["offset"] + p["filesz"])
            )

    # Each LOAD's mapped file bytes, at the file offsets the kernel maps
    # them from.  Where two LOADs map the same file page the image holds
    # the same bytes for both, so a byte written twice must agree; a
    # disagreement is a snapshot no single file loads to.
    out = bytearray()
    written = bytearray()   # 1 where a byte of out has been placed
    for p in loads:
        if p["filesz"] == 0:
            continue
        delta = p["vaddr"] % PAGE_SIZE
        file_lo = p["offset"] - delta
        span = ((delta + p["filesz"] + PAGE_SIZE - 1) // PAGE_SIZE) * PAGE_SIZE
        if p["memsz"] > p["filesz"]:
            span = delta + p["filesz"]
        chunk = _image_read(segments, p["vaddr"] - delta, span)
        end = file_lo + span
        if end > len(out):
            out.extend(b"\x00" * (end - len(out)))
            written.extend(b"\x00" * (end - len(written)))
        for k, b in enumerate(chunk):
            at = file_lo + k
            if written[at] and out[at] != b:
                raise ValueError(
                    "file offset 0x%x is mapped by two LOADs with different bytes" % at
                )
            out[at] = b
            written[at] = 1
    if e_phoff + e_phnum * e_phentsize > len(out):
        raise ValueError("the program header table runs past the rebuilt file")
    return bytes(out)


def rebuild(v_path: str, out_path: str, max_total_bytes=None) -> int:
    """`--rebuild <MemImage.v> <out-binary>`: write the ELF rebuild_elf
    recovers, then hold it to the round trip -- _parse_elf of the written
    file must be the snapshot -- and delete the file if it is not."""
    try:
        snap = read_snapshot(v_path)
        data = rebuild_elf(snap)
    except (OSError, ValueError) as e:
        print("elf_snapshot: %s" % e, file=sys.stderr)
        return 1
    with open(out_path, "wb") as f:
        f.write(data)
    os.chmod(out_path, 0o755)
    try:
        back = _parse_elf(out_path, max_total_bytes=max_total_bytes)
    except ValueError as e:
        os.unlink(out_path)
        print("elf_snapshot: the rebuilt ELF does not parse: %s" % e, file=sys.stderr)
        return 1
    if back != snap:
        os.unlink(out_path)
        print(
            "elf_snapshot: the rebuilt ELF does not load to the snapshot's image "
            "(entry, segments or phdrs differ); refusing to keep it", file=sys.stderr,
        )
        return 1
    print(
        "elf_snapshot: rebuilt %s from %s: %d segments, entry 0x%x, %d bytes"
        % (out_path, v_path, len(snap["segments"]), snap["entry"], len(data)),
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    # The three alternate modes are dispatched here, before argparse runs,
    # so each one lifts out the cap override by hand and honours it exactly
    # as the default mode does.
    _argv = sys.argv[1:]
    _mode = next(
        (m for m in ("--rebuild", "--print-phdrs", "--verify") if m in _argv),
        None,
    )
    if _mode is not None:
        try:
            _rest, _flag = _take_max_total_bytes_flag(
                [a for a in _argv if a != _mode]
            )
            _cap, _cap_source = resolve_max_total_bytes_with_source(_flag)
        except ValueError as _e:
            print("elf_snapshot: %s" % _e, file=sys.stderr)
            sys.exit(2)

        # `--rebuild <MemImage.v> <out-binary>`: the snapshot back to an ELF.
        if _mode == "--rebuild":
            if len(_rest) != 2:
                print("usage: elf_snapshot.py --rebuild <MemImage.v> <out-binary>", file=sys.stderr)
                sys.exit(2)
            sys.exit(rebuild(_rest[0], _rest[1], max_total_bytes=_cap))

        # `--print-phdrs <binary>`: report just the auxv phdr triple.
        if _mode == "--print-phdrs":
            if len(_rest) != 1:
                print("usage: elf_snapshot.py --print-phdrs <binary>", file=sys.stderr)
                sys.exit(2)
            sys.exit(print_phdrs(_rest[0], max_total_bytes=_cap))

        # `--verify <path>...`: parse-check every ELF under the given
        # paths/dirs instead of snapshotting one binary (the build gate
        # uses this).
        sys.exit(
            verify_paths(
                _rest,
                max_total_bytes=_cap,
                max_total_bytes_source=_cap_source,
            )
        )
    main()
