#!/usr/bin/env python3
"""Regression tests for faithful ELF snapshot generation.

The Rocq trusted spec enforces per-segment ELF r/w/x page permissions, so the
snapshot tool MUST derive each Segment's perms from that segment's own
PT_LOAD p_flags (never a blanket value copied across segments).  This test
synthesizes a minimal 64-bit little-endian RISC-V ELF with four PT_LOAD
segments carrying four DISTINCT p_flags (r-x, rw-, r--, ---), then checks:

  1. _parse_elf returns each segment with exactly its own perms string.
  2. _emit_coq / snapshot_binary writes one `seg_perms := "..."` per segment
     with the correct distinct value, and the .hex byte files match the
     segment contents (including p_memsz > p_filesz zero-padding).
  3. The auxv's AT_PHDR/AT_PHENT/AT_PHNUM are derived as the kernel does,
     a PT_TLS segment is accepted (thread-local storage), and an unmapped
     or unreadable program header table is rejected.

It also covers bounded multi-string segment payloads and the loader's other
fail-closed rejections, each of which keeps
an unfaithful or VACUOUS image out of the development: init_pc comes from
e_entry, whole images over the total cap and truncated/overlapping segments
are refused, and extents are page-rounded and read as the kernel's whole-page
FILE mapping (head/tail
slack holds the neighboring file bytes; only bss is zeroed), a segment whose
p_vaddr and p_offset are not congruent mod the page size is refused (the
kernel cannot exec it), a w+x (RWX) segment is recorded with its exact perms, and an
ELF with no mapped PT_LOAD segment at all is refused (see the group comments
below for why each one matters).

No toolchain or pytest needed:
    python3 tools/test_elf_snapshot.py
Exits non-zero on any failure.
"""

import os
import re
import struct
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import elf_snapshot  # noqa: E402
from elf_snapshot import _parse_elf, snapshot_binary  # noqa: E402
from gen_fd_lemmas import read_text_words  # noqa: E402

EHDR_SIZE = 64
PHENTSIZE = 56
ENTRY = 0x10000

# (p_flags, expected perms, vaddr, file contents, memsz)
# Segment 1 exercises p_memsz > p_filesz zero-padding: 4 file bytes, 10 memsz.
# Every synthesized ELF also gets a trailing PT_LOAD mapping the ELF header
# and program header table, as real toolchain output does (the first LOAD
# of a real binary starts at file offset 0).  The loader needs the table
# mapped to publish AT_PHDR at all.  It is appended LAST in the phdr table
# -- segment order in the parse result is phdr order -- so the per-segment
# assertions below keep indexing SEG_SPECS from 0.
HDR_VADDR = 0x8000
HDR_PERMS = "r--"

SEG_SPECS = [
    (5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),      # PF_R|PF_X
    (6, "rw-", 0x20000, b"\xde\xad\xbe\xef", 10),        # PF_R|PF_W, zero-pad
    (4, "r--", 0x30000, b"RODATA", None),                # PF_R
    (0, "---", 0x40000, b"ZZ", None),                    # no flags
]


def build_elf(seg_specs, tls_extra=False, start_symbol_at=None,
              map_phdrs=True, tls_vaddr=0x50000, hdr_maps=None):
    """Build a minimal 64-bit LE RISC-V ELF with the given PT_LOAD segments.

    Field offsets match exactly what _parse_elf reads: EI_MAG/EI_CLASS/EI_DATA,
    e_machine@18, e_entry@24, e_phoff@32, e_phentsize@54, e_phnum@56.

    When ``start_symbol_at`` is given, a .symtab/.strtab section pair is
    appended defining a ``_start`` symbol at that address (used to prove the
    loader takes init_pc from e_entry, never from the symbol table).

    ``hdr_maps`` replaces the default single phdr-mapping LOAD segment with an
    explicit list of ``(p_flags, p_offset, p_filesz, p_vaddr)`` LOAD segments,
    appended in that order.  It is what lets a fixture control the FILE extent
    of the segment the program header table lands in: a nonzero ``p_offset``,
    an unreadable one, or several segments that all cover ``e_phoff``.
    """
    if hdr_maps is not None:
        n_hdr = len(hdr_maps)
    else:
        n_hdr = 1 if map_phdrs else 0
    phnum = len(seg_specs) + (1 if tls_extra else 0) + n_hdr
    phoff = EHDR_SIZE
    data_off = phoff + phnum * PHENTSIZE

    ehdr = bytearray(EHDR_SIZE)
    ehdr[0:4] = b"\x7fELF"
    ehdr[4] = 2  # ELFCLASS64
    ehdr[5] = 1  # ELFDATA2LSB
    ehdr[6] = 1  # EV_CURRENT (unread, cosmetic)
    struct.pack_into("<H", ehdr, 16, 2)        # e_type = ET_EXEC (unread)
    struct.pack_into("<H", ehdr, 18, 243)      # e_machine = EM_RISCV
    struct.pack_into("<I", ehdr, 20, 1)        # e_version (unread)
    struct.pack_into("<Q", ehdr, 24, ENTRY)    # e_entry
    struct.pack_into("<Q", ehdr, 32, phoff)    # e_phoff
    struct.pack_into("<Q", ehdr, 40, 0)        # e_shoff = 0 (no sections)
    struct.pack_into("<H", ehdr, 52, EHDR_SIZE)   # e_ehsize (unread)
    struct.pack_into("<H", ehdr, 54, PHENTSIZE)   # e_phentsize
    struct.pack_into("<H", ehdr, 56, phnum)       # e_phnum
    # e_shentsize/e_shnum/e_shstrndx stay 0.

    phdrs = bytearray()
    payload = bytearray()
    off = data_off
    for p_flags, _perms, vaddr, contents, memsz in seg_specs:
        filesz = len(contents)
        if memsz is None:
            memsz = filesz
        # A file-backed segment is only kernel-loadable when p_offset and
        # p_vaddr are congruent mod the page size (elf_map hands vm_mmap
        # the page-rounded file offset), and the loader rejects anything
        # else, so lay the payload out the way a real linker does: pad the
        # file up to the next congruent offset.  Zero-filesz segments map
        # no file bytes and need no padding.
        if filesz:
            pad = (vaddr - off) % PAGE
            payload += b"\x00" * pad
            off += pad
        phdrs += struct.pack(
            "<IIQQQQQQ",
            1,          # p_type = PT_LOAD
            p_flags,    # p_flags
            off,        # p_offset
            vaddr,      # p_vaddr
            vaddr,      # p_paddr
            filesz,     # p_filesz
            memsz,      # p_memsz
            1,          # p_align
        )
        payload += contents
        off += filesz

    if tls_extra:
        # PT_TLS overlaying whichever LOAD segment covers tls_vaddr, as a
        # real .tdata/.tbss does.
        phdrs += struct.pack(
            "<IIQQQQQQ", 7, 4, off, tls_vaddr, tls_vaddr, 8, 8, 8
        )

    if hdr_maps is not None:
        for p_flags, p_offset, p_filesz, p_vaddr in hdr_maps:
            phdrs += struct.pack(
                "<IIQQQQQQ",
                1,          # p_type = PT_LOAD
                p_flags,
                p_offset,
                p_vaddr,
                p_vaddr,
                p_filesz,
                p_filesz,   # p_memsz
                1,
            )
    elif map_phdrs:
        phdrs += struct.pack(
            "<IIQQQQQQ",
            1,          # p_type = PT_LOAD
            4,          # PF_R
            0,          # p_offset: from the very start of the file
            HDR_VADDR,  # p_vaddr
            HDR_VADDR,
            data_off,   # p_filesz: ELF header + the whole phdr table
            data_off,   # p_memsz
            1,
        )

    tail = bytearray()
    if start_symbol_at is not None:
        # Append: strtab bytes, symtab entries, then 3 section headers
        # (null, SHT_SYMTAB linked to strtab, SHT_STRTAB).
        strtab = b"\x00_start\x00"
        strtab_off = off
        symtab_off = strtab_off + len(strtab)
        # Elf64_Sym: st_name(4) st_info(1) st_other(1) st_shndx(2)
        #            st_value(8) st_size(8)
        symtab = struct.pack("<IBBHQQ", 0, 0, 0, 0, 0, 0)  # null symbol
        symtab += struct.pack(
            "<IBBHQQ", 1, 2, 0, 1, start_symbol_at, 0  # STT_FUNC "_start"
        )
        shoff = symtab_off + len(symtab)

        def shdr(sh_type, sh_offset, sh_size, sh_link, sh_entsize):
            # Elf64_Shdr: name(4) type(4) flags(8) addr(8) offset(8)
            #             size(8) link(4) info(4) addralign(8) entsize(8)
            return struct.pack(
                "<IIQQQQIIQQ", 0, sh_type, 0, 0, sh_offset, sh_size,
                sh_link, 0, 0, sh_entsize,
            )

        shdrs = shdr(0, 0, 0, 0, 0)                              # null
        shdrs += shdr(2, symtab_off, len(symtab), 2, 24)         # SHT_SYMTAB
        shdrs += shdr(3, strtab_off, len(strtab), 0, 0)          # SHT_STRTAB
        tail = bytearray(strtab) + symtab + shdrs
        struct.pack_into("<Q", ehdr, 40, shoff)  # e_shoff
        struct.pack_into("<H", ehdr, 58, 64)     # e_shentsize
        struct.pack_into("<H", ehdr, 60, 3)      # e_shnum
        struct.pack_into("<H", ehdr, 62, 0)      # e_shstrndx

    return bytes(ehdr) + bytes(phdrs) + bytes(payload) + bytes(tail)


PAGE = 4096


def load_phdrs(data):
    """The PT_LOAD headers of a built ELF, parsed independently of
    _parse_elf, so expected bytes can be computed from the phdr table a
    fixture actually carries (build_elf inserts congruence padding, so a
    spec's file offset is not knowable without reading it back)."""
    e_phoff = struct.unpack_from("<Q", data, 32)[0]
    e_phentsize = struct.unpack_from("<H", data, 54)[0]
    e_phnum = struct.unpack_from("<H", data, 56)[0]
    out = []
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        if struct.unpack_from("<I", data, off)[0] != 1:  # PT_LOAD
            continue
        out.append(
            {
                "offset": struct.unpack_from("<Q", data, off + 8)[0],
                "vaddr": struct.unpack_from("<Q", data, off + 16)[0],
                "filesz": struct.unpack_from("<Q", data, off + 32)[0],
                "memsz": struct.unpack_from("<Q", data, off + 40)[0],
            }
        )
    return out


def expected_segment(data, ph):
    """Expected (page-rounded base, mapped bytes) for a PT_LOAD segment,
    per the kernel's elf_load rule: the extent [round_down(vaddr),
    round_up(vaddr+memsz)) is a whole-page FILE mapping of
    [offset - (vaddr % PAGE), round_up thereof + filesz), zero past EOF;
    a bss-carrying segment (memsz > filesz) is zeroed past vaddr+filesz;
    pages beyond the file mapping are anonymous zeros."""
    vaddr, offset = ph["vaddr"], ph["offset"]
    filesz, memsz = ph["filesz"], ph["memsz"]
    ext_lo = vaddr - vaddr % PAGE
    ext_hi = (vaddr + memsz + PAGE - 1) // PAGE * PAGE
    ext_size = ext_hi - ext_lo
    delta = vaddr - ext_lo
    if filesz == 0:
        return ext_lo, b"\x00" * ext_size
    file_lo = offset - delta
    file_span = (delta + filesz + PAGE - 1) // PAGE * PAGE
    mapped = data[file_lo : file_lo + file_span]
    mapped += b"\x00" * (file_span - len(mapped))
    if memsz > filesz:
        mapped = mapped[: delta + filesz]
    return ext_lo, mapped + b"\x00" * (ext_size - len(mapped))


def main():
    groups_passed = []

    with tempfile.TemporaryDirectory() as tmp:
        elf_path = os.path.join(tmp, "fake_riscv.elf")
        elf_data = build_elf(SEG_SPECS)
        with open(elf_path, "wb") as f:
            f.write(elf_data)
        spec_phs = load_phdrs(elf_data)  # phdr order == SEG_SPECS order

        # -- Group 1: _parse_elf yields per-segment perms, not a blanket copy.
        parsed = _parse_elf(elf_path)
        assert parsed["entry"] == ENTRY, (
            "entry mismatch: got 0x%x, want 0x%x" % (parsed["entry"], ENTRY)
        )
        segs = parsed["segments"]
        assert len(segs) == len(SEG_SPECS) + 1, (
            "expected %d segments (SEG_SPECS + the phdr-mapping one), got %d"
            % (len(SEG_SPECS) + 1, len(segs))
        )
        hdr_seg = segs[-1]
        assert (hdr_seg["base"], hdr_seg["perms"]) == (HDR_VADDR, HDR_PERMS), (
            "trailing phdr-mapping segment is not [0x%x, %r]: %r"
            % (HDR_VADDR, HDR_PERMS, hdr_seg)
        )
        segs = segs[: len(SEG_SPECS)]
        for i, ((_fl, want_perms, vaddr, contents, memsz), seg) in enumerate(
            zip(SEG_SPECS, segs)
        ):
            want_base, want_bytes = expected_segment(elf_data, spec_phs[i])
            assert seg["base"] == want_base, (
                "seg %d: base 0x%x != expected page-rounded base 0x%x"
                % (i, seg["base"], want_base)
            )
            assert seg["perms"] == want_perms, (
                "seg %d (vaddr=0x%x): perms %r != expected %r -- "
                "per-segment p_flags not honored"
                % (i, vaddr, seg["perms"], want_perms)
            )
            assert seg["size"] == len(want_bytes), (
                "seg %d: size %d != page-rounded extent %d"
                % (i, seg["size"], len(want_bytes))
            )
            assert seg["size"] % PAGE == 0, (
                "seg %d: size 0x%x is not page-rounded" % (i, seg["size"])
            )
            assert seg["hex_bytes"] == want_bytes.hex(), (
                "seg %d: hex_bytes mismatch:\n  got  %s\n  want %s"
                % (i, seg["hex_bytes"], want_bytes.hex())
            )
        # Blanket-copy detector: all four perms strings must be distinct.
        perms_list = [s["perms"] for s in segs]
        assert len(set(perms_list)) == len(SEG_SPECS), (
            "perms are not distinct per segment (blanket copy?): %r" % perms_list
        )
        groups_passed.append("parse_elf per-segment perms")

        # -- Group 2: emitted Coq + hex files carry per-segment perms/bytes.
        out_dir = os.path.join(tmp, "out")
        os.makedirs(out_dir)
        result = snapshot_binary(elf_path, out_dir, prefix="MemImage")
        assert result["num_segments"] == len(SEG_SPECS) + 1, (
            "snapshot_binary emitted %d segments, want %d"
            % (result["num_segments"], len(SEG_SPECS) + 1)
        )
        assert result["init_pc"] == ENTRY, (
            "init_pc 0x%x != e_entry 0x%x" % (result["init_pc"], ENTRY)
        )
        v_path = os.path.join(out_dir, "MemImage.v")
        assert os.path.isfile(v_path), "missing emitted file %s" % v_path
        with open(v_path) as f:
            v_text = f.read()

        assert (
            "From LinuxProcessSemantics.LinuxProcessSem Require Import "
            "MemImageType."
            in v_text
        ), "emitted Rocq import does not use the LinuxProcessSem top-level module"
        old_module_name = "Task" + "Specification"
        assert old_module_name not in v_text, (
            "emitted Rocq file still refers to the old specification module"
        )

        emitted_perms = re.findall(r'seg_perms := "([^"]*)";', v_text)
        want_perms_list = [spec[1] for spec in SEG_SPECS] + [HDR_PERMS]
        assert emitted_perms == want_perms_list, (
            "emitted seg_perms %r != expected %r (order = segment order)"
            % (emitted_perms, want_perms_list)
        )
        assert "as MemImage_seg_dep_000." in v_text
        assert "As MemImage_seg_bytes_000." in v_text
        assert "MemImage_seg_dep_000_000" not in v_text
        assert "MemImage_seg_bytes_000_000" not in v_text
        assert "seg_bytes := [MemImage_seg_bytes_000]" in v_text
        # Each perms string must sit inside its own segment Definition,
        # matched to the right base address.
        for i, (_fl, want_perms, vaddr, _c, _m) in enumerate(SEG_SPECS):
            pat = (
                r"Definition MemImage_segment_%03d : Segment := \{\|\s*"
                r"seg_base\s+:= 0x%x%%N;\s*"
                r"seg_size\s+:= 0x[0-9a-f]+%%N;\s*"
                r'seg_perms := "%s";' % (i, vaddr, re.escape(want_perms))
            )
            assert re.search(pat, v_text), (
                "segment %d (vaddr=0x%x): .v text does not pair base with "
                "perms %r:\n%s" % (i, vaddr, want_perms, v_text)
            )
        for i, (_fl, _p, _v, contents, memsz) in enumerate(SEG_SPECS):
            hex_path = os.path.join(out_dir, "MemImage_seg_%03d.hex" % i)
            assert os.path.isfile(hex_path), "missing hex file %s" % hex_path
            with open(hex_path) as f:
                hex_text = f.read()
            want_hex = expected_segment(elf_data, spec_phs[i])[1].hex()
            assert hex_text == want_hex, (
                "hex file %s mismatch:\n  got  %s\n  want %s"
                % (hex_path, hex_text, want_hex)
            )
        groups_passed.append("emit_coq per-segment perms + hex bytes")

        # -- Group 3: the auxv's program header table (AT_PHDR/AT_PHENT/
        # AT_PHNUM), which is what a static libc walks to find PT_TLS
        # before laying out thread-local storage.
        #
        # AT_PHDR is the address the table gets by virtue of lying inside a
        # mapped LOAD segment: p_vaddr + (e_phoff - p_offset) for the
        # segment whose file extent covers e_phoff -- here the trailing
        # phdr-mapping segment, at file offset 0 and vaddr HDR_VADDR.
        want_phnum = len(SEG_SPECS) + 1
        phdrs = parsed["phdrs"]
        assert phdrs == {
            "addr": HDR_VADDR + EHDR_SIZE,
            "ent": PHENTSIZE,
            "num": want_phnum,
        }, "phdr info %r is not the kernel's derivation" % (phdrs,)
        assert (
            "Definition MemImage_phdrs : PhdrInfo := {|" in v_text
            and ("ph_addr := 0x%x%%N;" % (HDR_VADDR + EHDR_SIZE)) in v_text
            and ("ph_ent  := %d%%N;" % PHENTSIZE) in v_text
            and ("ph_num  := %d%%N" % want_phnum) in v_text
        ), "emitted MemImage.v does not carry the phdr record:\n%s" % v_text

        # The `- p_offset` term is the whole difference between the kernel's
        # per-segment rule and a naive `p_vaddr + e_phoff`, and every fixture
        # above (like every real toolchain link) has the table in a segment at
        # file offset 0, where the two agree.  Pin it with a phdr-covering
        # segment at a NONZERO p_offset: a first LOAD mapping only the ELF
        # header (so it does not cover e_phoff), then a second one starting
        # exactly at e_phoff.
        off_specs = [(5, "r-x", 0x10000, b"\x13\x05\x00\x00", None)]
        off_phnum = len(off_specs) + 2
        off_data_off = EHDR_SIZE + off_phnum * PHENTSIZE
        off_path = os.path.join(tmp, "fake_phdr_offset.elf")
        with open(off_path, "wb") as f:
            f.write(build_elf(off_specs, hdr_maps=[
                # ELF header only: p_offset 0, extent ends AT e_phoff.
                (4, 0, EHDR_SIZE, 0x8000),
                # The phdr table proper, at file offset e_phoff; the vaddr
                # must be offset-congruent mod the page size for the
                # segment to be kernel-loadable at all.
                (4, EHDR_SIZE, off_data_off - EHDR_SIZE, 0x9000 + EHDR_SIZE),
            ]))
        off_phdrs = _parse_elf(off_path)["phdrs"]
        assert off_phdrs["addr"] == 0x9000 + EHDR_SIZE, (
            "AT_PHDR for a phdr table in a segment at p_offset=0x%x is 0x%x, "
            "expected p_vaddr + (e_phoff - p_offset) = 0x%x"
            % (EHDR_SIZE, off_phdrs["addr"], 0x9000 + EHDR_SIZE)
        )
        assert off_phdrs["addr"] != 0x9000 + 2 * EHDR_SIZE, (
            "AT_PHDR looks like the naive p_vaddr + e_phoff: the "
            "'- p_offset' term is missing"
        )
        assert off_phdrs["num"] == off_phnum, (
            "AT_PHNUM %d != e_phnum %d" % (off_phdrs["num"], off_phnum)
        )

        # Several PT_LOADs can cover e_phoff (only a crafted ELF does, since
        # the overlap check compares mapped extents and not file extents).  The
        # kernel's loop in load_elf_binary has no `break`, so the LAST covering
        # segment sets phdr_addr; taking the first would publish an AT_PHDR a
        # real execve never publishes, and musl derives its load base from
        # AT_PHDR before reading the PT_TLS init image through it.
        dup_specs = [(5, "r-x", 0x10000, b"\x13\x05\x00\x00", None)]
        dup_phnum = len(dup_specs) + 2
        dup_data_off = EHDR_SIZE + dup_phnum * PHENTSIZE
        dup_path = os.path.join(tmp, "fake_phdr_two_covering.elf")
        with open(dup_path, "wb") as f:
            f.write(build_elf(dup_specs, hdr_maps=[
                (4, 0, dup_data_off, 0x8000),
                (4, 0, dup_data_off, 0x9000),  # same file extent, later vaddr
            ]))
        dup_phdrs = _parse_elf(dup_path)["phdrs"]
        assert dup_phdrs["addr"] == 0x9000 + EHDR_SIZE, (
            "with two PT_LOADs covering e_phoff, AT_PHDR is 0x%x; the kernel "
            "keeps scanning and the LAST one wins, so it must be 0x%x"
            % (dup_phdrs["addr"], 0x9000 + EHDR_SIZE)
        )

        # The phdr table's mapped range must be wholly READABLE, not merely
        # mapped: the model publishes AT_PHDR into it and libc's TLS setup
        # walks exactly that range, while the model's loads are gated on
        # seg_readable.  A phdr-covering segment without PF_R is rejected.
        noread_specs = [(5, "r-x", 0x10000, b"\x13\x05\x00\x00", None)]
        noread_data_off = EHDR_SIZE + (len(noread_specs) + 1) * PHENTSIZE
        noread_path = os.path.join(tmp, "fake_phdr_unreadable.elf")
        with open(noread_path, "wb") as f:
            f.write(build_elf(noread_specs, hdr_maps=[
                (1, 0, noread_data_off, 0x8000),  # PF_X only: "--x"
            ]))
        try:
            _parse_elf(noread_path)
        except ValueError as e:
            assert "readable LOAD segment" in str(e), (
                "unreadable-phdr-table rejection has the wrong message: %s" % e
            )
        else:
            raise AssertionError(
                "a phdr table mapped by a non-readable (--x) LOAD segment was "
                "accepted; the model would publish an AT_PHDR the process "
                "cannot read"
            )
        groups_passed.append("auxv AT_PHDR/AT_PHENT/AT_PHNUM derivation")

        # A PT_TLS segment is ACCEPTED: its bytes overlay a LOAD
        # segment (real .tdata sits in the writable one), and what libc
        # needs beyond them -- the ability to find the header -- is the
        # AT_PHDR above.
        tls_path = os.path.join(tmp, "fake_tls.elf")
        with open(tls_path, "wb") as f:
            f.write(build_elf(SEG_SPECS, tls_extra=True, tls_vaddr=0x20000))
        tls_parsed = _parse_elf(tls_path)
        assert tls_parsed["phdrs"]["num"] == len(SEG_SPECS) + 2, (
            "PT_TLS binary's AT_PHNUM does not count every program header: %r"
            % (tls_parsed["phdrs"],)
        )
        # PT_TLS maps no segment of its own.
        assert len(tls_parsed["segments"]) == len(SEG_SPECS) + 1, (
            "PT_TLS should not add a segment: %d segments"
            % len(tls_parsed["segments"])
        )

        # ...but a PT_TLS whose initialization image is NOT inside a
        # readable LOAD segment is rejected: __copy_tls memcpy's p_filesz
        # bytes out of it on every startup, and the snapshot would not have
        # them.
        tls_bad = os.path.join(tmp, "fake_tls_unmapped.elf")
        with open(tls_bad, "wb") as f:
            f.write(build_elf(SEG_SPECS, tls_extra=True, tls_vaddr=0x900000))
        try:
            _parse_elf(tls_bad)
        except ValueError as e:
            assert "PT_TLS initialization image" in str(e), (
                "unmapped PT_TLS rejection has the wrong message: %s" % e
            )
        else:
            raise AssertionError(
                "PT_TLS outside every readable segment was accepted; "
                "expected ValueError"
            )

        # An UNMAPPED program header table is rejected: with no AT_PHDR to
        # publish, libc startup could not find PT_TLS at all.
        nophdr = os.path.join(tmp, "fake_unmapped_phdrs.elf")
        with open(nophdr, "wb") as f:
            f.write(build_elf(SEG_SPECS, map_phdrs=False))
        try:
            _parse_elf(nophdr)
        except ValueError as e:
            assert "AT_PHDR" in str(e), (
                "unmapped-phdr-table rejection lacks 'AT_PHDR': %s" % e
            )
        else:
            raise AssertionError(
                "ELF with an unmapped program header table was accepted; "
                "expected ValueError"
            )
        groups_passed.append("PT_TLS accepted; unmapped phdrs/TLS rejected")

        # A program header table with entries of any size other than 56
        # bytes is rejected: Linux's execve refuses it (load_elf_phdrs).
        # Re-lay a valid table in place with 64-byte entries, inside a
        # header mapping large enough to still cover it.
        phent = bytearray(build_elf(SEG_SPECS[:1],
                                    hdr_maps=[(4, 0, 0x200, HDR_VADDR)]))
        ph_off = struct.unpack_from("<Q", phent, 32)[0]
        ph_num = struct.unpack_from("<H", phent, 56)[0]
        entries = [bytes(phent[ph_off + PHENTSIZE * i:
                               ph_off + PHENTSIZE * (i + 1)])
                   for i in range(ph_num)]
        phent[ph_off:ph_off + 64 * ph_num] = b"".join(
            e + b"\x00" * 8 for e in entries)
        struct.pack_into("<H", phent, 54, 64)
        phent_path = os.path.join(tmp, "fake_phentsize64.elf")
        with open(phent_path, "wb") as f:
            f.write(phent)
        try:
            _parse_elf(phent_path)
        except ValueError as e:
            assert "e_phentsize=64" in str(e), (
                "e_phentsize rejection has the wrong message: %s" % e
            )
        else:
            raise AssertionError(
                "ELF with e_phentsize=64 was accepted; expected ValueError"
            )
        groups_passed.append("e_phentsize other than 56 rejected")

        # A program header table over 64 KiB is rejected too (load_elf_phdrs
        # again): 1171 entries of 56 bytes is the first count over the limit.
        # Both the parser and rebuild_elf refuse it.
        bigtab = bytearray(build_elf(SEG_SPECS[:1]))
        struct.pack_into("<H", bigtab, 56, 1171)
        bigtab_path = os.path.join(tmp, "fake_phnum1171.elf")
        with open(bigtab_path, "wb") as f:
            f.write(bigtab)
        try:
            _parse_elf(bigtab_path)
        except ValueError as e:
            assert "e_phnum=1171" in str(e), (
                "oversized phdr table rejection has the wrong message: %s" % e
            )
        else:
            raise AssertionError(
                "ELF with a 65576-byte phdr table was accepted; expected ValueError"
            )
        base_path = os.path.join(tmp, "fake_bigtab_base.elf")
        with open(base_path, "wb") as f:
            f.write(build_elf(SEG_SPECS[:1],
                              hdr_maps=[(4, 0, 0x200, HDR_VADDR)]))
        snap = _parse_elf(base_path)
        snap["phdrs"] = dict(snap["phdrs"], num=1171)
        try:
            elf_snapshot.rebuild_elf(snap)
        except ValueError as e:
            assert "ph_num 1171" in str(e), (
                "rebuild_elf oversized-table rejection has the wrong message: %s" % e
            )
        else:
            raise AssertionError(
                "rebuild_elf accepted a 1171-entry phdr table; expected ValueError"
            )
        groups_passed.append("phdr tables over 64 KiB rejected")

        # -- Group 4: a logical LOAD segment may cross ReadFileString's
        # primitive-string ceiling without being split into fake mappings.
        big_path = os.path.join(tmp, "fake_bigseg.elf")
        # A large measured segment size, above one primitive-string chunk.
        big_memsz = 9_878_516
        with open(big_path, "wb") as f:
            f.write(
                build_elf(
                    [
                        (
                            5,
                            "r-x",
                            0x10000,
                            b"\x73\x00\x00\x00\x13\x00\x00\x00",
                            big_memsz,
                        )
                    ]
                )
            )
        big_out = os.path.join(tmp, "out_bigseg")
        os.makedirs(big_out)
        stale_single = os.path.join(big_out, "BigImage_seg_000.hex")
        stale_wide_segment = os.path.join(big_out, "BigImage_seg_1000.hex")
        stale_wide_chunk = os.path.join(
            big_out, "BigImage_seg_1000_chunk_1001.hex"
        )
        unrelated = os.path.join(big_out, "BigImage_seg_not-an-index.hex")
        with open(stale_single, "w") as f:
            f.write("stale")
        for path in (stale_wide_segment, stale_wide_chunk, unrelated):
            with open(path, "w") as f:
                f.write("stale")
        snapshot_binary(big_path, big_out, prefix="BigImage")
        logical = [
            s for s in _parse_elf(big_path)["segments"] if s["base"] == 0x10000
        ]
        assert len(logical) == 1, (
            "large PT_LOAD became %d logical segments instead of one" % len(logical)
        )
        chunk0 = os.path.join(big_out, "BigImage_seg_000_chunk_000.hex")
        chunk1 = os.path.join(big_out, "BigImage_seg_000_chunk_001.hex")
        assert not os.path.exists(stale_single), "obsolete single chunk survived"
        assert not os.path.exists(stale_wide_segment), (
            "obsolete segment index above 999 survived"
        )
        assert not os.path.exists(stale_wide_chunk), (
            "obsolete chunk index above 999 survived"
        )
        assert os.path.exists(unrelated), "cleanup removed a non-owned filename"
        assert os.path.getsize(chunk0) == 2 * elf_snapshot.MAX_CHUNK_BYTES
        assert 0 < os.path.getsize(chunk1) <= 2 * elf_snapshot.MAX_CHUNK_BYTES
        with open(os.path.join(big_out, "BigImage.v")) as f:
            big_v = f.read()
        assert big_v.count("Definition BigImage_segment_000 : Segment") == 1
        assert "seg_bytes := [BigImage_seg_bytes_000_000; " \
               "BigImage_seg_bytes_000_001]" in big_v
        text_base, words, writable = read_text_words(
            big_out, "BigImage", text_range=(0x10000, 0x10008)
        )
        assert (text_base, words, writable) == (0x10000, [0x73, 0x13], False), (
            "fetch-lemma generator did not reassemble the chunked segment: %r"
            % ((text_base, words, writable),)
        )

        # ... but a large .bss is snapshotted, not refused.  A writable
        # segment whose memsz page-rounds just past 1 MiB is ordinary
        # output for a program with a big static table, and the old cap
        # rejected exactly that shape -- a setup failure with no bearing on
        # what the model can express.  Sized like the real binary that hit
        # it: p_memsz 0x110020, page-rounding to 0x111000.
        bss_path = os.path.join(tmp, "fake_big_bss.elf")
        with open(bss_path, "wb") as f:
            f.write(
                build_elf(
                    [
                        (5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),
                        (6, "rw-", 0x20000, b"", 0x110020),
                    ]
                )
            )
        bss_segs = _parse_elf(bss_path)["segments"]
        bss_seg = [s for s in bss_segs if s["base"] == 0x20000]
        assert len(bss_seg) == 1 and bss_seg[0]["size"] == 0x111000, (
            "a 0x110020-memsz writable segment did not snapshot to a "
            "0x111000-byte region: %r" % (bss_segs,)
        )
        assert len(bss_seg[0]["hex_bytes"]) == 2 * 0x111000, (
            "big-bss segment hex is %d chars, expected %d (two per byte)"
            % (len(bss_seg[0]["hex_bytes"]), 2 * 0x111000)
        )

        # The whole-image cap fails hard rather than dropping a segment.
        # Driven through the cap override rather than by building
        # MAX_TOTAL_BYTES of real segments, so this stays a test of the
        # refusal and not of how long half a gigabyte of hex takes to
        # synthesize.  Space the segments by more than a full region so they
        # stay DISJOINT: overlapping ones would be rejected by the overlap
        # check instead, and this group would then pass for the wrong reason.
        total_stride = 2 * elf_snapshot.PAGE_SIZE
        total_specs = [
            (4, "r--", 0x10000 + i * total_stride, b"", elf_snapshot.PAGE_SIZE)
            for i in range(4)
        ]
        total_path = os.path.join(tmp, "fake_totalbytes.elf")
        with open(total_path, "wb") as f:
            f.write(build_elf(total_specs))

        # Calibrate against the image itself: the page-rounded extents this
        # ELF actually loads (the synthesized phdr-mapping LOAD included)
        # are exactly what the cap is compared against.  A cap of that many
        # bytes must be accepted and one byte less refused, so the refusal
        # below is the cap's doing and not some other rejection.
        total_fits = sum(
            seg["size"]
            for seg in _parse_elf(
                total_path, max_total_bytes=elf_snapshot.MAX_TOTAL_BYTES
            )["segments"]
        )
        _parse_elf(total_path, max_total_bytes=total_fits)
        try:
            _parse_elf(total_path, max_total_bytes=total_fits - 1)
        except ValueError as e:
            assert "MAX_TOTAL_BYTES" in str(e), (
                "total-bytes rejection message lacks MAX_TOTAL_BYTES: %s" % e
            )
        else:
            raise AssertionError(
                "LOAD segments over the whole-image cap were silently "
                "accepted/dropped; expected ValueError"
            )
        assert elf_snapshot.MAX_CHUNK_BYTES == 0x7FFFFD, (
            "chunk size 0x%x is not the exact ReadFileString byte ceiling"
            % elf_snapshot.MAX_CHUNK_BYTES
        )
        groups_passed.append("large segments chunked; total limit fail-hard")

        # -- Group 4b: the whole-image cap's value, its ceiling, and the
        # override the command line and the Python API share.  The cap is
        # what setup admits; the ceiling is what the checker can still check, so
        # a cap above the ceiling has to be refused rather than honoured --
        # otherwise a snapshot is built that coqchk dies on.
        assert elf_snapshot.MAX_TOTAL_BYTES == 512 * 1024 * 1024, (
            "MAX_TOTAL_BYTES is %d, not the 512 MiB this toolchain is "
            "measured to handle" % elf_snapshot.MAX_TOTAL_BYTES
        )
        assert elf_snapshot.MAX_TOTAL_BYTES_CEILING == 2040 * 1024 * 1024, (
            "MAX_TOTAL_BYTES_CEILING is %d, not the measured largest image "
            "coqchk accepts" % elf_snapshot.MAX_TOTAL_BYTES_CEILING
        )
        assert (
            elf_snapshot.MAX_TOTAL_BYTES < elf_snapshot.MAX_TOTAL_BYTES_CEILING
        ), "the default cap admits images the checker cannot check"
        assert elf_snapshot.MAX_TOTAL_BYTES_ENV == "ELF_SNAPSHOT_MAX_TOTAL_BYTES"

        env_name = elf_snapshot.MAX_TOTAL_BYTES_ENV
        resolve = elf_snapshot.resolve_max_total_bytes

        # Precedence: flag, then environment, then the constant.
        assert resolve("1000", env={env_name: "2000"}) == 1000, (
            "the flag did not outrank the environment variable"
        )
        assert resolve(None, env={env_name: "2000"}) == 2000, (
            "the environment variable was ignored"
        )
        assert resolve(None, env={}) == elf_snapshot.MAX_TOTAL_BYTES, (
            "with neither override set the constant was not used"
        )
        assert resolve(None, env={env_name: "  "}) == elf_snapshot.MAX_TOTAL_BYTES, (
            "a blank environment variable was read as a cap"
        )
        assert resolve("0x1000", env={}) == 0x1000, "a 0x cap was not parsed"

        # A bool IS an int in Python, so without the guard in _checked_cap
        # True would resolve to a one-byte cap that refuses every image and
        # False to a zero-byte one.  Both have to be refused BY NAME, from
        # every source a cap can arrive through: an AttributeError raised on
        # the way past would stop the run but tell a reader neither which
        # setting was wrong nor what was wrong with it.
        for raw in (True, False):
            for kwargs, source in (
                ({"flag_value": raw}, "--max-total-bytes"),
                ({"env": {env_name: raw}}, env_name),
            ):
                try:
                    resolve(**kwargs)
                except ValueError as e:
                    assert source in str(e), (
                        "the refusal of %r does not name %s: %s"
                        % (raw, source, e)
                    )
                    assert repr(raw) in str(e), (
                        "the refusal of %r does not quote the value: %s"
                        % (raw, e)
                    )
                else:
                    raise AssertionError(
                        "%r was accepted as a byte count from %s"
                        % (raw, source)
                    )

        # Same for the Python API's own keyword, which no command line
        # filters on its way in.
        for raw in (True, False):
            try:
                _parse_elf(total_path, max_total_bytes=raw)
            except ValueError as e:
                assert "max_total_bytes" in str(e) and repr(raw) in str(e), (
                    "the refusal of max_total_bytes=%r names the argument or "
                    "the value poorly: %s" % (raw, e)
                )
            else:
                raise AssertionError(
                    "max_total_bytes=%r was accepted as a byte count" % raw
                )

        # A cap above the ceiling is refused from either source; a cap AT
        # the ceiling is accepted, so the refusal is the ceiling and not an
        # off-by-one that rejects everything large.
        over = elf_snapshot.MAX_TOTAL_BYTES_CEILING + 1
        for kwargs, source in (
            ({"flag_value": str(over)}, "--max-total-bytes"),
            ({"env": {env_name: str(over)}}, env_name),
        ):
            try:
                resolve(**kwargs)
            except ValueError as e:
                assert source in str(e), (
                    "over-ceiling refusal does not name %s: %s" % (source, e)
                )
                assert str(elf_snapshot.MAX_TOTAL_BYTES_CEILING) in str(e), (
                    "over-ceiling refusal does not name the ceiling: %s" % e
                )
            else:
                raise AssertionError(
                    "a cap above MAX_TOTAL_BYTES_CEILING was accepted from "
                    "%s; the checker could not check an image that large" % source
                )
        at = elf_snapshot.MAX_TOTAL_BYTES_CEILING
        assert resolve(str(at), env={}) == at, "the ceiling itself was refused"
        assert resolve(None, env={env_name: str(at)}) == at, (
            "the ceiling itself was refused from the environment"
        )

        # An unusable value is an error that names where it came from,
        # rather than a silently ignored setting.
        for kwargs, source in (
            ({"flag_value": "not-a-number"}, "--max-total-bytes"),
            ({"flag_value": "0"}, "--max-total-bytes"),
            ({"flag_value": "-1"}, "--max-total-bytes"),
            ({"env": {env_name: "not-a-number"}}, env_name),
            ({"env": {env_name: "0"}}, env_name),
            ({"env": {env_name: "-4096"}}, env_name),
        ):
            try:
                resolve(**kwargs)
            except ValueError as e:
                assert source in str(e), (
                    "the refusal of %r does not name %s: %s"
                    % (kwargs, source, e)
                )
            else:
                raise AssertionError(
                    "an unusable cap from %s was accepted: %r" % (source, kwargs)
                )
        # A bad environment variable is an error even when the flag supplies
        # the value, so a typo cannot ride along unnoticed.
        try:
            resolve("4096", env={env_name: "not-a-number"})
        except ValueError as e:
            assert env_name in str(e), (
                "an unparsable environment variable was reported without "
                "naming it: %s" % e
            )
        else:
            raise AssertionError(
                "an unparsable environment variable was ignored because the "
                "flag was also given"
            )

        # End to end through the CLI: --verify is the build gate, so it has
        # to check binaries against the SAME cap the snapshot will run
        # under.  Before this it read only the constant.
        tool = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "elf_snapshot.py")
        verify_dir = os.path.join(tmp, "verify_cap")
        os.makedirs(verify_dir)
        with open(os.path.join(verify_dir, "capped.elf"), "wb") as f:
            f.write(build_elf(total_specs))

        # The developer's own environment must never decide these runs, so
        # the cap variable is removed from every child's environment and set
        # back only where the case under test wants it.  The rest of the
        # environment is carried so the interpreter still starts; if a real
        # setting ever did leak through, the constant-source assertions
        # below would be the ones to fail.
        def run_verify(extra_args=(), env_value=None, target=None):
            env = dict(os.environ)
            env.pop(env_name, None)
            if env_value is not None:
                env[env_name] = env_value
            return subprocess.run(
                [sys.executable, tool, "--verify", target or verify_dir]
                + list(extra_args),
                capture_output=True, text=True, env=env,
            )

        # The gate's report has to say what cap it actually applied and
        # which of the three sources supplied it.  A pass that names no cap
        # tells a reader nothing about what was admitted, and a bare number
        # would not separate an intended override from a stale variable.
        def cap_line(result):
            marker = "elf_snapshot --verify: whole-image cap "
            found = [
                ln for ln in result.stderr.splitlines() if ln.startswith(marker)
            ]
            assert len(found) == 1, (
                "--verify did not report its effective cap exactly once; "
                "stderr was %r" % result.stderr
            )
            return found[0]

        def expect_cap_line(result, cap, source, what):
            want = ("elf_snapshot --verify: whole-image cap 0x%x bytes, "
                    "from %s" % (cap, source))
            assert cap_line(result) == want, (
                "--verify %s reported %r, wanted %r"
                % (what, cap_line(result), want)
            )

        base = run_verify()
        assert base.returncode == 0, (
            "--verify rejected an in-cap binary under the default cap: %s"
            % base.stderr
        )
        expect_cap_line(
            base, elf_snapshot.MAX_TOTAL_BYTES, elf_snapshot.CAP_SOURCE_CONSTANT,
            "passing with neither override set",
        )
        env_run = run_verify(env_value=str(total_fits - 1))
        assert env_run.returncode == 1 and "UNSNAPSHOTTABLE" in env_run.stderr, (
            "--verify ignored %s: exit %d, stderr %s"
            % (env_name, env_run.returncode, env_run.stderr)
        )
        expect_cap_line(
            env_run, total_fits - 1, elf_snapshot.CAP_SOURCE_ENV,
            "failing under the environment variable",
        )
        flag_run = run_verify(
            extra_args=["--max-total-bytes", str(total_fits - 1)]
        )
        assert flag_run.returncode == 1 and "UNSNAPSHOTTABLE" in flag_run.stderr, (
            "--verify ignored --max-total-bytes: exit %d, stderr %s"
            % (flag_run.returncode, flag_run.stderr)
        )
        expect_cap_line(
            flag_run, total_fits - 1, elf_snapshot.CAP_SOURCE_FLAG,
            "failing under the flag",
        )
        flag_wins = run_verify(
            extra_args=["--max-total-bytes", str(total_fits)],
            env_value=str(total_fits - 1),
        )
        assert flag_wins.returncode == 0, (
            "--verify let %s outrank --max-total-bytes: exit %d, stderr %s"
            % (env_name, flag_wins.returncode, flag_wins.stderr)
        )
        expect_cap_line(
            flag_wins, total_fits, elf_snapshot.CAP_SOURCE_FLAG,
            "passing with the flag outranking the environment",
        )

        # The constant as the source on a FAILING run too, so the report is
        # not something only a passing gate prints.  An ELF truncated below
        # a header is refused for a reason that has nothing to do with size,
        # which keeps this case about the reporting.
        bad_dir = os.path.join(tmp, "verify_bad")
        os.makedirs(bad_dir)
        with open(os.path.join(bad_dir, "truncated.elf"), "wb") as f:
            f.write(b"\x7fELF" + b"\x00" * 8)
        bad_run = run_verify(target=bad_dir)
        assert bad_run.returncode == 1 and "UNSNAPSHOTTABLE" in bad_run.stderr, (
            "--verify accepted a truncated ELF: exit %d, stderr %s"
            % (bad_run.returncode, bad_run.stderr)
        )
        expect_cap_line(
            bad_run, elf_snapshot.MAX_TOTAL_BYTES,
            elf_snapshot.CAP_SOURCE_CONSTANT,
            "failing with neither override set",
        )

        # The three source phrases have to be tellable apart in a report --
        # MAX_TOTAL_BYTES is itself a substring of the variable's name.
        sources = [
            elf_snapshot.CAP_SOURCE_FLAG,
            elf_snapshot.CAP_SOURCE_ENV,
            elf_snapshot.CAP_SOURCE_CONSTANT,
        ]
        for one in sources:
            for other in sources:
                assert one == other or one not in other, (
                    "cap source %r cannot be told from %r in a report"
                    % (one, other)
                )
        bad_env = run_verify(env_value="not-a-number")
        assert bad_env.returncode == 2 and env_name in bad_env.stderr, (
            "--verify did not fail on an unparsable %s: exit %d, stderr %s"
            % (env_name, bad_env.returncode, bad_env.stderr)
        )
        over_flag = run_verify(extra_args=["--max-total-bytes", str(over)])
        assert (
            over_flag.returncode == 2
            and str(elf_snapshot.MAX_TOTAL_BYTES_CEILING) in over_flag.stderr
        ), (
            "--verify accepted a cap above the ceiling: exit %d, stderr %s"
            % (over_flag.returncode, over_flag.stderr)
        )
        groups_passed.append(
            "whole-image cap value, coqchk ceiling, and the "
            "flag/environment/constant override through --verify"
        )

        # -- Group 5: init_pc comes from e_entry even when a _start symbol
        # exists at a DIFFERENT address (BUG 37): the kernel jumps to
        # e_entry; the symbol table is advisory metadata.
        sym_path = os.path.join(tmp, "fake_start_sym.elf")
        with open(sym_path, "wb") as f:
            f.write(build_elf(SEG_SPECS, start_symbol_at=ENTRY + 0x40))
        sym_out = os.path.join(tmp, "out_sym")
        os.makedirs(sym_out)
        sym_result = snapshot_binary(sym_path, sym_out, prefix="MemImage")
        assert sym_result["init_pc"] == ENTRY, (
            "init_pc 0x%x != e_entry 0x%x: loader preferred the _start "
            "symbol (0x%x) over the ELF header entry point"
            % (sym_result["init_pc"], ENTRY, ENTRY + 0x40)
        )
        with open(os.path.join(sym_out, "MemImage.v")) as f:
            sym_v = f.read()
        assert ("Definition MemImage_init_pc : N := 0x%x%%N." % ENTRY) in sym_v, (
            "emitted init_pc is not e_entry:\n%s" % sym_v
        )
        groups_passed.append("init_pc from e_entry, not _start symbol")

        # -- Group 6: a LOAD segment whose file extent runs past the end of
        # the ELF (truncated/crafted file) is rejected instead of being
        # silently short-read and zero-padded (BUG 40).
        whole = build_elf(SEG_SPECS)
        trunc_path = os.path.join(tmp, "fake_truncated.elf")
        with open(trunc_path, "wb") as f:
            f.write(whole[:-3])  # chop tail of the last segment's file bytes
        try:
            _parse_elf(trunc_path)
        except ValueError as e:
            assert "file extent" in str(e), (
                "truncated-ELF rejection message lacks 'file extent': %s" % e
            )
        else:
            raise AssertionError(
                "truncated ELF (segment file extent past EOF) was accepted; "
                "expected ValueError"
            )
        groups_passed.append("file-extent past EOF rejection")

        # -- Group 7: overlapping LOAD segments are rejected (BUG 39).  The
        # kernel resolves overlaps last-mapping-wins; the model's
        # find_segment scan is first-match — so overlaps must never reach
        # the model.  Real toolchains never emit them.
        overlap_specs = [
            (5, "r-x", 0x10000, b"\x13\x05\x00\x00", 0x100),
            (6, "rw-", 0x100f0, b"\xde\xad", 0x20),  # starts inside seg 0
        ]
        overlap_path = os.path.join(tmp, "fake_overlap.elf")
        with open(overlap_path, "wb") as f:
            f.write(build_elf(overlap_specs))
        try:
            _parse_elf(overlap_path)
        except ValueError as e:
            assert "overlapping LOAD segments" in str(e), (
                "overlap rejection message lacks 'overlapping LOAD "
                "segments': %s" % e
            )
        else:
            raise AssertionError(
                "overlapping LOAD segments were accepted; expected ValueError"
            )
        # Exactly-adjacent segments (prev page extent end == next page
        # extent base) must still parse.
        adjacent_specs = [
            (5, "r-x", 0x10000, b"\x13\x05\x00\x00", 0x100),
            (6, "rw-", 0x11000, b"\xde\xad", 0x20),
        ]
        adjacent_path = os.path.join(tmp, "fake_adjacent.elf")
        with open(adjacent_path, "wb") as f:
            f.write(build_elf(adjacent_specs))
        adj = _parse_elf(adjacent_path)
        assert len(adj["segments"]) == 3, (
            "exactly-adjacent segments were not both kept (+ the phdr "
            "segment): %d" % len(adj["segments"])
        )
        groups_passed.append("overlapping LOAD segment rejection")

        # -- Group 8: page rounding (BUG 38).  The kernel maps whole pages:
        # a segment at an unaligned vaddr occupies
        # [round_down(vaddr), round_up(vaddr+memsz)), and those pages are a
        # FILE mapping — the head slack [round_down(vaddr), vaddr) holds
        # the file bytes before p_offset (zero-filling it was the bug that
        # broke lld/zig layouts whose first section starts mid-page), and a
        # memsz == filesz segment's last page holds the file bytes after
        # p_offset + p_filesz.
        #
        # Layout of the fixture file (build_elf pads for congruence):
        # seg0's 4 bytes land at file offset 0x1000, then 0x230 bytes of
        # padding, then seg1's 4 bytes at file offset 0x1234, where the
        # payload (and file) ends.
        rounded_specs = [
            (5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),
            # unaligned base, memsz > filesz: 0x234 head slack mapping the
            # file bytes before p_offset, then bss zeros out to the page
            # boundary.
            (6, "rw-", 0x11234, b"\xca\xfe\xba\xbe", 0x10),
        ]
        round_path = os.path.join(tmp, "fake_rounding.elf")
        with open(round_path, "wb") as f:
            f.write(build_elf(rounded_specs))
        rnd = _parse_elf(round_path)
        assert len(rnd["segments"]) == 3
        s0, s1, _hdr = rnd["segments"]
        assert (s0["base"], s0["size"]) == (0x10000, 0x1000), (
            "aligned segment not rounded to one page: base=0x%x size=0x%x"
            % (s0["base"], s0["size"])
        )
        # s0 has memsz == filesz, so its single page is pure file mapping:
        # its tail holds what follows in the FILE (padding zeros, then
        # seg1's bytes at in-page offset 0x234), zero past EOF.
        assert s0["hex_bytes"] == (
            b"\x13\x05\x00\x00"
            + b"\x00" * 0x230
            + b"\xca\xfe\xba\xbe"
            + b"\x00" * (0x1000 - 0x238)
        ).hex(), (
            "memsz==filesz segment's page tail must map the file bytes "
            "after p_offset + p_filesz (kernel file-page mapping)"
        )
        assert (s1["base"], s1["size"]) == (0x11000, 0x1000), (
            "unaligned segment extent not [0x11000, 0x12000): base=0x%x "
            "size=0x%x" % (s1["base"], s1["size"])
        )
        # s1's head slack maps the 0x234 file bytes before its p_offset
        # (seg0's bytes + congruence padding) — NOT zeros; past
        # vaddr + filesz it carries bss and is zeroed.
        want1 = (
            b"\x13\x05\x00\x00"
            + b"\x00" * 0x230
            + b"\xca\xfe\xba\xbe"
            + b"\x00" * (0x1000 - 0x234 - 4)
        )
        assert s1["hex_bytes"] == want1.hex(), (
            "unaligned segment's head slack must map the file bytes before "
            "p_offset, and its bss tail must be zeroed"
        )
        # A zero-memsz LOAD segment maps no pages at all.
        empty_specs = [
            (5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),
            (4, "r--", 0x12345, b"", 0),
        ]
        empty_path = os.path.join(tmp, "fake_emptyseg.elf")
        with open(empty_path, "wb") as f:
            f.write(build_elf(empty_specs))
        assert len(_parse_elf(empty_path)["segments"]) == 2, (
            "zero-memsz LOAD segment should map nothing (leaving the text "
            "and phdr segments)"
        )
        groups_passed.append("page-rounded extents map whole file pages")

        # -- Group 9: w+x (RWX) LOAD segments are snapshotted faithfully.
        #
        # Instruction fetch reads a writable executable segment through the
        # writable overlay with the image bytes underneath (code_read_ov in
        # RiscvSemantics.v), so the RWX layout GNU ld's default
        # -z noseparate-code produces (one merged segment holding .text +
        # the initialized writable sections) is an ordinary image.
        # These cases pin the acceptance, with the perms recorded
        # exactly, so the model's per-segment gates see the truth.
        for label, rwx_specs, want_perms in [
            # The realistic shape ld produces: one merged RWX segment
            # holding .text + .rodata + .sdata/.bss, containing the entry.
            ("single merged RWX segment at the entry point",
             [(7, "rwx", 0x10000, b"\x13\x05\x00\x00", 0x1970)],
             ["rwx", HDR_PERMS]),
            # An RWX segment that is NOT the entry segment.
            ("non-entry RWX segment alongside a clean r-x text segment",
             [(5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),
              (7, "rwx", 0x20000, b"\xde\xad\xbe\xef", None)],
             ["r-x", "rwx", HDR_PERMS]),
            # Write+execute without read is still snapshotted as such.
            ("w+x segment without the read flag",
             [(3, "-wx", 0x10000, b"\x13\x05\x00\x00", None)],
             ["-wx", HDR_PERMS]),
        ]:
            rwx_path = os.path.join(tmp, "fake_rwx_accept.elf")
            with open(rwx_path, "wb") as f:
                f.write(build_elf(rwx_specs))
            got = [s["perms"] for s in _parse_elf(rwx_path)["segments"]]
            assert got == want_perms, (
                "%s: expected perms %r, got %r" % (label, want_perms, got)
            )

        # And through the programmatic snapshot path (snapshot_binary), not
        # just the parser.
        rwx_path = os.path.join(tmp, "fake_rwx_top.elf")
        with open(rwx_path, "wb") as f:
            f.write(build_elf([(7, "rwx", 0x10000, b"\x13\x05\x00\x00", None)]))
        snapshot_binary(rwx_path, os.path.join(tmp, "rwx_out"))

        # w and x in SEPARATE segments (the
        # normal, correct layout that -z separate-code produces) must still
        # be accepted, so the check cannot regress into rejecting everything.
        ok_path = os.path.join(tmp, "fake_wx_split.elf")
        with open(ok_path, "wb") as f:
            f.write(build_elf([
                (4, "r--", 0x10000, b"RODATA", None),
                (5, "r-x", 0x11000, b"\x13\x05\x00\x00", None),
                (6, "rw-", 0x12000, b"\xde\xad", 0x20),
            ]))
        split = _parse_elf(ok_path)
        # (the trailing HDR_PERMS segment is build_elf's phdr mapping)
        assert [s["perms"] for s in split["segments"]] == [
            "r--", "r-x", "rw-", HDR_PERMS
        ], (
            "the -z separate-code layout (r--, r-x, rw-) must be accepted: %r"
            % [s["perms"] for s in split["segments"]]
        )
        # A p_memsz == 0 LOAD entry with RWX flags maps NO pages, so it is not
        # an RWX text segment and must not abort the snapshot: the w+x check
        # sits below the zero-memsz skip, and a diagnostic here would point at
        # a segment that does not exist in the image.
        zero_rwx_path = os.path.join(tmp, "fake_zero_rwx.elf")
        with open(zero_rwx_path, "wb") as f:
            f.write(build_elf([
                (5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),
                (7, "rwx", 0x20000, b"", 0),
            ]))
        zero_rwx = _parse_elf(zero_rwx_path)
        assert [s["perms"] for s in zero_rwx["segments"]] == ["r-x", HDR_PERMS], (
            "a zero-memsz RWX LOAD entry maps nothing and must be skipped, "
            "not rejected: %r" % [s["perms"] for s in zero_rwx["segments"]]
        )
        groups_passed.append("w+x (RWX) LOAD segment acceptance")

        # -- Group 10: an image with NO mapped LOAD segment is rejected.
        #
        # This is the MAXIMALLY vacuous image, and it is vacuous in a way the
        # w+x check cannot see: find_segment returns None for every address
        # on an empty segment list, so the first instruction fetch fails,
        # [Run.all_traces_error] holds of the initial configuration, and
        # [Equivalence.equiv]'s bh_all_errors escape admits ANY target — the
        # hole reached by having no text at all.  The Rocq-side check is
        # [Equivalence.image_entry_fetchable], and this is the same check
        # one layer earlier, where the image is built.
        for idx, (label, no_load_specs) in enumerate([
            # No PT_LOAD entry at all (e_phnum == 0).
            ("no program headers at all", []),
            # PT_LOAD entries that map nothing (p_memsz == 0).
            ("only zero-memsz PT_LOAD entries",
             [(5, "r-x", 0x10000, b"", 0), (6, "rw-", 0x20000, b"", 0)]),
        ]):
            no_load_path = os.path.join(tmp, "fake_no_load_%d.elf" % idx)
            with open(no_load_path, "wb") as f:
                # map_phdrs=False: build_elf's phdr-mapping LOAD segment would
                # itself be a mapped segment, which is not the image under test.
                f.write(build_elf(no_load_specs, map_phdrs=False))
            try:
                _parse_elf(no_load_path)
            except ValueError as e:
                assert "PT_LOAD" in str(e), (
                    "%s: rejected, but not with the no-mapped-segment "
                    "diagnostic: %s" % (label, e)
                )
            else:
                raise AssertionError(
                    "%s: _parse_elf ACCEPTED an ELF that maps nothing.  Such "
                    "an image faults on its first fetch, making a source task "
                    "vacuous via equiv's bh_all_errors escape "
                    "— it must be rejected here."
                    % label
                )
        # snapshot_binary must refuse too, not just the parser (same reason
        # as the w+x case above).
        no_load_top = os.path.join(tmp, "fake_no_load_top.elf")
        with open(no_load_top, "wb") as f:
            f.write(build_elf([], map_phdrs=False))
        try:
            snapshot_binary(no_load_top, os.path.join(tmp, "no_load_out"))
        except ValueError as e:
            assert "PT_LOAD" in str(e), (
                "snapshot_binary: wrong diagnostic: %s" % e
            )
        else:
            raise AssertionError(
                "snapshot_binary accepted an ELF with no mapped LOAD segment"
            )
        groups_passed.append("no-mapped-LOAD-segment rejection")

        # -- Group 11: the kernel's whole-page FILE mapping, pinned byte by
        # byte.  elf_load (fs/binfmt_elf.c) maps a segment's pages FROM THE
        # FILE at offset p_offset - (p_vaddr % PAGE): head slack holds the
        # preceding file bytes (zero-filling it was the bug that broke
        # lld/zig layouts whose first section starts mid-page — there the
        # slack holds the ELF header and phdr table, memory a real process
        # reads), a bss-carrying segment is zeroed past vaddr + filesz even
        # where the file has bytes, and a mapping reaching past EOF reads
        # zeros.  Three mid-page segments whose file extents interleave
        # within each other's pages:
        kfm_specs = [
            (5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),
            # bss-carrying (memsz > filesz): its page must be zeroed past
            # vaddr + filesz even though seg2's "RODATA" sits there in the
            # FILE.
            (6, "rw-", 0x11080, b"\xde\xad", 0x100),
            # memsz == filesz: pure file mapping, tail past EOF reads zero.
            (4, "r--", 0x12100, b"RODATA", None),
        ]
        kfm_path = os.path.join(tmp, "fake_filemap.elf")
        kfm_data = build_elf(kfm_specs)
        with open(kfm_path, "wb") as f:
            f.write(kfm_data)
        kfm_phs = load_phdrs(kfm_data)
        ph1, ph2 = kfm_phs[1], kfm_phs[2]
        kfm_segs = _parse_elf(kfm_path)["segments"]
        k1 = [s for s in kfm_segs if s["base"] == 0x11000][0]
        k2 = [s for s in kfm_segs if s["base"] == 0x12000][0]

        # Anti-vacuity: the file bytes the rules below act on really are
        # where the fixture intends them.  seg2's contents lie inside
        # seg1's mapped file page (so the bss zeroing has something real
        # to zero), and seg1's head-slack file window is not all zeros.
        d1 = ph1["vaddr"] % PAGE
        head1 = kfm_data[ph1["offset"] - d1 : ph1["offset"]]
        assert ph1["offset"] - d1 + PAGE > ph2["offset"] and (
            kfm_data[ph2["offset"] : ph2["offset"] + 6] == b"RODATA"
        ), "fixture drifted: seg2's bytes are not in seg1's file page"
        assert head1 != b"\x00" * len(head1), (
            "fixture drifted: seg1's head-slack file window is all zeros, "
            "so the head-slack assertion would not detect zero-filling"
        )

        # seg1: head slack = preceding file bytes; everything past
        # vaddr + filesz zeroed (bss), including over seg2's file bytes.
        want_k1 = head1 + b"\xde\xad" + b"\x00" * (PAGE - d1 - 2)
        assert k1["hex_bytes"] == want_k1.hex(), (
            "bss-carrying segment: head slack must map the file bytes "
            "before p_offset and the page must be zeroed past "
            "vaddr + filesz (the kernel's padzero), even where the file "
            "has bytes"
        )

        # seg2: head slack = preceding file bytes (which include seg1's
        # \xde\xad); the tail maps file bytes past EOF, which read zero.
        d2 = ph2["vaddr"] % PAGE
        head2 = kfm_data[ph2["offset"] - d2 : ph2["offset"]]
        assert b"\xde\xad" in head2, (
            "fixture drifted: seg1's bytes are not in seg2's head slack"
        )
        want_k2 = head2 + b"RODATA" + b"\x00" * (PAGE - d2 - 6)
        assert k2["hex_bytes"] == want_k2.hex(), (
            "memsz==filesz segment: head slack must map the file bytes "
            "before p_offset, and the mapping past EOF must read zero"
        )

        # A file-backed segment whose p_vaddr and p_offset are NOT
        # congruent mod the page size is rejected: the kernel's elf_map
        # hands vm_mmap a non-page-aligned file offset and the execve
        # fails, so such a binary has no process semantics to snapshot.
        noncong_path = os.path.join(tmp, "fake_noncongruent.elf")
        with open(noncong_path, "wb") as f:
            f.write(build_elf([], hdr_maps=[(4, EHDR_SIZE, 0x10, 0x8000)]))
        try:
            _parse_elf(noncong_path)
        except ValueError as e:
            assert "not congruent" in str(e), (
                "non-congruent segment rejection has the wrong message: %s"
                % e
            )
        else:
            raise AssertionError(
                "a LOAD segment with p_vaddr and p_offset not congruent "
                "mod the page size was accepted; the kernel cannot exec it"
            )

        # ...but a zero-filesz segment maps no file bytes at all (anonymous
        # pages only), so congruence does not apply and its extent is pure
        # zeros regardless of its (meaningless) p_offset.
        anon_path = os.path.join(tmp, "fake_anon_noncongruent.elf")
        with open(anon_path, "wb") as f:
            f.write(build_elf([
                (5, "r-x", 0x10000, b"\x13\x05\x00\x00", None),
                (6, "rw-", 0x13010, b"", 0x20),
            ]))
        anon_segs = _parse_elf(anon_path)["segments"]
        anon = [s for s in anon_segs if s["base"] == 0x13000][0]
        assert anon["hex_bytes"] == ("00" * PAGE), (
            "zero-filesz segment must map anonymous zeros regardless of "
            "p_offset congruence"
        )
        groups_passed.append("kernel file-page mapping (head/bss/EOF/congruence)")

    # -- Group: --rebuild puts a snapshot back into an ELF that loads to it.
    # The round trip is what makes a run of a binary rebuilt this way a run
    # of the binary the proof is about.  Positive: parse(rebuild(snapshot(x)))
    # is parse(x) for the fixture, for the nonzero-p_offset phdr layout, and
    # for every committed example snapshot.  Negative: the rebuilt binary
    # follows the SNAPSHOT, not the original -- a byte edited in a .hex
    # chunk comes back in the rebuilt image and no longer matches the
    # original -- and a snapshot whose phdr table names a LOAD the snapshot
    # does not hold, a chunk file of the wrong length, a header type the
    # kernel reads from the file outside every LOAD, and a .v that is not
    # the emitter's template are each refused naming the reason.
    with tempfile.TemporaryDirectory() as tmp:
        from elf_snapshot import read_snapshot, rebuild, rebuild_elf

        def round_trip(name, elf_data, **build_kw):
            src = os.path.join(tmp, name + ".elf")
            with open(src, "wb") as f:
                f.write(elf_data)
            out_dir = os.path.join(tmp, name + ".snap")
            os.makedirs(out_dir)
            snapshot_binary(src, out_dir, prefix="MemImage")
            v_path = os.path.join(out_dir, "MemImage.v")
            snap = read_snapshot(v_path)
            assert snap == _parse_elf(src), (
                "%s: read_snapshot does not read back what snapshot_binary wrote" % name
            )
            rebuilt = os.path.join(tmp, name + ".rebuilt")
            rc = rebuild(v_path, rebuilt)
            assert rc == 0 and os.path.isfile(rebuilt), "%s: --rebuild failed" % name
            assert _parse_elf(rebuilt) == _parse_elf(src), (
                "%s: the rebuilt ELF does not load to the original's image" % name
            )
            return v_path, rebuilt

        v_path, _ = round_trip("plain", build_elf(SEG_SPECS))
        off_specs = [(5, "r-x", 0x10000, b"\x13\x05\x00\x00", None)]
        off_data_off = EHDR_SIZE + (len(off_specs) + 2) * PHENTSIZE
        round_trip("phdr_offset", build_elf(off_specs, hdr_maps=[
            (4, 0, EHDR_SIZE, 0x8000),
            (4, EHDR_SIZE, off_data_off - EHDR_SIZE, 0x9000 + EHDR_SIZE),
        ]))
        round_trip("tls", build_elf(SEG_SPECS, tls_extra=True, tls_vaddr=0x20000))
        round_trip("rwx", build_elf([(7, "rwx", 0x10000, b"\x13\x05\x00\x00", None)]))

        examples_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                    "theories", "Examples")
        committed = sorted(
            os.path.join(d, v) for d in
            (os.path.join(examples_dir, e) for e in os.listdir(examples_dir))
            for v in ("SourceMemImage.v", "TargetMemImage.v") if os.path.isfile(os.path.join(d, v))
        )
        assert committed, "no committed example snapshot under %s" % examples_dir
        for v in committed:
            out = os.path.join(tmp, os.path.basename(os.path.dirname(v)) + "-" + os.path.basename(v))
            assert rebuild(v, out) == 0, "committed snapshot %s does not rebuild" % v
            assert _parse_elf(out) == read_snapshot(v), "%s: rebuilt image is not the snapshot" % v

        # The rebuilt binary is the snapshot's, not the original's: edit one
        # byte of the text chunk and the rebuilt image carries the edit.
        edited_dir = os.path.join(tmp, "edited")
        import shutil
        shutil.copytree(os.path.dirname(v_path), edited_dir)
        hex_path = os.path.join(edited_dir, "MemImage_seg_000.hex")
        with open(hex_path) as f:
            h = f.read()
        assert h[:2] == "13", "the fixture's first text byte is 0x13"
        with open(hex_path, "w") as f:
            f.write("ff" + h[2:])
        edited_out = os.path.join(tmp, "edited.rebuilt")
        assert rebuild(os.path.join(edited_dir, "MemImage.v"), edited_out) == 0
        assert _parse_elf(edited_out) == read_snapshot(os.path.join(edited_dir, "MemImage.v"))
        assert _parse_elf(edited_out) != _parse_elf(os.path.join(tmp, "plain.elf")), (
            "a rebuilt ELF must follow the edited snapshot, not the original binary"
        )

        def refuses(name, v, phrase):
            try:
                rebuild_elf(read_snapshot(v))
            except ValueError as e:
                assert phrase in str(e), "%s: refused, but not for the stated reason: %s" % (name, e)
                return
            raise AssertionError("%s: not refused" % name)

        # A chunk file whose length is not the segment's declared size.
        short_dir = os.path.join(tmp, "short")
        shutil.copytree(os.path.dirname(v_path), short_dir)
        with open(os.path.join(short_dir, "MemImage_seg_000.hex"), "w") as f:
            f.write(h[:-2])
        refuses("a short chunk file", os.path.join(short_dir, "MemImage.v"), "chunk files hold")

        # loaded_segments missing the segment a LOAD's file bytes live in.
        dropped_dir = os.path.join(tmp, "dropped")
        shutil.copytree(os.path.dirname(v_path), dropped_dir)
        dv = os.path.join(dropped_dir, "MemImage.v")
        with open(dv) as f:
            text = f.read()
        assert "MemImage_segment_000;\n" in text
        with open(dv, "w") as f:
            f.write(text.replace("[ MemImage_segment_000;\n  ", "[ "))
        refuses("a LOAD whose bytes the snapshot lacks", dv, "not inside any snapshotted segment")

        # A PT_INTERP outside every LOAD's file extent: the kernel reads it
        # from the file, and the snapshot cannot supply it.  Patched into
        # the phdr table as the image holds it: the TLS fixture's PT_TLS
        # entry becomes type 3 at a file offset past everything mapped.
        tls_dir = os.path.join(tmp, "tls.snap")
        tv = os.path.join(tls_dir, "MemImage.v")
        tsnap = read_snapshot(tv)
        ph = tsnap["phdrs"]
        hdr_seg = [s for s in tsnap["segments"] if s["base"] <= ph["addr"] < s["base"] + s["size"]][0]
        table_off = ph["addr"] - hdr_seg["base"]
        raw = bytearray(bytes.fromhex(hdr_seg["hex_bytes"]))
        patched = False
        for i in range(ph["num"]):
            off = table_off + i * ph["ent"]
            if struct.unpack_from("<I", raw, off)[0] == 7:  # PT_TLS
                struct.pack_into("<I", raw, off, 3)         # PT_INTERP
                struct.pack_into("<Q", raw, off + 8, 0x100000)  # p_offset past every LOAD
                struct.pack_into("<Q", raw, off + 32, 8)    # p_filesz
                patched = True
        assert patched, "the TLS fixture has a PT_TLS entry to patch"
        idx = tsnap["segments"].index(hdr_seg)
        hex_name = "MemImage_seg_%03d.hex" % idx
        with open(os.path.join(tls_dir, hex_name), "w") as f:
            f.write(raw.hex())
        refuses("a PT_INTERP outside every LOAD", tv, "outside every LOAD")

        # The round trip is the check that makes a rebuilt binary trustworthy,
        # so it has to be shown failing: a snapshot whose image carries a phdr
        # table that disagrees with its own segments (here a LOAD's p_flags
        # patched to rwx while the segment says r-x) rebuilds to a file the
        # kernel would load with other permissions, and rebuild() must refuse
        # it -- returning 1, deleting the output, saying why.
        import contextlib
        import io
        flags_dir = os.path.join(tmp, "flags.snap")
        shutil.copytree(os.path.dirname(v_path), flags_dir)
        fv = os.path.join(flags_dir, "MemImage.v")
        fsnap = read_snapshot(fv)
        fph = fsnap["phdrs"]
        fhdr = [s for s in fsnap["segments"] if s["base"] <= fph["addr"] < s["base"] + s["size"]][0]
        ftable = fph["addr"] - fhdr["base"]
        raw = bytearray(bytes.fromhex(fhdr["hex_bytes"]))
        patched = False
        for i in range(fph["num"]):
            off = ftable + i * fph["ent"]
            if struct.unpack_from("<I", raw, off)[0] == 1 and struct.unpack_from("<I", raw, off + 4)[0] == 5:
                struct.pack_into("<I", raw, off + 4, 7)  # PF_R|PF_W|PF_X on the r-x LOAD
                patched = True
                break
        assert patched, "the plain fixture has an r-x LOAD to patch"
        with open(os.path.join(flags_dir, "MemImage_seg_%03d.hex" % fsnap["segments"].index(fhdr)), "w") as f:
            f.write(raw.hex())
        flags_out = os.path.join(tmp, "flags.rebuilt")
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = rebuild(fv, flags_out)
        assert rc == 1, "a rebuilt file that does not load to the snapshot's image was kept (rc %d)" % rc
        assert not os.path.exists(flags_out), "the refused rebuild was left on disk"
        assert "does not load to the snapshot's image" in err.getvalue(), err.getvalue()
        # ...and rebuild_elf itself is not what refused: the table is consistent
        # enough to write a file, which is exactly why the round trip is needed.
        rebuild_elf(read_snapshot(fv))

        # Not the emitter's template at all.
        bad_v = os.path.join(tmp, "NotASnapshot.v")
        with open(bad_v, "w") as f:
            f.write("Definition x := 1.\n")
        try:
            read_snapshot(bad_v)
            raise AssertionError("a file that is not a snapshot was read")
        except ValueError as e:
            assert "not a snapshot this tool emitted" in str(e), e
        assert rebuild(bad_v, os.path.join(tmp, "never")) == 1
        assert not os.path.exists(os.path.join(tmp, "never"))
        groups_passed.append("--rebuild round trip (fixtures, committed examples; edited/short/dropped/interp/flags/non-snapshot refusals)")

    for g in groups_passed:
        print("PASS: %s" % g)
    print("OK: %d assertion groups passed" % len(groups_passed))


def emit_large_rocq_check(out_path):
    """Emit a Rocq check of a large segment that spans two hex chunks."""
    measured_memsz = 9_878_516
    size = (
        (measured_memsz + elf_snapshot.PAGE_SIZE - 1)
        // elf_snapshot.PAGE_SIZE
        * elf_snapshot.PAGE_SIZE
    )
    boundary = elf_snapshot.MAX_CHUNK_BYTES
    data = bytearray(size)
    data[boundary - 2 : boundary + 3] = b"\x11\x22\x33\x44\x55"
    elf_snapshot._emit_coq(
        [
            {
                "base": 0x10000,
                "size": size,
                "perms": "r-x",
                "hex_bytes": data.hex(),
            }
        ],
        0x10000,
        {"addr": 0x10000, "ent": 56, "num": 1},
        out_path,
        prefix="LargeChunkImage",
        namespace="LinuxProcessSemantics.Tests",
    )
    with open(out_path, "a") as f:
        f.write(
            """
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics.
Open Scope bv_scope.

Example large_chunk_join_data_read :
  memory_read LargeChunkImage_loaded_segments (Z_to_bv 64 0x80fffb) 5 =
    Some [Z_to_bv 8 0x11; Z_to_bv 8 0x22; Z_to_bv 8 0x33;
          Z_to_bv 8 0x44; Z_to_bv 8 0x55].
Proof. vm_compute. reflexivity. Qed.

Example large_chunk_join_instruction_fetch :
  fetch_word LargeChunkImage_loaded_segments (Z_to_bv 64 0x80fffc) =
    Some (Z_to_bv 32 0x55443322).
Proof. vm_compute. reflexivity. Qed.
"""
        )


if __name__ == "__main__":
    if sys.argv[1:2] == ["--emit-large-rocq-check"]:
        if len(sys.argv) != 3:
            sys.exit("usage: test_elf_snapshot.py --emit-large-rocq-check OUT.v")
        emit_large_rocq_check(sys.argv[2])
    else:
        main()
