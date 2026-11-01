#!/usr/bin/env python3
"""Measure a riscv64 Linux vDSO image.

Usage:
    python3 measure_vdso.py vdso-defconfig.so [more.so ...]

It prints a JSON list, one object per image, on stdout.

The script uses the Python standard library only.  It parses the ELF file
itself with ``struct``.  It reads the dynamic symbol table through
``PT_DYNAMIC``/``DT_SYMTAB``/``DT_STRTAB``, as musl's ``__vdsosym`` does.
It decodes the RV64GC instructions itself, so it does not need a riscv64
``objdump``.

The script holds a record of the build of each known image and a record of
the ``readelf`` output for it, both keyed by the SHA-256 of the image.  The
script compares its own result against the ``readelf`` record and puts the
result of that comparison in the JSON.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import struct
import sys

HEX_CHUNK_CHARS = 1024  # 512 bytes per chunk

# --------------------------------------------------------------------------
# Records of the builds, keyed by the SHA-256 of the image.
# --------------------------------------------------------------------------

# The configuration each delivered file was built with.
FILE_CONFIG = {
    "vdso-defconfig.so": "defconfig",
    "vdso-defconfig-thp.so": "defconfig + CONFIG_TRANSPARENT_HUGEPAGE=y",
    "vdso-defconfig-norandom.so": "defconfig + no randomisation",
}

BUILD_RECORDS = {
    "0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36": {
        "kernel_repo": "https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git",
        "kernel_tag": "v6.18.46",
        "kernel_commit": "1f99e9ab748fc5c32120de9c4eca31abfe54a4d5",
        "arch": "riscv",
        "cross_compile": "riscv64-linux-gnu-",
        "machine": "GCE VM ossv-lpsrev-vdso (32 vCPU)",
        "container_image": "vdsobuild:1 (built from debian:trixie)",
        "container_image_id": "sha256:b2a3aaad7a485cbd9a372bd4aa068ce0ecc60e92125c195b6a39af95a8dfade7",
        "container_base_image": "debian:trixie",
        "toolchain": {
            "gcc": "riscv64-linux-gnu-gcc (Debian 14.2.0-19) 14.2.0",
            "ld": "GNU ld (GNU Binutils for Debian) 2.44",
            "objdump": "GNU objdump (GNU Binutils for Debian) 2.44",
            "readelf": "GNU readelf (GNU Binutils for Debian) 2.44",
        },
        "mapped_file": (
            "arch/riscv/kernel/vdso/vdso.so -- the stripped image. "
            "arch/riscv/kernel/vdso/vdso.S does .incbin of this path, and "
            "arch/riscv/kernel/vdso.c maps the bytes between vdso_start and "
            "vdso_end. The unstripped vdso.so.dbg is not mapped."
        ),
        "configurations": [
            {
                "name": "defconfig",
                "config_commands": [
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 defconfig",
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 olddefconfig",
                ],
                "config_delta_from_defconfig": [],
                "make_commands": [
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 -j32 prepare",
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c0 -j32 arch/riscv/kernel/vdso/",
                ],
            },
            {
                "name": "defconfig + CONFIG_TRANSPARENT_HUGEPAGE=y",
                "config_commands": [
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 defconfig",
                    "./scripts/config --file /out/c1/.config -e TRANSPARENT_HUGEPAGE",
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 olddefconfig",
                ],
                "config_delta_from_defconfig": [
                    "-# CONFIG_TRANSPARENT_HUGEPAGE is not set",
                    "+CONFIG_TRANSPARENT_HUGEPAGE=y",
                    "+CONFIG_TRANSPARENT_HUGEPAGE_ALWAYS=y",
                    "+# CONFIG_TRANSPARENT_HUGEPAGE_MADVISE is not set",
                    "+# CONFIG_TRANSPARENT_HUGEPAGE_NEVER is not set",
                    "+# CONFIG_PERSISTENT_HUGE_ZERO_FOLIO is not set",
                    "+CONFIG_MM_ID=y",
                    "+CONFIG_THP_SWAP=y",
                    "+# CONFIG_READ_ONLY_THP_FOR_FS is not set",
                    "+# CONFIG_NO_PAGE_MAPCOUNT is not set",
                    "+CONFIG_ARCH_SUPPORTS_HUGE_PFNMAP=y",
                    "+CONFIG_ARCH_SUPPORTS_PMD_PFNMAP=y",
                    "+CONFIG_ARCH_SUPPORTS_PUD_PFNMAP=y",
                    "+# CONFIG_DEV_DAX is not set",
                ],
                "make_commands": [
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 -j32 prepare",
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c1 -j32 arch/riscv/kernel/vdso/",
                ],
            },
            {
                "name": "defconfig + no randomisation",
                "config_commands": [
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 defconfig",
                    "./scripts/config --file /out/c2/.config -e COMPAT_BRK -d RANDOMIZE_BASE -d RANDOMIZE_KSTACK_OFFSET",
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 olddefconfig",
                ],
                "config_delta_from_defconfig": [],
                "config_note": (
                    "The .config of this configuration is byte-identical to the "
                    "defconfig .config. riscv defconfig already sets "
                    "CONFIG_COMPAT_BRK=y (no brk randomisation) and leaves "
                    "CONFIG_RANDOMIZE_BASE unset. CONFIG_RANDOMIZE_KSTACK_OFFSET "
                    "stays y because arch/riscv selects it. There is no Kconfig "
                    "option for vDSO or mmap randomisation; norandmaps is a boot "
                    "parameter."
                ),
                "make_commands": [
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 -j32 prepare",
                    "make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O=/out/c2 -j32 arch/riscv/kernel/vdso/",
                ],
            },
        ],
        "note": (
            "All three configurations give the same bytes. The vDSO image does "
            "not depend on CONFIG_TRANSPARENT_HUGEPAGE, and the no-randomisation "
            "configuration has the same .config as defconfig. There is one "
            "distinct image, not three."
        ),
    }
}

# readelf --dyn-syms -V output of each known image, for the cross-check.
READELF_RECORDS = {
    "0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36": """
Symbol table '.dynsym' contains 11 entries:
   Num:    Value          Size Type    Bind   Vis      Ndx Name
     0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND
     1: 0000000000000498     0 SECTION LOCAL  DEFAULT    7 .rodata
     2: 0000000000000870   500 FUNC    GLOBAL DEFAULT   11 __vdso_gettimeofday@@LINUX_4.15
     3: 0000000000000a64   144 FUNC    GLOBAL DEFAULT   11 __vdso_clock_getres@@LINUX_4.15
     4: 0000000000000000     0 OBJECT  GLOBAL DEFAULT  ABS LINUX_4.15
     5: 0000000000000b10   284 FUNC    GLOBAL DEFAULT   11 __vdso_riscv_hwprobe@@LINUX_4.15
     6: 0000000000000c3c   552 FUNC    GLOBAL DEFAULT   11 __vdso_getrandom@@LINUX_4.15
     7: 0000000000000590     8 FUNC    GLOBAL DEFAULT   11 __vdso_rt_sigreturn@@LINUX_4.15
     8: 00000000000005b4   698 FUNC    GLOBAL DEFAULT   11 __vdso_clock_gettime@@LINUX_4.15
     9: 0000000000000b04    10 FUNC    GLOBAL DEFAULT   11 __vdso_flush_icache@@LINUX_4.15
    10: 0000000000000af8    10 FUNC    GLOBAL DEFAULT   11 __vdso_getcpu@@LINUX_4.15

Version symbols section '.gnu.version' contains 11 entries:
 Addr: 0x0000000000000326  Offset: 0x00000326  Link: 2 (.dynsym)
  000:   0 (*local*)       0 (*local*)       2 (LINUX_4.15)    2 (LINUX_4.15)
  004:   2 (LINUX_4.15)    2 (LINUX_4.15)    2 (LINUX_4.15)    2 (LINUX_4.15)
  008:   2 (LINUX_4.15)    2 (LINUX_4.15)    2 (LINUX_4.15)

Version definition section '.gnu.version_d' contains 2 entries:
 Addr: 0x0000000000000340  Offset: 0x00000340  Link: 3 (.dynstr)
  000000: Rev: 1  Flags: BASE  Index: 1  Cnt: 1  Name: linux-vdso.so.1
  0x001c: Rev: 1  Flags: none  Index: 2  Cnt: 1  Name: LINUX_4.15
"""
}

# --------------------------------------------------------------------------
# ELF constants
# --------------------------------------------------------------------------

PT_NAMES = {
    0: "PT_NULL", 1: "PT_LOAD", 2: "PT_DYNAMIC", 3: "PT_INTERP", 4: "PT_NOTE",
    5: "PT_SHLIB", 6: "PT_PHDR", 7: "PT_TLS",
    0x6474e550: "PT_GNU_EH_FRAME", 0x6474e551: "PT_GNU_STACK",
    0x6474e552: "PT_GNU_RELRO", 0x6474e553: "PT_GNU_PROPERTY",
}

DT_NAMES = {
    0: "DT_NULL", 1: "DT_NEEDED", 2: "DT_PLTRELSZ", 3: "DT_PLTGOT",
    4: "DT_HASH", 5: "DT_STRTAB", 6: "DT_SYMTAB", 7: "DT_RELA",
    8: "DT_RELASZ", 9: "DT_RELAENT", 10: "DT_STRSZ", 11: "DT_SYMENT",
    12: "DT_INIT", 13: "DT_FINI", 14: "DT_SONAME", 15: "DT_RPATH",
    16: "DT_SYMBOLIC", 17: "DT_REL", 18: "DT_RELSZ", 19: "DT_RELENT",
    20: "DT_PLTREL", 21: "DT_DEBUG", 22: "DT_TEXTREL", 23: "DT_JMPREL",
    24: "DT_BIND_NOW", 30: "DT_FLAGS",
    0x6ffffef5: "DT_GNU_HASH", 0x6ffffff0: "DT_VERSYM",
    0x6ffffffc: "DT_VERDEF", 0x6ffffffd: "DT_VERDEFNUM",
    0x6ffffffe: "DT_VERNEED", 0x6fffffff: "DT_VERNEEDNUM",
    0x6ffffff9: "DT_RELACOUNT", 0x6ffffffb: "DT_FLAGS_1",
}

STT_NAMES = {0: "STT_NOTYPE", 1: "STT_OBJECT", 2: "STT_FUNC", 3: "STT_SECTION",
             4: "STT_FILE", 6: "STT_TLS"}
STB_NAMES = {0: "STB_LOCAL", 1: "STB_GLOBAL", 2: "STB_WEAK"}


def pflags_text(flags: int) -> str:
    return ("R" if flags & 4 else "") + ("W" if flags & 2 else "") + ("X" if flags & 1 else "")


# --------------------------------------------------------------------------
# ELF reader
# --------------------------------------------------------------------------


class Elf:
    """A little-endian 64-bit ELF image held in memory."""

    def __init__(self, data: bytes):
        self.data = data
        if data[:4] != b"\x7fELF":
            raise ValueError("not an ELF file")
        if data[4] != 2 or data[5] != 1:
            raise ValueError("not a little-endian 64-bit ELF file")
        (self.e_type, self.e_machine, self.e_version, self.e_entry,
         self.e_phoff, self.e_shoff, self.e_flags, self.e_ehsize,
         self.e_phentsize, self.e_phnum, self.e_shentsize, self.e_shnum,
         self.e_shstrndx) = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
        self.phdrs = []
        for i in range(self.e_phnum):
            off = self.e_phoff + i * self.e_phentsize
            (p_type, p_flags, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz,
             p_align) = struct.unpack_from("<IIQQQQQQ", data, off)
            self.phdrs.append({
                "index": i,
                "p_type": p_type,
                "p_type_name": PT_NAMES.get(p_type, hex(p_type)),
                "p_flags": p_flags,
                "p_flags_text": pflags_text(p_flags),
                "p_offset": p_offset,
                "p_vaddr": p_vaddr,
                "p_paddr": p_paddr,
                "p_filesz": p_filesz,
                "p_memsz": p_memsz,
                "p_align": p_align,
            })

    def loads(self):
        return [p for p in self.phdrs if p["p_type"] == 1]

    def vaddr_to_off(self, vaddr: int) -> int:
        """Map a virtual address to a file offset through the PT_LOAD headers."""
        for p in self.loads():
            if p["p_vaddr"] <= vaddr < p["p_vaddr"] + p["p_filesz"]:
                return p["p_offset"] + (vaddr - p["p_vaddr"])
        raise ValueError("vaddr 0x%x is in no PT_LOAD segment" % vaddr)

    def cstr(self, off: int) -> str:
        end = self.data.index(b"\0", off)
        return self.data[off:end].decode("utf-8", "replace")


def read_dynamic(elf: Elf):
    """Read PT_DYNAMIC the way musl's __vdsosym does."""
    dyn = None
    for p in elf.phdrs:
        if p["p_type"] == 2:
            dyn = p
    if dyn is None:
        raise ValueError("no PT_DYNAMIC segment")
    entries = []
    off = dyn["p_offset"]
    end = off + dyn["p_filesz"]
    tags = {}
    while off + 16 <= end:
        d_tag, d_val = struct.unpack_from("<qQ", elf.data, off)
        entries.append({
            "d_tag": d_tag,
            "d_tag_name": DT_NAMES.get(d_tag & 0xFFFFFFFFFFFFFFFF, DT_NAMES.get(d_tag, hex(d_tag))),
            "d_val": d_val,
        })
        if d_tag == 0:
            break
        tags.setdefault(d_tag, d_val)
        off += 16
    return dyn, entries, tags


DT_HASH = 4
DT_STRTAB = 5
DT_SYMTAB = 6
DT_SYMENT = 11
DT_GNU_HASH = 0x6FFFFEF5
DT_VERSYM = 0x6FFFFFF0
DT_VERDEF = 0x6FFFFFFC


def count_symbols(elf: Elf, tags):
    """Count dynamic symbols as musl does: DT_HASH first, else DT_GNU_HASH."""
    if DT_HASH in tags:
        off = elf.vaddr_to_off(tags[DT_HASH])
        nbucket, nchain = struct.unpack_from("<II", elf.data, off)
        return nchain, "DT_HASH", {"nbucket": nbucket, "nchain": nchain}
    if DT_GNU_HASH in tags:
        off = elf.vaddr_to_off(tags[DT_GNU_HASH])
        nbuckets, symoffset, bloom_size, _shift = struct.unpack_from("<IIII", elf.data, off)
        buckets_off = off + 16 + bloom_size * 8
        last = 0
        for i in range(nbuckets):
            b = struct.unpack_from("<I", elf.data, buckets_off + 4 * i)[0]
            if b > last:
                last = b
        if last < symoffset:
            return symoffset, "DT_GNU_HASH", {"nbuckets": nbuckets, "symoffset": symoffset}
        chain_off = buckets_off + 4 * nbuckets
        i = last
        while True:
            h = struct.unpack_from("<I", elf.data, chain_off + 4 * (i - symoffset))[0]
            i += 1
            if h & 1:
                break
        return i, "DT_GNU_HASH", {"nbuckets": nbuckets, "symoffset": symoffset}
    raise ValueError("neither DT_HASH nor DT_GNU_HASH is present")


def version_names(elf: Elf, tags):
    """Read .gnu.version_d: version index -> version name."""
    out = {}
    if DT_VERDEF not in tags:
        return out
    off = elf.vaddr_to_off(tags[DT_VERDEF])
    while True:
        (vd_version, vd_flags, vd_ndx, vd_cnt, vd_hash, vd_aux,
         vd_next) = struct.unpack_from("<HHHHIII", elf.data, off)
        aux = off + vd_aux
        for _ in range(vd_cnt):
            vda_name, vda_next = struct.unpack_from("<II", elf.data, aux)
            name = elf.cstr(elf.vaddr_to_off(tags[DT_STRTAB]) + vda_name)
            out.setdefault(vd_ndx, {"name": name, "flags": vd_flags, "base": bool(vd_flags & 1)})
            if vda_next == 0:
                break
            aux += vda_next
        if vd_next == 0:
            break
        off += vd_next
    return out


def read_dynsyms(elf: Elf, tags, nsyms):
    strtab = elf.vaddr_to_off(tags[DT_STRTAB])
    symtab = elf.vaddr_to_off(tags[DT_SYMTAB])
    syment = tags.get(DT_SYMENT, 24)
    versym_off = elf.vaddr_to_off(tags[DT_VERSYM]) if DT_VERSYM in tags else None
    vnames = version_names(elf, tags)
    syms = []
    for i in range(nsyms):
        off = symtab + i * syment
        st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
            "<IBBHQQ", elf.data, off)
        ver_index = None
        ver_name = None
        hidden = False
        if versym_off is not None:
            raw = struct.unpack_from("<H", elf.data, versym_off + 2 * i)[0]
            ver_index = raw & 0x7FFF
            hidden = bool(raw & 0x8000)
            if ver_index in vnames:
                ver_name = vnames[ver_index]["name"]
            elif ver_index == 0:
                ver_name = "*local*"
            elif ver_index == 1:
                ver_name = "*global*"
        syms.append({
            "index": i,
            "name": elf.cstr(strtab + st_name),
            "st_value": st_value,
            "st_size": st_size,
            "st_info": st_info,
            "st_type": STT_NAMES.get(st_info & 0xF, st_info & 0xF),
            "st_bind": STB_NAMES.get(st_info >> 4, st_info >> 4),
            "st_other": st_other,
            "st_shndx": st_shndx,
            "version_index": ver_index,
            "version": ver_name,
            "version_hidden": hidden,
        })
    return syms, vnames


# --------------------------------------------------------------------------
# RV64GC decoder
# --------------------------------------------------------------------------

XNAMES = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1",
          "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
          "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
          "t3", "t4", "t5", "t6"]

CALLEE_SAVED = {2, 3, 4, 8, 9} | set(range(18, 28))  # sp, gp, tp, s0, s1, s2-s11


def sx(value: int, bits: int) -> int:
    mask = 1 << (bits - 1)
    return (value ^ mask) - mask


def bits(word: int, hi: int, lo: int) -> int:
    return (word >> lo) & ((1 << (hi - lo + 1)) - 1)


class Insn(dict):
    """One decoded instruction."""


def _i(addr, length, kind, text, **kw) -> Insn:
    ins = Insn(addr=addr, len=length, kind=kind, text=text,
               rd=None, rs1=None, rs2=None, imm=None, target=None)
    ins.update(kw)
    return ins


LOAD_W = {0: "lb", 1: "lh", 2: "lw", 3: "ld", 4: "lbu", 5: "lhu", 6: "lwu"}
STORE_W = {0: "sb", 1: "sh", 2: "sw", 3: "sd"}
OPIMM = {0: "addi", 1: "slli", 2: "slti", 3: "sltiu", 4: "xori", 5: "srli/srai",
         6: "ori", 7: "andi"}
OP = {0: "add/sub", 1: "sll", 2: "slt", 3: "sltu", 4: "xor", 5: "srl/sra",
      6: "or", 7: "and"}
MULDIV = {0: "mul", 1: "mulh", 2: "mulhsu", 3: "mulhu", 4: "div", 5: "divu",
          6: "rem", 7: "remu"}


def decode32(w: int, addr: int) -> Insn:
    op = w & 0x7F
    rd = bits(w, 11, 7)
    f3 = bits(w, 14, 12)
    rs1 = bits(w, 19, 15)
    rs2 = bits(w, 24, 20)
    f7 = bits(w, 31, 25)
    if op == 0x37:
        imm = sx(w & 0xFFFFF000, 32)
        return _i(addr, 4, "lui", "lui %s,0x%x" % (XNAMES[rd], (w >> 12) & 0xFFFFF), rd=rd, imm=imm)
    if op == 0x17:
        imm = sx(w & 0xFFFFF000, 32)
        return _i(addr, 4, "auipc", "auipc %s,0x%x" % (XNAMES[rd], (w >> 12) & 0xFFFFF),
                  rd=rd, imm=imm)
    if op == 0x6F:
        imm = sx((bits(w, 31, 31) << 20) | (bits(w, 19, 12) << 12) |
                 (bits(w, 20, 20) << 11) | (bits(w, 30, 21) << 1), 21)
        kind = "call" if rd != 0 else "jump"
        return _i(addr, 4, kind, "jal %s,%x" % (XNAMES[rd], addr + imm),
                  rd=rd, imm=imm, target=addr + imm)
    if op == 0x67:
        imm = sx(bits(w, 31, 20), 12)
        if rd == 0 and rs1 == 1 and imm == 0:
            return _i(addr, 4, "ret", "ret")
        kind = "icall" if rd != 0 else "ijump"
        return _i(addr, 4, kind, "jalr %s,%d(%s)" % (XNAMES[rd], imm, XNAMES[rs1]),
                  rd=rd, rs1=rs1, imm=imm)
    if op == 0x63:
        imm = sx((bits(w, 31, 31) << 12) | (bits(w, 7, 7) << 11) |
                 (bits(w, 30, 25) << 5) | (bits(w, 11, 8) << 1), 13)
        names = {0: "beq", 1: "bne", 4: "blt", 5: "bge", 6: "bltu", 7: "bgeu"}
        return _i(addr, 4, "branch", "%s %s,%s,%x" % (names.get(f3, "b?"), XNAMES[rs1],
                                                      XNAMES[rs2], addr + imm),
                  rs1=rs1, rs2=rs2, imm=imm, target=addr + imm)
    if op == 0x03:
        imm = sx(bits(w, 31, 20), 12)
        return _i(addr, 4, "load", "%s %s,%d(%s)" % (LOAD_W.get(f3, "l?"), XNAMES[rd], imm,
                                                     XNAMES[rs1]),
                  rd=rd, rs1=rs1, imm=imm, width=1 << (f3 & 3))
    if op == 0x23:
        imm = sx((f7 << 5) | rd, 12)
        return _i(addr, 4, "store", "%s %s,%d(%s)" % (STORE_W.get(f3, "s?"), XNAMES[rs2], imm,
                                                      XNAMES[rs1]),
                  rs1=rs1, rs2=rs2, imm=imm, width=1 << (f3 & 3))
    if op == 0x07:
        imm = sx(bits(w, 31, 20), 12)
        return _i(addr, 4, "fload", "fload f%d,%d(%s)" % (rd, imm, XNAMES[rs1]), rs1=rs1, imm=imm)
    if op == 0x27:
        imm = sx((f7 << 5) | rd, 12)
        return _i(addr, 4, "store", "fstore f%d,%d(%s)" % (rs2, imm, XNAMES[rs1]),
                  rs1=rs1, rs2=None, imm=imm, width=8, fp=True)
    if op == 0x13:
        imm = sx(bits(w, 31, 20), 12)
        name = OPIMM[f3]
        if f3 in (1, 5):
            imm = bits(w, 25, 20)
            name = "slli" if f3 == 1 else ("srai" if f7 & 0x20 else "srli")
        return _i(addr, 4, "opimm", "%s %s,%s,%d" % (name, XNAMES[rd], XNAMES[rs1], imm),
                  rd=rd, rs1=rs1, imm=imm, op=name)
    if op == 0x1B:
        imm = sx(bits(w, 31, 20), 12)
        name = "addiw" if f3 == 0 else ("slliw" if f3 == 1 else "sr_iw")
        if f3 in (1, 5):
            imm = bits(w, 24, 20)
        return _i(addr, 4, "opimm32", "%s %s,%s,%d" % (name, XNAMES[rd], XNAMES[rs1], imm),
                  rd=rd, rs1=rs1, imm=imm, op=name)
    if op in (0x33, 0x3B):
        if f7 == 1:
            name = MULDIV[f3] + ("w" if op == 0x3B else "")
        elif f7 == 0x20:
            name = "sub" if f3 == 0 else "sra"
        else:
            name = OP[f3]
        return _i(addr, 4, "op", "%s %s,%s,%s" % (name, XNAMES[rd], XNAMES[rs1], XNAMES[rs2]),
                  rd=rd, rs1=rs1, rs2=rs2, op=name)
    if op == 0x0F:
        return _i(addr, 4, "fence", "fence")
    if op == 0x73:
        if w == 0x73:
            return _i(addr, 4, "ecall", "ecall")
        if w == 0x100073:
            return _i(addr, 4, "ebreak", "ebreak")
        return _i(addr, 4, "csr", "csr %s" % XNAMES[rd], rd=rd, rs1=rs1)
    if op == 0x2F:
        return _i(addr, 4, "amo", "amo", rd=rd, rs1=rs1, rs2=rs2, width=1 << (f3 & 3),
                  imm=0, is_store=True)
    return _i(addr, 4, "unknown", "unknown .word 0x%08x" % w)


def decode16(w: int, addr: int) -> Insn:
    q = w & 3
    f3 = bits(w, 15, 13)
    rdp = 8 + bits(w, 4, 2)
    rs1p = 8 + bits(w, 9, 7)
    rd = bits(w, 11, 7)
    rs2 = bits(w, 6, 2)
    if w == 0:
        return _i(addr, 2, "unknown", "illegal")
    if q == 0:
        if f3 == 0:  # c.addi4spn
            imm = (bits(w, 10, 7) << 6) | (bits(w, 12, 11) << 4) | (bits(w, 5, 5) << 3) | \
                  (bits(w, 6, 6) << 2)
            return _i(addr, 2, "opimm", "addi %s,sp,%d" % (XNAMES[rdp], imm),
                      rd=rdp, rs1=2, imm=imm, op="addi")
        if f3 in (1, 2, 3):  # c.fld, c.lw, c.ld
            if f3 == 2:
                imm = (bits(w, 5, 5) << 6) | (bits(w, 12, 10) << 3) | (bits(w, 6, 6) << 2)
                return _i(addr, 2, "load", "lw %s,%d(%s)" % (XNAMES[rdp], imm, XNAMES[rs1p]),
                          rd=rdp, rs1=rs1p, imm=imm, width=4)
            imm = (bits(w, 6, 5) << 6) | (bits(w, 12, 10) << 3)
            if f3 == 3:
                return _i(addr, 2, "load", "ld %s,%d(%s)" % (XNAMES[rdp], imm, XNAMES[rs1p]),
                          rd=rdp, rs1=rs1p, imm=imm, width=8)
            return _i(addr, 2, "fload", "fld f%d,%d(%s)" % (rdp, imm, XNAMES[rs1p]),
                      rs1=rs1p, imm=imm)
        if f3 in (5, 6, 7):  # c.fsd, c.sw, c.sd
            if f3 == 6:
                imm = (bits(w, 5, 5) << 6) | (bits(w, 12, 10) << 3) | (bits(w, 6, 6) << 2)
                return _i(addr, 2, "store", "sw %s,%d(%s)" % (XNAMES[rdp], imm, XNAMES[rs1p]),
                          rs1=rs1p, rs2=rdp, imm=imm, width=4)
            imm = (bits(w, 6, 5) << 6) | (bits(w, 12, 10) << 3)
            if f3 == 7:
                return _i(addr, 2, "store", "sd %s,%d(%s)" % (XNAMES[rdp], imm, XNAMES[rs1p]),
                          rs1=rs1p, rs2=rdp, imm=imm, width=8)
            return _i(addr, 2, "store", "fsd f%d,%d(%s)" % (rdp, imm, XNAMES[rs1p]),
                      rs1=rs1p, rs2=None, imm=imm, width=8, fp=True)
        return _i(addr, 2, "unknown", "c.unknown 0x%04x" % w)
    if q == 1:
        if f3 == 0:
            imm = sx((bits(w, 12, 12) << 5) | rs2, 6)
            if rd == 0:
                return _i(addr, 2, "nop", "nop")
            return _i(addr, 2, "opimm", "addi %s,%s,%d" % (XNAMES[rd], XNAMES[rd], imm),
                      rd=rd, rs1=rd, imm=imm, op="addi")
        if f3 == 1:
            imm = sx((bits(w, 12, 12) << 5) | rs2, 6)
            return _i(addr, 2, "opimm32", "addiw %s,%s,%d" % (XNAMES[rd], XNAMES[rd], imm),
                      rd=rd, rs1=rd, imm=imm, op="addiw")
        if f3 == 2:
            imm = sx((bits(w, 12, 12) << 5) | rs2, 6)
            return _i(addr, 2, "opimm", "li %s,%d" % (XNAMES[rd], imm),
                      rd=rd, rs1=0, imm=imm, op="addi")
        if f3 == 3:
            if rd == 2:  # c.addi16sp
                imm = sx((bits(w, 12, 12) << 9) | (bits(w, 4, 3) << 7) |
                         (bits(w, 5, 5) << 6) | (bits(w, 2, 2) << 5) |
                         (bits(w, 6, 6) << 4), 10)
                return _i(addr, 2, "opimm", "addi sp,sp,%d" % imm,
                          rd=2, rs1=2, imm=imm, op="addi")
            imm = sx((bits(w, 12, 12) << 17) | (rs2 << 12), 18)
            return _i(addr, 2, "lui", "lui %s,0x%x" % (XNAMES[rd], (imm >> 12) & 0xFFFFF),
                      rd=rd, imm=imm)
        if f3 == 4:
            f2 = bits(w, 11, 10)
            if f2 in (0, 1):
                sh = (bits(w, 12, 12) << 5) | rs2
                return _i(addr, 2, "opimm", "%s %s,%s,%d" % ("srli" if f2 == 0 else "srai",
                                                             XNAMES[rs1p], XNAMES[rs1p], sh),
                          rd=rs1p, rs1=rs1p, imm=sh, op="srli" if f2 == 0 else "srai")
            if f2 == 2:
                imm = sx((bits(w, 12, 12) << 5) | rs2, 6)
                return _i(addr, 2, "opimm", "andi %s,%s,%d" % (XNAMES[rs1p], XNAMES[rs1p], imm),
                          rd=rs1p, rs1=rs1p, imm=imm, op="andi")
            rs2p = 8 + bits(w, 4, 2)
            sel = bits(w, 6, 5)
            if bits(w, 12, 12) == 0:
                name = ["sub", "xor", "or", "and"][sel]
            else:
                name = ["subw", "addw", "?", "?"][sel]
            return _i(addr, 2, "op", "%s %s,%s,%s" % (name, XNAMES[rs1p], XNAMES[rs1p],
                                                      XNAMES[rs2p]),
                      rd=rs1p, rs1=rs1p, rs2=rs2p, op=name)
        if f3 == 5:
            imm = sx((bits(w, 12, 12) << 11) | (bits(w, 8, 8) << 10) |
                     (bits(w, 10, 9) << 8) | (bits(w, 6, 6) << 7) |
                     (bits(w, 7, 7) << 6) | (bits(w, 2, 2) << 5) |
                     (bits(w, 11, 11) << 4) | (bits(w, 5, 3) << 1), 12)
            return _i(addr, 2, "jump", "j %x" % (addr + imm), imm=imm, target=addr + imm)
        if f3 in (6, 7):
            imm = sx((bits(w, 12, 12) << 8) | (bits(w, 6, 5) << 6) |
                     (bits(w, 2, 2) << 5) | (bits(w, 11, 10) << 3) |
                     (bits(w, 4, 3) << 1), 9)
            name = "beqz" if f3 == 6 else "bnez"
            return _i(addr, 2, "branch", "%s %s,%x" % (name, XNAMES[rs1p], addr + imm),
                      rs1=rs1p, rs2=0, imm=imm, target=addr + imm)
    if q == 2:
        if f3 == 0:
            sh = (bits(w, 12, 12) << 5) | rs2
            return _i(addr, 2, "opimm", "slli %s,%s,%d" % (XNAMES[rd], XNAMES[rd], sh),
                      rd=rd, rs1=rd, imm=sh, op="slli")
        if f3 in (1, 2, 3):
            if f3 == 2:  # c.lwsp
                imm = (bits(w, 3, 2) << 6) | (bits(w, 12, 12) << 5) | (bits(w, 6, 4) << 2)
                return _i(addr, 2, "load", "lw %s,%d(sp)" % (XNAMES[rd], imm),
                          rd=rd, rs1=2, imm=imm, width=4)
            imm = (bits(w, 4, 2) << 6) | (bits(w, 12, 12) << 5) | (bits(w, 6, 5) << 3)
            if f3 == 3:  # c.ldsp
                return _i(addr, 2, "load", "ld %s,%d(sp)" % (XNAMES[rd], imm),
                          rd=rd, rs1=2, imm=imm, width=8)
            return _i(addr, 2, "fload", "fld f%d,%d(sp)" % (rd, imm), rs1=2, imm=imm)
        if f3 == 4:
            if bits(w, 12, 12) == 0:
                if rs2 == 0:
                    if rd == 1:
                        return _i(addr, 2, "ret", "ret")
                    return _i(addr, 2, "ijump", "jr %s" % XNAMES[rd], rs1=rd)
                return _i(addr, 2, "op", "mv %s,%s" % (XNAMES[rd], XNAMES[rs2]),
                          rd=rd, rs1=0, rs2=rs2, op="add")
            if rs2 == 0:
                if rd == 0:
                    return _i(addr, 2, "ebreak", "ebreak")
                return _i(addr, 2, "icall", "jalr %s" % XNAMES[rd], rd=1, rs1=rd)
            return _i(addr, 2, "op", "add %s,%s,%s" % (XNAMES[rd], XNAMES[rd], XNAMES[rs2]),
                      rd=rd, rs1=rd, rs2=rs2, op="add")
        if f3 in (5, 6, 7):
            if f3 == 6:  # c.swsp
                imm = (bits(w, 8, 7) << 6) | (bits(w, 12, 9) << 2)
                return _i(addr, 2, "store", "sw %s,%d(sp)" % (XNAMES[rs2], imm),
                          rs1=2, rs2=rs2, imm=imm, width=4)
            imm = (bits(w, 9, 7) << 6) | (bits(w, 12, 10) << 3)
            if f3 == 7:  # c.sdsp
                return _i(addr, 2, "store", "sd %s,%d(sp)" % (XNAMES[rs2], imm),
                          rs1=2, rs2=rs2, imm=imm, width=8)
            return _i(addr, 2, "store", "fsd f%d,%d(sp)" % (rs2, imm),
                      rs1=2, rs2=None, imm=imm, width=8, fp=True)
    return _i(addr, 2, "unknown", "c.unknown 0x%04x" % w)


def decode_at(elf: Elf, vaddr: int) -> Insn:
    off = elf.vaddr_to_off(vaddr)
    half = struct.unpack_from("<H", elf.data, off)[0]
    if (half & 3) == 3:
        word = struct.unpack_from("<I", elf.data, off)[0]
        return decode32(word, vaddr)
    return decode16(half, vaddr)


# --------------------------------------------------------------------------
# Control-flow walk of one function
# --------------------------------------------------------------------------

TERMINATORS = {"ret", "jump", "ijump"}


def walk_function(elf: Elf, entry: int, text_lo: int, text_hi: int, end: int):
    """Walk the control-flow graph of the function at `entry`.

    Returns the decoded instructions, the called addresses, and the state of
    sp and of the callee-saved registers at every `ret`.
    """
    insns = {}
    # state at the start of a block: (sp_delta, frozenset of clobbered callee-saved,
    #                                 saved-slot map, taint map)
    start_state = (0, frozenset(), (), {})
    todo = [(entry, start_state)]
    seen = {}
    calls = set()
    rets = []
    stores = []
    problems = []
    min_sp = 0

    def taint_of(regs, r):
        return regs.get(r, "unknown")

    while todo:
        addr, state = todo.pop()
        sp_delta, clobbered, slots, regs_in = state
        key = (addr, sp_delta, clobbered, slots)
        if key in seen:
            continue
        seen[key] = True
        regs = dict(regs_in)
        if addr == entry:
            regs = {r: "arg" for r in range(10, 18)}
            regs[2] = "sp"
            regs[1] = "ra"
        clob = set(clobbered)
        slotmap = dict(slots)
        pc = addr
        guard = 0
        while True:
            guard += 1
            if guard > 20000:
                problems.append("walk at 0x%x did not terminate" % addr)
                break
            if not (text_lo <= pc < text_hi):
                problems.append("control flow leaves the image at 0x%x" % pc)
                break
            if pc >= end:
                # The walk ran off the end of the function. The last
                # instruction before it does not return (an ecall that the
                # kernel does not come back from), or the bytes after it are
                # padding.
                break
            ins = decode_at(elf, pc)
            insns[pc] = ins
            kind = ins["kind"]

            # sp tracking
            if kind == "opimm" and ins.get("op") == "addi" and ins["rd"] == 2 and ins["rs1"] == 2:
                sp_delta += ins["imm"]
                if sp_delta < min_sp:
                    min_sp = sp_delta
            elif ins["rd"] == 2 and kind not in ("branch", "store", "jump", "ret"):
                if not (kind == "opimm" and ins.get("op") == "addi" and ins["rs1"] == 2):
                    problems.append("sp written by a non-addi at 0x%x: %s" % (pc, ins["text"]))

            # callee-saved save and restore
            if kind == "store" and ins["rs1"] in (2, 8) and ins.get("rs2") is not None:
                base = "sp" if ins["rs1"] == 2 else "s0"
                slot = None
                if base == "sp":
                    slot = sp_delta + ins["imm"]
                elif "fp" in slotmap:
                    slot = slotmap["fp"] + ins["imm"]
                if ins["rs2"] in CALLEE_SAVED and ins["rs2"] not in clob and slot is not None:
                    slotmap[("save", ins["rs2"])] = slot
            if kind == "load" and ins["rd"] in CALLEE_SAVED and ins["rs1"] in (2, 8):
                slot = None
                if ins["rs1"] == 2:
                    slot = sp_delta + ins["imm"]
                elif "fp" in slotmap:
                    slot = slotmap["fp"] + ins["imm"]
                if slot is not None and slotmap.get(("save", ins["rd"])) == slot:
                    clob.discard(ins["rd"])
                else:
                    clob.add(ins["rd"])
            elif ins["rd"] is not None and ins["rd"] in CALLEE_SAVED and ins["rd"] != 2:
                # s0 = sp + k keeps the frame pointer; it is still a clobber
                clob.add(ins["rd"])
                if ins["rd"] == 8 and kind == "opimm" and ins.get("op") == "addi" \
                        and ins["rs1"] == 2:
                    slotmap["fp"] = sp_delta + ins["imm"]

            # taint
            if kind == "store":
                base = ins["rs1"]
                btaint = taint_of(regs, base)
                slot = None
                if base == 2:
                    btaint = "sp"
                    slot = sp_delta + ins["imm"]
                elif base == 8 and "fp" in slotmap:
                    btaint = "frame"
                    slot = slotmap["fp"] + ins["imm"]
                if slot is not None:
                    # Remember what kind of value the frame slot now holds, so
                    # that a reload of a spilled argument pointer is still an
                    # argument pointer.
                    slotmap[("val", slot)] = (taint_of(regs, ins["rs2"])
                                              if ins.get("rs2") else "const")
                stores.append({
                    "addr": "0x%x" % pc,
                    "text": ins["text"],
                    "base_reg": XNAMES[base],
                    "base_kind": btaint,
                    "sp_delta": sp_delta,
                    "slot": slot,
                    "width": ins.get("width", 8),
                })
            if ins["rd"] is not None and ins["rd"] != 0 and kind not in ("branch", "store"):
                if kind == "auipc":
                    regs[ins["rd"]] = "pc_relative"
                elif kind == "lui":
                    regs[ins["rd"]] = "const"
                elif kind in ("load", "fload"):
                    lslot = None
                    if ins["rs1"] == 2:
                        lslot = sp_delta + ins["imm"]
                    elif ins["rs1"] == 8 and "fp" in slotmap:
                        lslot = slotmap["fp"] + ins["imm"]
                    regs[ins["rd"]] = slotmap.get(("val", lslot), "loaded") \
                        if lslot is not None else "loaded"
                elif kind in ("opimm", "opimm32", "op"):
                    a = taint_of(regs, ins["rs1"]) if ins["rs1"] else "const"
                    b = taint_of(regs, ins["rs2"]) if ins.get("rs2") else "const"
                    if ins["rd"] == 8 and ins["rs1"] == 2:
                        regs[8] = "frame"
                    elif "arg" in (a, b):
                        regs[ins["rd"]] = "arg"
                    elif "pc_relative" in (a, b):
                        regs[ins["rd"]] = "pc_relative"
                    elif "sp" in (a, b) or "frame" in (a, b):
                        regs[ins["rd"]] = "frame"
                    elif a == b:
                        regs[ins["rd"]] = a
                    else:
                        regs[ins["rd"]] = "unknown"
                elif kind in ("call", "icall"):
                    pass
                else:
                    regs[ins["rd"]] = "unknown"
            if kind in ("call", "icall"):
                for r in list(range(5, 8)) + list(range(10, 18)) + list(range(28, 32)):
                    regs[r] = "unknown"
                regs[1] = "ra"

            if kind == "call":
                calls.add(ins["target"])
            if kind == "icall":
                problems.append("indirect call at 0x%x: %s" % (pc, ins["text"]))

            if kind == "ret":
                rets.append({
                    "addr": "0x%x" % pc,
                    "sp_delta": sp_delta,
                    "clobbered_callee_saved": sorted(XNAMES[r] for r in clob),
                })
                break
            if kind == "ijump":
                problems.append("indirect jump at 0x%x: %s" % (pc, ins["text"]))
                break
            nxt_state = (sp_delta, frozenset(clob),
                         tuple(sorted(slotmap.items(), key=repr)), dict(regs))
            if kind == "jump":
                todo.append((ins["target"], nxt_state))
                break
            if kind == "branch":
                todo.append((ins["target"], nxt_state))
            pc += ins["len"]
    return {
        "insns": insns,
        "calls": sorted(calls),
        "rets": rets,
        "stores": stores,
        "problems": problems,
        "own_frame": -min_sp,
    }


def sp_evidence(walk):
    out = []
    for addr in sorted(walk["insns"]):
        ins = walk["insns"][addr]
        if ins["kind"] == "opimm" and ins.get("op") == "addi" and ins["rd"] == 2 \
                and ins["rs1"] == 2 and ins["imm"] < 0:
            out.append("0x%x: %s" % (addr, ins["text"]))
    return out


# --------------------------------------------------------------------------
# The measurement of one image
# --------------------------------------------------------------------------


def analyse_code(elf: Elf, exported):
    text_lo = min(p["p_vaddr"] for p in elf.loads())
    text_hi = max(p["p_vaddr"] + p["p_filesz"] for p in elf.loads())
    walks = {}
    order = []
    # The end of a function: its st_size when the symbol table gives one, else
    # the start of the next known function above it.
    bounds = {s["st_value"]: s["st_value"] + s["st_size"] for s in exported if s["st_size"]}
    starts = sorted(s["st_value"] for s in exported)

    def end_of(addr):
        if addr in bounds:
            return bounds[addr]
        above = [a for a in starts if a > addr]
        return min(above) if above else text_hi

    def ensure(addr):
        if addr in walks:
            return
        walks[addr] = None  # cycle guard
        w = walk_function(elf, addr, text_lo, text_hi, end_of(addr))
        walks[addr] = w
        order.append(addr)
        for c in w["calls"]:
            ensure(c)

    for s in exported:
        ensure(s["st_value"])

    names = {s["st_value"]: s["name"] for s in exported}
    for addr in list(walks):
        names.setdefault(addr, "sub_%x" % addr)

    def chain(addr, stack):
        if addr in stack:
            return None, [names[a] for a in stack] + [names[addr]]
        w = walks[addr]
        best = w["own_frame"]
        best_path = [names[addr]]
        for c in w["calls"]:
            sub, cyc = chain(c, stack + [addr])
            if sub is None:
                return None, cyc
            if w["own_frame"] + sub[0] > best:
                best = w["own_frame"] + sub[0]
                best_path = [names[addr]] + sub[1]
        return (best, best_path), None

    per_function = {}
    cycles = []
    for addr in sorted(walks):
        res, cyc = chain(addr, [])
        if res is None:
            cycles.append(cyc)
            per_function[names[addr]] = {"error": "recursion: %s" % " -> ".join(cyc)}
            continue
        w = walks[addr]
        per_function[names[addr]] = {
            "address": "0x%x" % addr,
            "exported": addr in {s["st_value"] for s in exported},
            "own_frame_bytes": w["own_frame"],
            "max_frame_bytes_with_callees": res[0],
            "deepest_chain": res[1],
            "calls": [names[c] for c in w["calls"]],
            "sp_instructions": sp_evidence(w),
            "return_instructions": len(w["rets"]),
            "problems": w["problems"],
        }

    exported_addrs = [s["st_value"] for s in exported]
    f_value = 0
    f_chain = []
    for a in exported_addrs:
        r = per_function[names[a]]
        if "max_frame_bytes_with_callees" in r and r["max_frame_bytes_with_callees"] > f_value:
            f_value = r["max_frame_bytes_with_callees"]
            f_chain = r["deepest_chain"]

    # Step 5: the callee-saved and memory-write report
    callee_report = {}
    for s in exported:
        a = s["st_value"]
        w = walks[a]
        bad_rets = [r for r in w["rets"]
                    if r["clobbered_callee_saved"] or r["sp_delta"] != 0]
        reachable = [a] + [c for c in w["calls"]]
        all_bad = list(bad_rets)
        for c in w["calls"]:
            for r in walks[c]["rets"]:
                if r["clobbered_callee_saved"] or r["sp_delta"] != 0:
                    all_bad.append(dict(r, function=names[c]))
        store_kinds = {}
        unknown_stores = []
        slot_lo = 0
        slot_hi = 0
        out_of_frame = []
        ecalls = []
        for fa in reachable:
            for st in walks[fa]["stores"]:
                store_kinds[st["base_kind"]] = store_kinds.get(st["base_kind"], 0) + 1
                if st["base_kind"] not in ("sp", "frame", "arg"):
                    unknown_stores.append(dict(st, function=names[fa]))
                if st["base_kind"] in ("sp", "frame") and st["slot"] is not None:
                    # The slot is an offset from the sp of the entry of that
                    # function; add the frames of the callers above it.
                    depth = 0 if fa == a else walks[a]["own_frame"]
                    lo = st["slot"] - depth
                    slot_lo = min(slot_lo, lo)
                    slot_hi = max(slot_hi, lo + st.get("width", 8))
                    if lo < -f_value or lo + st.get("width", 8) > 0:
                        out_of_frame.append(dict(st, function=names[fa]))
            for addr2, ins2 in sorted(walks[fa]["insns"].items()):
                if ins2["kind"] == "ecall":
                    ecalls.append("0x%x in %s" % (addr2, names[fa]))
        callee_report[s["name"]] = {
            "returns_to_caller": bool(w["rets"]),
            "returns": w["rets"],
            "callee_saved_left_clobbered_at_return": sorted(
                {r for ret in all_bad for r in ret.get("clobbered_callee_saved", [])}),
            "writes_callee_saved_without_restoring_it": bool(
                {r for ret in all_bad for r in ret.get("clobbered_callee_saved", [])}),
            "sp_restored_at_every_return": all(r["sp_delta"] == 0 for r in w["rets"]),
            "reachable_functions": [names[x] for x in reachable],
            "store_base_kinds": store_kinds,
            "frame_store_range_from_caller_sp": [slot_lo, slot_hi],
            "frame_stores_outside_F_window": out_of_frame,
            "stores_outside_frame_and_arguments": unknown_stores,
            "writes_only_frame_and_argument_buffers": not unknown_stores and not out_of_frame,
            "ecall_sites": ecalls,
            "problems": sorted(set(sum((walks[x]["problems"] for x in reachable), []))),
        }

    return {
        "largest_frame_bytes": f_value,
        "largest_frame_chain": f_chain,
        "recursion_found": cycles,
        "per_function": per_function,
        "callee_saved_report": callee_report,
    }


def parse_readelf(text):
    """Read the symbol lines of a readelf --dyn-syms output."""
    out = {}
    for line in text.splitlines():
        m = re.match(r"\s*(\d+):\s+([0-9a-f]+)\s+(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)",
                     line)
        if not m:
            continue
        name = m.group(8)
        if "@@" in name:
            base, ver = name.split("@@", 1)
        elif "@" in name:
            base, ver = name.split("@", 1)
        else:
            base, ver = name, None
        out[base] = {"st_value": int(m.group(2), 16), "st_size": int(m.group(3)),
                     "version": ver}
    return out


def measure(path):
    data = open(path, "rb").read()
    sha = hashlib.sha256(data).hexdigest()
    elf = Elf(data)
    dyn_ph, dyn_entries, tags = read_dynamic(elf)
    nsyms, count_src, count_detail = count_symbols(elf, tags)
    syms, vnames = read_dynsyms(elf, tags, nsyms)
    exported = [s for s in syms
                if s["st_type"] == "STT_FUNC" and s["st_bind"] in ("STB_GLOBAL", "STB_WEAK")
                and s["st_shndx"] not in (0,)]
    exported.sort(key=lambda s: s["st_value"])

    code = analyse_code(elf, exported)

    hexs = data.hex()
    chunks = [hexs[i:i + HEX_CHUNK_CHARS] for i in range(0, len(hexs), HEX_CHUNK_CHARS)]

    crosscheck = {"source": "riscv64-linux-gnu-readelf -W --dyn-syms -V"}
    if sha in READELF_RECORDS:
        ref = parse_readelf(READELF_RECORDS[sha])
        rows = []
        agree = True
        for s in exported:
            r = ref.get(s["name"])
            ok = (r is not None and r["st_value"] == s["st_value"]
                  and r["st_size"] == s["st_size"] and r["version"] == s["version"])
            agree = agree and ok
            rows.append({
                "name": s["name"],
                "parser_offset": s["st_value"],
                "readelf_offset": r["st_value"] if r else None,
                "parser_size": s["st_size"],
                "readelf_size": r["st_size"] if r else None,
                "parser_version": s["version"],
                "readelf_version": r["version"] if r else None,
                "agree": ok,
            })
        crosscheck["rows"] = rows
        crosscheck["agree"] = agree
        crosscheck["readelf_output"] = READELF_RECORDS[sha].strip("\n")
    else:
        crosscheck["agree"] = None
        crosscheck["note"] = "no recorded readelf output for this sha256"

    result = {
        "file": os.path.basename(path),
        "configuration": FILE_CONFIG.get(os.path.basename(path)),
        "size": len(data),
        "pages": math.ceil(len(data) / 4096),
        "page_size": 4096,
        "sha256": sha,
        "elf_magic": data[:4].hex(),
        "elf_magic_ok": data[:4] == b"\x7fELF",
        "bytes_hex_chunk_chars": HEX_CHUNK_CHARS,
        "bytes_hex_chunks": chunks,
        "elf_header": {
            "e_type": elf.e_type,
            "e_machine": elf.e_machine,
            "e_machine_name": "EM_RISCV" if elf.e_machine == 243 else str(elf.e_machine),
            "e_entry": elf.e_entry,
            "e_phoff": elf.e_phoff,
            "e_phnum": elf.e_phnum,
            "e_phentsize": elf.e_phentsize,
            "e_shoff": elf.e_shoff,
            "e_shnum": elf.e_shnum,
            "e_shentsize": elf.e_shentsize,
            "e_flags": elf.e_flags,
        },
        "program_headers": elf.phdrs,
        "pt_load": elf.loads(),
        "pt_dynamic": dyn_ph,
        "dynamic_entries": dyn_entries,
        "dynamic": {
            "DT_STRTAB": tags.get(DT_STRTAB),
            "DT_SYMTAB": tags.get(DT_SYMTAB),
            "DT_SYMENT": tags.get(DT_SYMENT),
            "DT_HASH": tags.get(DT_HASH),
            "DT_GNU_HASH": tags.get(DT_GNU_HASH),
            "DT_VERSYM": tags.get(DT_VERSYM),
            "DT_VERDEF": tags.get(DT_VERDEF),
            "DT_HASH_present": DT_HASH in tags,
            "DT_GNU_HASH_present": DT_GNU_HASH in tags,
            "symbol_count": nsyms,
            "symbol_count_source": count_src,
            "symbol_count_detail": count_detail,
            "note": ("musl's __vdsosym counts the dynamic symbols from DT_HASH when "
                     "DT_HASH is present, and from DT_GNU_HASH when it is not."),
        },
        "version_definitions": {str(k): v for k, v in sorted(vnames.items())},
        "dynamic_symbols": syms,
        "exported_symbols": [
            {"name": s["name"], "offset": s["st_value"], "st_value": s["st_value"],
             "st_size": s["st_size"], "version": s["version"],
             "version_index": s["version_index"], "st_shndx": s["st_shndx"]}
            for s in exported],
        "stack": {
            "F_largest_frame_bytes": code["largest_frame_bytes"],
            "F_deepest_chain": code["largest_frame_chain"],
            "recursion_found": code["recursion_found"],
            "per_function": code["per_function"],
            "method": ("The script decodes every RV64GC instruction of every function "
                       "that an exported entry can reach by a direct call, and it adds "
                       "the sp decrements along each call chain."),
        },
        "callee_saved_and_memory_writes": code["callee_saved_report"],
        "crosscheck_readelf": crosscheck,
        "build": BUILD_RECORDS.get(sha, {"note": "no recorded build for this sha256"}),
    }
    return result


def dump_text(results):
    """A plain-text dump of the data the Rocq side needs."""
    lines = []
    for i, r in enumerate(results):
        lines.append("# image %d" % i)
        lines.append("file %s" % r["file"])
        lines.append("configuration %s" % r["configuration"])
        lines.append("sha256 %s" % r["sha256"])
        lines.append("size %d" % r["size"])
        lines.append("pages %d" % r["pages"])
        lines.append("F %d" % r["stack"]["F_largest_frame_bytes"])
        lines.append("chunks %d" % len(r["bytes_hex_chunks"]))
        for c in r["bytes_hex_chunks"]:
            lines.append("chunk %s" % c)
        lines.append("symbols %d" % len(r["exported_symbols"]))
        for s in r["exported_symbols"]:
            lines.append("symbol %s %d %d %s" % (s["name"], s["offset"], s["st_size"],
                                                 s["version"]))
        lines.append("")
    return "\n".join(lines)


def main(argv):
    paths = [a for a in argv[1:] if not a.startswith("--")]
    dump_path = None
    for i, a in enumerate(argv):
        if a == "--dump":
            dump_path = argv[i + 1]
            if dump_path in paths:
                paths.remove(dump_path)
    if not paths:
        print(__doc__)
        return 2
    out = [measure(p) for p in paths]
    if dump_path:
        with open(dump_path, "w") as fh:
            fh.write(dump_text(out))
    json.dump(out, sys.stdout, indent=2)
    sys.stdout.write("\n")
    for r in out:
        cc = r["crosscheck_readelf"]
        sys.stderr.write("%s: %d bytes, %d pages, sha256 %s\n"
                         % (r["file"], r["size"], r["pages"], r["sha256"]))
        sys.stderr.write("  readelf cross-check: %s\n" % cc.get("agree"))
        for row in cc.get("rows", []):
            sys.stderr.write("    %-24s parser 0x%04x/%s  readelf 0x%04x/%s  %s\n"
                             % (row["name"], row["parser_offset"], row["parser_version"],
                                row["readelf_offset"] or 0, row["readelf_version"],
                                "ok" if row["agree"] else "DISAGREE"))
        sys.stderr.write("  F = %d bytes (%s)\n"
                         % (r["stack"]["F_largest_frame_bytes"],
                            " -> ".join(r["stack"]["F_deepest_chain"])))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
