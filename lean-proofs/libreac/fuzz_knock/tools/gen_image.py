#!/usr/bin/env python3
"""ELF -> Lean memory image with the byte certificates the kernel needs.

    python3 gen_image.py <elf> --out-dir <dir> --module OssFuzzTheorems.libreac.fuzz_knock.Image
                              --name Plain [--code 0x12d9c:28 ...]

Writes two Lean modules:

  <Name>.lean       the segments of every PT_LOAD, as hex chunk strings, with
                    the `_chars`/`_chars_eq`/`_ascii`/`_hex`/`_size` certificates
                    of `LinuxProcessSemantics.Common.ImageBytes` and the two
                    per-segment reading lemmas `_read_ascii` and `_byte_ascii`;
                    then `loaded_segments`, `init_pc`, `phdrs` and `image`.
  <Name>Code.lean   `IMAGE_WF` of that image, and, for each `--code BASE:LEN`
                    range, one `fetch_word` and one `decode_any` theorem per
                    4-byte word, each closed by the kernel.

Why the certificates.  A Lean string literal is UTF-8 encoded by the kernel at
every fetch, so `decide +kernel` on a fetch through a whole generated image does
not finish: 10.7 GB and still growing on the 245,308-byte image of
`fuzz_knock.plain` (OSSV-265 gaps ledger row T-13, measured 2026-10-31).
`ImageBytes` replaces the encoding with list indexing, given a proof that every
character of the chunk is one UTF-8 byte.  That proof is the `_ascii`
certificate, and this file emits it.

The image module is TRUSTED, as linux-process-semantics' own
`tools/gen_lean_example_image.py` says of its twin: its segment records, chunk
strings, entry pc and program-header record ARE the program the statement is
about, and nothing in Lean checks them against the ELF.  What checks them is
`--check`, which re-reads the emitted text and compares it with the ELF.
The code module is NOT trusted: every proposed fetch and decode is closed by
`decide +kernel` against Lean's own decoder and the image's own bytes, so a
wrong proposal fails to compile rather than stating a false fact.

The decoder proposer, the character-list compaction and the proof shapes are
taken from linux-process-semantics `tools/gen_lean_example_image.py` at
`ff0313ba4f2e9baffcf5b5f50bc9d31628ae8556`; the ELF reading is from
`probe/ossv265-t/gen_image.py` (OSSV-265 slice T).
"""

from dataclasses import dataclass
from pathlib import Path
import argparse
import itertools
import json
import struct
import sys

CHUNK = 256      # bytes per mixed hex chunk
RUN_MIN = 64     # a run of one repeated byte this long or longer becomes its own chunk
RUN_CAP = 32768  # and is cut no longer than this; `String.ofList` keeps its cost O(1)

# `rfl` between a chunk's literal and its character list recurses in proportion
# to the chunk's length; a chunk longer than one page gets its own limit.
PAGE_CHUNK_DIGITS = 8192
DEPTH_PER_DIGIT = 16


# --------------------------------------------------------------------------- #
# The ELF
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Seg:
    name: str
    base: int
    size: int
    perms: str
    data: bytes          # p_filesz bytes, zero-extended to p_memsz

    @property
    def chunks(self):
        """Cut the segment into chunks a kernel computation can take.

        A chunk costs five kernel-checked certificates whatever its length, so
        the number of chunks is what the image module's build time is a
        function of. A run of one repeated byte renders as `List.replicate`,
        which `List.all_replicate` decides in one step however long the run
        is, so a run of at least `RUN_MIN` bytes becomes its own chunk, capped
        at `RUN_CAP` so that the `rfl` between the string literal and the
        character list stays inside a recursion depth Lean accepts. Everything
        else is cut at `CHUNK` bytes. Measured on `fuzz_knock.plain`: 955
        chunks at a flat 256 bytes, against far fewer this way, because the
        199,232-byte .bss tail is one run.
        """
        pieces, mixed = [], bytearray()

        def flush():
            while mixed:
                pieces.append(bytes(mixed[:CHUNK]))
                del mixed[:CHUNK]

        i, n = 0, len(self.data)
        while i < n:
            j = i
            while j < n and self.data[j] == self.data[i]:
                j += 1
            if j - i >= RUN_MIN:
                flush()
                for k in range(i, j, RUN_CAP):
                    pieces.append(self.data[k:min(k + RUN_CAP, j)])
            else:
                mixed += self.data[i:j]
                while len(mixed) >= CHUNK:
                    pieces.append(bytes(mixed[:CHUNK]))
                    del mixed[:CHUNK]
            i = j
        flush()
        assert b"".join(pieces) == self.data, f"{self.name}: chunking lost bytes"
        return [(f"{self.name}_c{idx:04d}", p.hex()) for idx, p in enumerate(pieces)]


@dataclass(frozen=True)
class Img:
    name: str
    segments: tuple
    pc: int
    ph_addr: int
    ph_ent: int
    ph_num: int


def read_elf(path: Path, name: str) -> Img:
    data = path.read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        sys.exit(f"{path}: not a little-endian ELF64")
    e_entry = struct.unpack_from("<Q", data, 0x18)[0]
    e_phoff = struct.unpack_from("<Q", data, 0x20)[0]
    e_phentsize, e_phnum = struct.unpack_from("<HH", data, 0x36)
    loads = []
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        p_type, p_flags = struct.unpack_from("<II", data, off)
        p_offset, p_vaddr, _pa, p_filesz, p_memsz, _al = struct.unpack_from("<QQQQQQ", data, off + 8)
        if p_type == 1:
            loads.append((p_vaddr, p_offset, p_filesz, p_memsz, p_flags))
    loads.sort()
    for a, b in zip(loads, loads[1:]):
        if a[0] + a[3] > b[0]:
            sys.exit(f"{path}: PT_LOAD at {a[0]:#x} overlaps the one at {b[0]:#x}; "
                     "`find_segment` would depend on list order")
    segs = []
    for i, (vaddr, offset, filesz, memsz, flags) in enumerate(loads):
        perms = ("r" if flags & 4 else "") + ("w" if flags & 2 else "") + ("x" if flags & 1 else "")
        body = data[offset:offset + filesz] + b"\x00" * (memsz - filesz)
        segs.append(Seg(f"{name.lower()}_seg{i:03d}", vaddr, memsz, perms, body))
    ph_addr = 0
    for vaddr, offset, filesz, _m, _f in loads:
        if offset <= e_phoff < offset + filesz:
            ph_addr = vaddr + (e_phoff - offset)
            break
    else:
        sys.exit(f"{path}: the program header table is in no PT_LOAD's file image")
    return Img(name, tuple(segs), e_entry, ph_addr, e_phentsize, e_phnum)


def containing(image: Img, address: int, width: int) -> Seg:
    for seg in image.segments:
        if seg.base <= address and address + width <= seg.base + seg.size:
            return seg
    sys.exit(f"{image.name}: [{address:#x}, {address + width:#x}) is in no segment")


# --------------------------------------------------------------------------- #
# The decoder proposer (gen_lean_example_image.py's `decode`, arm for arm)
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Decoded:
    ctor: str
    args: tuple

    def lean(self) -> str:
        parts = ["." + self.ctor]
        for arg in self.args:
            parts.append(arg if isinstance(arg, str) else arg.render())
        return " ".join(parts)


@dataclass(frozen=True)
class Reg:
    n: int

    def render(self) -> str:
        return str(self.n)


@dataclass(frozen=True)
class Imm:
    value: int
    width: int

    def render(self) -> str:
        return f"0x{self.value:x}"


@dataclass(frozen=True)
class Small:
    value: int

    def render(self) -> str:
        return str(self.value)


BRANCH = {0: "BC_EQ", 1: "BC_NE", 4: "BC_LT", 5: "BC_GE", 6: "BC_LTU", 7: "BC_GEU"}
LOAD = {0: ("SZ1", "true"), 1: ("SZ2", "true"), 2: ("SZ4", "true"), 3: ("SZ8", "true"),
        4: ("SZ1", "false"), 5: ("SZ2", "false"), 6: ("SZ4", "false")}
STORE = {0: "SZ1", 1: "SZ2", 2: "SZ4", 3: "SZ8"}
OP_IMM = {0: "ALU_ADD", 2: "ALU_SLT", 3: "ALU_SLTU", 4: "ALU_XOR", 6: "ALU_OR", 7: "ALU_AND"}
OP = {(0x00, 0): ("Op", "ALU_ADD"), (0x20, 0): ("Op", "ALU_SUB"), (0x00, 1): ("Op", "ALU_SLL"),
      (0x00, 2): ("Op", "ALU_SLT"), (0x00, 3): ("Op", "ALU_SLTU"), (0x00, 4): ("Op", "ALU_XOR"),
      (0x00, 5): ("Op", "ALU_SRL"), (0x20, 5): ("Op", "ALU_SRA"), (0x00, 6): ("Op", "ALU_OR"),
      (0x00, 7): ("Op", "ALU_AND"),
      (0x01, 0): ("Mul", "M_MUL"), (0x01, 1): ("Mul", "M_MULH"), (0x01, 2): ("Mul", "M_MULHSU"),
      (0x01, 3): ("Mul", "M_MULHU"), (0x01, 4): ("Mul", "M_DIV"), (0x01, 5): ("Mul", "M_DIVU"),
      (0x01, 6): ("Mul", "M_REM"), (0x01, 7): ("Mul", "M_REMU")}
OP32 = {(0x00, 0): ("Op32", "ALU_ADD"), (0x20, 0): ("Op32", "ALU_SUB"),
        (0x00, 1): ("Op32", "ALU_SLL"), (0x00, 5): ("Op32", "ALU_SRL"),
        (0x20, 5): ("Op32", "ALU_SRA"), (0x01, 0): ("Mul32", "M_MUL"),
        (0x01, 4): ("Mul32", "M_DIV"), (0x01, 5): ("Mul32", "M_DIVU"),
        (0x01, 6): ("Mul32", "M_REM"), (0x01, 7): ("Mul32", "M_REMU")}
AMO = {0x00: "AMO_ADD", 0x01: "AMO_SWAP", 0x04: "AMO_XOR", 0x08: "AMO_OR", 0x0C: "AMO_AND",
       0x10: "AMO_MIN", 0x14: "AMO_MAX", 0x18: "AMO_MINU", 0x1C: "AMO_MAXU"}
CSR = {1: "CSR_RW", 2: "CSR_RS", 3: "CSR_RC"}
FP_OPCODES = (0x07, 0x27, 0x43, 0x47, 0x4B, 0x4F, 0x53)


def decode(word: int) -> Decoded:
    """Propose the `instr` Lean's `decode_any` returns for a 32-bit word.

    Nothing depends on this being right: the generated theorem is the check.
    """
    def bits(lo, n):
        return word >> lo & ((1 << n) - 1)

    if not 0 <= word < 1 << 32:
        raise ValueError(f"not a 32-bit word: {word:#x}")
    where = f"instruction 0x{word:08x}"
    if bits(0, 2) != 3:
        raise ValueError(f"{where} is a compressed (RVC) parcel; Lean's DecodeC does not "
                         "port RVC yet (decode_any answers none), so there is no decode fact")
    opc, rd, f3, rs1, rs2, f7 = bits(0, 7), Reg(bits(7, 5)), bits(12, 3), Reg(bits(15, 5)), \
        Reg(bits(20, 5)), bits(25, 7)
    imm_i = Imm(bits(20, 12), 12)
    imm_s = Imm(bits(25, 7) << 5 | bits(7, 5), 12)
    imm_b = Imm(bits(31, 1) << 12 | bits(7, 1) << 11 | bits(25, 6) << 5 | bits(8, 4) << 1, 13)
    imm_u = Imm(bits(12, 20), 20)
    imm_j = Imm(bits(31, 1) << 20 | bits(12, 8) << 12 | bits(20, 1) << 11 | bits(21, 10) << 1, 21)
    found = None
    if opc == 0x37:
        found = Decoded("Lui", (rd, imm_u))
    elif opc == 0x17:
        found = Decoded("Auipc", (rd, imm_u))
    elif opc == 0x6F:
        found = Decoded("Jal", (rd, imm_j))
    elif opc == 0x67 and f3 == 0:
        found = Decoded("Jalr", (rd, rs1, imm_i))
    elif opc == 0x63 and f3 in BRANCH:
        found = Decoded("Branch", ("." + BRANCH[f3], rs1, rs2, imm_b))
    elif opc == 0x03 and f3 in LOAD:
        size, signed = LOAD[f3]
        found = Decoded("Load", ("." + size, signed, rd, rs1, imm_i))
    elif opc == 0x23 and f3 in STORE:
        found = Decoded("Store", ("." + STORE[f3], rs1, rs2, imm_s))
    elif opc == 0x13:
        shamt = Small(bits(20, 6))
        if f3 in OP_IMM:
            found = Decoded("OpImm", ("." + OP_IMM[f3], rd, rs1, imm_i))
        elif f3 == 1 and bits(26, 6) == 0:
            found = Decoded("ShiftImm", (".ALU_SLL", rd, rs1, shamt))
        elif f3 == 5 and bits(26, 6) in (0x00, 0x10):
            op = ".ALU_SRL" if bits(26, 6) == 0 else ".ALU_SRA"
            found = Decoded("ShiftImm", (op, rd, rs1, shamt))
    elif opc == 0x1B:
        shamt = Small(bits(20, 5))
        if f3 == 0:
            found = Decoded("OpImm32", (rd, rs1, imm_i))
        elif f3 == 1 and f7 == 0:
            found = Decoded("ShiftImm32", (".ALU_SLL", rd, rs1, shamt))
        elif f3 == 5 and f7 in (0x00, 0x20):
            op = ".ALU_SRL" if f7 == 0 else ".ALU_SRA"
            found = Decoded("ShiftImm32", (op, rd, rs1, shamt))
    elif opc in (0x33, 0x3B) and (f7, f3) in (OP if opc == 0x33 else OP32):
        ctor, op = (OP if opc == 0x33 else OP32)[f7, f3]
        found = Decoded(ctor, ("." + op, rd, rs1, rs2))
    elif opc == 0x0F:
        if f3 == 0 and rd.n == 0 and rs1.n == 0 and (bits(28, 4) == 0 or bits(20, 12) == 0x833):
            found = Decoded("Fence", (Small(bits(28, 4)), Small(bits(24, 4)), Small(bits(20, 4)),
                                      rd, rs1))
        elif f3 == 1 and word == 0x0000100F:
            found = Decoded("FenceI", (rd, rs1, imm_i))
    elif opc == 0x73:
        if word == 0x00000073:
            found = Decoded("Ecall", ())
        elif word == 0x00100073:
            found = Decoded("Ebreak", ())
        elif f3 in CSR:
            found = Decoded("Csr", ("." + CSR[f3], rd, rs1, Imm(bits(20, 12), 12)))
        elif f3 - 4 in CSR:
            found = Decoded("CsrI", ("." + CSR[f3 - 4], rd, Imm(rs1.n, 5), Imm(bits(20, 12), 12)))
    elif opc == 0x2F and f3 in (2, 3):
        width = ".AW" if f3 == 2 else ".AD"
        aq, rl = ("true" if bits(k, 1) else "false" for k in (26, 25))
        funct5 = bits(27, 5)
        if funct5 in AMO:
            found = Decoded("Amo", ("." + AMO[funct5], width, aq, rl, rd, rs1, rs2))
        elif funct5 == 0x02 and rs2.n == 0:
            found = Decoded("Lr", (width, aq, rl, rd, rs1))
        elif funct5 == 0x03:
            found = Decoded("Sc", (width, aq, rl, rd, rs1, rs2))
    elif opc in FP_OPCODES:
        raise ValueError(f"{where} is a floating-point instruction; Lean's Decode does not "
                         "port the F/D arms yet (decode answers none)")
    if found is None:
        raise ValueError(f"unknown opcode: {where} does not decode under Lean's Decode")
    return found


# --------------------------------------------------------------------------- #
# Rendering
# --------------------------------------------------------------------------- #

def chars_term(content: str) -> str:
    """Compact a proposed character list; the kernel proves its literal identity."""
    parts, pending = [], []
    for char, run in itertools.groupby(content):
        count = sum(1 for _ in run)
        if count < 8:
            pending.extend(char * count)
        else:
            if pending:
                parts.append("[" + ", ".join(repr(c) for c in pending) + "]")
                pending = []
            parts.append(f"List.replicate {count} {char!r}")
    if pending:
        parts.append("[" + ", ".join(repr(c) for c in pending) + "]")
    return " ++ ".join(parts) if parts else "[]"


def chunk_depth(content: str) -> list:
    if len(content) <= PAGE_CHUNK_DIGITS:
        return []
    return [f"set_option maxRecDepth {DEPTH_PER_DIGIT * len(content)} in"]


def image_module(image: Img, module: str, elf_name: str, sha: str) -> str:
    ns = f"{module}.{image.name}"
    lines = [f"-- GENERATED by tools/gen_image.py from {elf_name}",
             f"-- SHA-256 {sha}",
             "-- Do not edit.  This module is TRUSTED: its records ARE the program the",
             "-- statement is about.  `gen_image.py --check` re-reads it against the ELF.",
             "-- Ports oss-verify-proofs-internal ossv/recipes:projects/libreac/fuzz_knock/images/<Build>.v",
             "-- (which linux-process-semantics' `elf-snapshot` generates at build time).",
             "import LinuxProcessSemantics.Common.ImageBytes", "",
             f"namespace {ns}", "",
             "open LinuxProcessSemantics.LinuxProcessSem.MemImageType",
             "open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
             "open LinuxProcessSemantics.Common.ImageBytes", "",
             "set_option maxRecDepth 65536", "set_option maxHeartbeats 1000000", ""]
    for seg in image.segments:
        chunk_list = seg.chunks
        for name, content in chunk_list:
            term = chars_term(content)
            # A chunk that is one `List.replicate` is decided in ONE step through
            # `List.all_replicate`, however long it is; anything else is decided
            # element by element, and a `simp only` in front of that is dead weight.
            rep = term.startswith("List.replicate ") and " ++ " not in term
            closes = (f"  simp only [{name}_chars, List.all_replicate]\n  decide +kernel"
                      if rep else "  decide +kernel")
            lines += [f"def {name}_chars : List Char := {term}",
                      f"def {name} : String := String.ofList {name}_chars",
                      f"theorem {name}_chars_eq : {name} = String.ofList {name}_chars := rfl",
                      f"theorem {name}_ascii : {name}_chars.all (fun c => c.utf8Size == 1) = true := by",
                      closes,
                      f"theorem {name}_hex : {name}_chars.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true := by",
                      closes, ""]
        lines += [f"def {seg.name} : Segment :=",
                  f"  {{ seg_base := 0x{seg.base:x}, seg_size := 0x{seg.size:x},",
                  f"    seg_perms := {json.dumps(seg.perms)},",
                  "    seg_bytes := [" + ", ".join(n for n, _ in chunk_list) + "] }", ""]
        chunks = "[" + ", ".join(n + "_chars" for n, _ in chunk_list) + "]"
        reprs = ", ".join(n + "_chars_eq" for n, _ in chunk_list)
        hname = seg.name + "_ascii"
        lines += [f"theorem {hname} :",
                  f"    ∀ cs ∈ ({chunks} : List (List Char)), cs.all (fun c => c.utf8Size == 1) = true := by",
                  "  intro cs h",
                  "  simp only [List.mem_cons, List.not_mem_nil, or_false] at h",
                  "  rcases h with " + " | ".join("rfl" for _ in chunk_list)]
        for name, _ in chunk_list:
            lines.append(f"  · exact {name}_ascii")
        lines += ["", f"theorem {seg.name}_read_ascii (off n : Nat) :",
                  f"    segment_read_bytes {seg.name}.seg_bytes off n =",
                  f"      ascii_segment_read_bytes {chunks} off n := by",
                  f"  change segment_read_bytes [{', '.join(n for n, _ in chunk_list)}] off n = _",
                  f"  rw [{reprs}]",
                  f"  exact segment_read_bytes_ascii {chunks} {hname} off n", "",
                  f"theorem {seg.name}_byte_ascii (off : Nat) :",
                  f"    segment_byte_at {seg.name}.seg_bytes off = ascii_segment_byte_at {chunks} off := by",
                  f"  change segment_byte_at [{', '.join(n for n, _ in chunk_list)}] off = _",
                  f"  rw [{reprs}]",
                  f"  exact segment_byte_at_ascii {chunks} {hname} off", ""]
    lines += ["def loaded_segments : List Segment :=",
              "  [" + ", ".join(s.name for s in image.segments) + "]",
              f"def init_pc : Nat := 0x{image.pc:x}",
              "def phdrs : PhdrInfo :=",
              f"  {{ ph_addr := 0x{image.ph_addr:x}, ph_ent := {image.ph_ent}, ph_num := {image.ph_num} }}",
              "",
              "def image : Image := Image.mkImage loaded_segments init_pc phdrs",
              "", f"end {ns}", ""]
    return "\n".join(lines)


def code_module(image: Img, module: str, ranges: list) -> str:
    ns = f"{module}.{image.name}"
    cns = f"{module}.{image.name}Code"
    lines = ["-- GENERATED by tools/gen_image.py.  NOT trusted: every proposed fetch and",
             "-- decode is closed by `decide +kernel` against Lean's own decoder and the",
             "-- image's own bytes, so a wrong proposal fails to compile.",
             "-- Ports oss-verify-proofs-internal ossv/recipes:projects/libreac/fuzz_knock/Images.v",
             "-- (the `_wf` lemmas) and linux-process-semantics' gen-fd-lemmas (the fetch/decode facts).",
             "import LinuxProcessSemantics.Riscv.DecodeC",
             "import LinuxProcessSemantics.EquivalenceDefinition.Equivalence",
             f"import {ns}", "",
             f"namespace {cns}", "",
             "open LinuxProcessSemantics.Riscv.Prelude",
             "open LinuxProcessSemantics.LinuxProcessSem.MemImageType",
             "open LinuxProcessSemantics.LinuxProcessSem.BvBase",
             "open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
             "open LinuxProcessSemantics.Common.ImageBytes",
             "open LinuxProcessSemantics.EquivalenceDefinition.Equivalence",
             "open LinuxProcessSemantics.Riscv.DecodeC",
             f"open {ns}", "",
             "set_option maxRecDepth 65536", "set_option maxHeartbeats 1000000", "",
             "abbrev segs := loaded_segments", ""]

    # --- the three IMAGE_WF helpers (gen_lean_example_image.py's, verbatim) ---
    lines += ["private theorem image_entry_of_wx (ss : List Segment) (pc : Nat) (w : BitVec 32)",
              "    (h : fetch_word_wx ss (Z_to_bv 64 (pc : Int)) = some w) :",
              "    image_entry_fetchable ss pc = true := by",
              "  cases hf : fetch_word ss (Z_to_bv 64 (pc : Int)) <;>",
              "    simp only [image_entry_fetchable, hf, h]", "",
              "private theorem image_entry_of_ro (ss : List Segment) (pc : Nat) (w : BitVec 32)",
              "    (h : fetch_word ss (Z_to_bv 64 (pc : Int)) = some w) :",
              "    image_entry_fetchable ss pc = true := by",
              "  simp only [image_entry_fetchable, h]", "",
              "private theorem image_phdrs_of_read (ss : List Segment) (ph : PhdrInfo)",
              "    (hn : 0 < ph.ph_num) (he : 0 < ph.ph_ent)",
              "    (hr : (memory_read ss (Z_to_bv 64 (ph.ph_addr : Int)) (ph.ph_num * ph.ph_ent)).isSome = true) :",
              "    image_phdrs_readable ss ph = true := by",
              "  simp [image_phdrs_readable, hn, he, hr]", ""]

    def fetch_theorem(pc: int, word: int, prefix: str = "F_"):
        seg = containing(image, pc, 4)
        writable = "w" in seg.perms
        fetch = "fetch_word_wx" if writable else "fetch_word"
        rule = fetch + "_of_bytes"
        byte_args = " ".join(f"0x{b:02x}" for b in word.to_bytes(4, "little"))
        byte_list = "[" + ", ".join(f"0x{b:02x}" for b in word.to_bytes(4, "little")) + "]"
        chunks = "[" + ", ".join(n + "_chars" for n, _ in seg.chunks) + "]"
        return [f"theorem {prefix}{pc:x} : {fetch} segs 0x{pc:x} = some 0x{word:08x} := by",
                f"  apply {rule} segs {seg.name} 0x{pc:x} {byte_args}",
                "  · decide +kernel",
                "  · rfl",
                "  · decide +kernel",
                "  · decide +kernel",
                f"  · have hr : ascii_segment_read_bytes {chunks} {pc - seg.base} 4 = some {byte_list} := by",
                "      decide +kernel",
                f"    exact ({seg.name}_read_ascii {pc - seg.base} 4).trans hr"]

    # --- IMAGE_WF ---
    entry_seg = containing(image, image.pc, 4)
    entry_word = int.from_bytes(entry_seg.data[image.pc - entry_seg.base:image.pc - entry_seg.base + 4],
                                "little")
    lines += fetch_theorem(image.pc, entry_word, "entryF_") + [""]
    ph_seg = containing(image, image.ph_addr, image.ph_ent * image.ph_num)
    entry_kind = "wx" if "w" in entry_seg.perms else "ro"
    lines += ["/-- The three obligations of `IMAGE_WF` (the Rocq `image_wf` of",
              "`OssFuzzTheorems.Core.Images`, which `Images.v` closes with `check_image_wf`). -/",
              "theorem imageWf : IMAGE_WF image := by",
              "  constructor",
              f"  · exact image_entry_of_{entry_kind} segs init_pc _ entryF_{image.pc:x}",
              "  · apply image_phdrs_of_read segs phdrs",
              "    · decide +kernel", "    · decide +kernel",
              f"    · apply memory_read_isSome_of_segment segs {ph_seg.name} _ _",
              "      · rfl", "      · decide +kernel"]
    if len(ph_seg.chunks) == 1:
        chunk_name = ph_seg.chunks[0][0]
        lines += [f"      · exact (congrArg Option.isSome ({ph_seg.name}_read_ascii _ _)).trans",
                  f"          (ascii_segment_read_bytes_single_isSome {chunk_name}_chars",
                  f"            {chunk_name}_hex _ _ (by decide +kernel))"]
    else:
        lines += [f"      · exact (congrArg Option.isSome ({ph_seg.name}_read_ascii _ _)).trans (by decide +kernel)"]
    lines += ["  · decide +kernel", ""]

    # --- the requested code ranges ---
    for base, length in ranges:
        if base % 4 or length % 4:
            sys.exit(f"--code {base:#x}:{length}: both the base and the length must be 4-byte aligned")
        seg = containing(image, base, length)
        lines += [f"/-! The {length} bytes at 0x{base:x}. -/", ""]
        for i in range(length // 4):
            pc = base + 4 * i
            word = int.from_bytes(seg.data[pc - seg.base:pc - seg.base + 4], "little")
            try:
                term = decode(word).lean()
            except ValueError as exc:
                sys.exit(f"{image.name} at pc {pc:#x}: {exc}")
            lines += fetch_theorem(pc, word)
            lines += [f"theorem D_{pc:x} : decode_any 0x{word:08x} = some ({term}, 4) := by",
                      "  decide +kernel", ""]
    lines += [f"end {cns}", ""]
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# --check: read the emitted image module back and compare it with the ELF
# --------------------------------------------------------------------------- #

def _chars_term_hex(term: str) -> str:
    """Read back a `chars_term` rendering: the hex digits it denotes.

    The inverse of `chars_term`, so that `--check` compares the ELF with the
    TERM the module carries, not with a second rendering of it.
    """
    import re
    out = []
    for part in term.split(" ++ "):
        part = part.strip()
        rep = re.fullmatch(r"List\.replicate (\d+) '(.)'", part)
        if rep:
            out.append(rep.group(2) * int(rep.group(1)))
            continue
        lit = re.fullmatch(r"\[(.*)\]", part)
        if lit is None:
            raise ValueError(f"gen_image.py --check: unreadable character term {part!r}")
        if lit.group(1).strip():
            for c in lit.group(1).split(", "):
                m = re.fullmatch(r"'(.)'", c.strip())
                if m is None:
                    raise ValueError(f"gen_image.py --check: unreadable character {c!r}")
                out.append(m.group(1))
    return "".join(out)


def check(image: Img, text: str) -> None:
    """Re-read the emitted image module's records and compare with the ELF."""
    import re
    bad = []
    for seg in image.segments:
        m = re.search(rf"def {seg.name} : Segment :=\s*\{{ seg_base := 0x([0-9a-f]+), "
                      rf"seg_size := 0x([0-9a-f]+),\s*seg_perms := \"([a-z]*)\",\s*"
                      rf"seg_bytes := \[([^\]]*)\] \}}", text)
        if m is None:
            bad.append(f"{seg.name}: no record in the emitted text")
            continue
        if (int(m.group(1), 16), int(m.group(2), 16), m.group(3)) != (seg.base, seg.size, seg.perms):
            bad.append(f"{seg.name}: record {m.group(1)},{m.group(2)},{m.group(3)} "
                       f"against the ELF's {seg.base:x},{seg.size:x},{seg.perms}")
        got = ""
        for name in [n.strip() for n in m.group(4).split(",")]:
            c = re.search(rf"def {name}_chars : List Char := (.*)\n", text)
            if c is None:
                bad.append(f"{name}: no character list")
                break
            got += _chars_term_hex(c.group(1))
        else:
            if got != seg.data.hex():
                bad.append(f"{seg.name}: the chunk literals are not the segment's bytes")
    for field, want, pat in (("init_pc", image.pc, r"def init_pc : Nat := 0x([0-9a-f]+)"),
                             ("ph_addr", image.ph_addr, r"ph_addr := 0x([0-9a-f]+)"),
                             ("ph_ent", image.ph_ent, r"ph_ent := (\d+)"),
                             ("ph_num", image.ph_num, r"ph_num := (\d+)")):
        m = re.search(pat, text)
        base = 16 if "0x" in pat else 10
        if m is None or int(m.group(1), base) != want:
            bad.append(f"{field}: emitted {m.group(1) if m else 'nothing'}, ELF says {want}")
    if bad:
        for line in bad:
            print("gen_image.py --check:", line, file=sys.stderr)
        sys.exit(1)
    print(f"gen_image.py --check: the emitted image is the ELF's "
          f"{len(image.segments)} segments, entry 0x{image.pc:x}, "
          f"phdrs 0x{image.ph_addr:x}/{image.ph_ent}x{image.ph_num}")


def main() -> None:
    import hashlib
    ap = argparse.ArgumentParser()
    ap.add_argument("elf")
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--module", required=True,
                    help="the Lean module prefix, e.g. OssFuzzTheorems.libreac.fuzz_knock.Image")
    ap.add_argument("--name", required=True, help="the build's name, e.g. Plain")
    ap.add_argument("--code", action="append", default=[],
                    help="BASE:LEN, a range to emit fetch and decode theorems for; repeatable")
    ap.add_argument("--sha256", default=None, help="refuse unless the ELF has this SHA-256")
    ap.add_argument("--check", action="store_true",
                    help="only re-read the emitted image module against the ELF")
    args = ap.parse_args()

    path = Path(args.elf)
    sha = hashlib.sha256(path.read_bytes()).hexdigest()
    if args.sha256 and sha != args.sha256:
        sys.exit(f"{path}: SHA-256 {sha}, not the pinned {args.sha256}")
    image = read_elf(path, args.name)
    out = Path(args.out_dir)
    img_path = out / f"{args.name}.lean"
    code_path = out / f"{args.name}Code.lean"

    if args.check:
        check(image, img_path.read_text())
        return

    ranges = []
    for spec in args.code:
        b, _, l = spec.partition(":")
        ranges.append((int(b, 0), int(l, 0)))

    out.mkdir(parents=True, exist_ok=True)
    img_path.write_text(image_module(image, args.module, path.name, sha))
    code_path.write_text(code_module(image, args.module, ranges))
    words = sum(l // 4 for _, l in ranges)
    print(f"{img_path}: {len(image.segments)} segments, "
          f"{sum(s.size for s in image.segments)} bytes of image")
    print(f"{code_path}: IMAGE_WF and {words} fetch/decode word pairs")


if __name__ == "__main__":
    main()
