#!/usr/bin/env python3
"""Generate the Lean memory images and checked fetch/decode facts of an example.

For theories/Examples/<name>/ this writes three Lean modules, each into its
own file:

    <name>/SourceMemImage.lean   the source snapshot's segments, entry, phdrs
    <name>/TargetMemImage.lean   the same for the target
    <name>/<name>_code.lean      one fetch and one decode theorem per .text
                                 word of each image, and IMAGE_WF for both

The input is the committed elf-snapshot of the example: <Role>MemImage.v and
every named .hex chunk. Nothing is read from an ELF, which is a build
product and not checked in; gen-fd-lemmas makes the same choice for the
Rocq twin of the code module, and for the same reason.

The image modules are TRUSTED: their segment records, chunk strings,
entry pc and program-header record build `Source.image`/`Target.image`,
the programs an equivalence statement is about, and nothing in Lean checks
them against the snapshot. What they rest on is `read_image`, which
refuses any text outside elf-snapshot's syntax, and `image_module`'s
rendering; tools/test_gen_lean_example_image.py re-reads every record the
rendering spells and compares it with the Rocq-side reading of the same
snapshot. The code module is not trusted. Its instruction decoder only
PROPOSES the Lean term of each word; every `decode_any` theorem is closed
by `decide +kernel` against Lean's own decoder, and every fetch by the
kernel against the image's bytes, so a wrong proposal fails to compile
rather than stating a false fact.

Which words get a theorem is the Rocq code file's choice, not a new one:
the .text of an image is located by the rule gen-fd-lemmas applies (the
maximal nonzero run inside the executable PT_LOAD's file extent, read from
the program header table the image maps), and an explicit range is taken
from the example's gen-fd-lemmas rule in theories/Examples/dune, the only
place an image with a writable executable segment gets one. So the Lean
code module covers exactly the words theories/Examples/<name>/<name>_code.v
does. The ranges choose which facts to prove; they restrict nothing about
the execution model.

What it refuses, and why, instead of emitting something the build then
rejects or silently narrower facts:
  - a compressed parcel: Lean's DecodeC does not port RVC yet
    (lean/LinuxProcessSemantics/Riscv/DecodeC.lean answers `none` for
    every one), so no true decode fact exists to generate;
  - a floating-point word: Lean's Decode does not port the F/D arms;
  - any other word Lean's `decode` answers `none` for;
  - overlapping segments, since `find_segment` would then depend on list
    order, which no elf-snapshot image has (overlapping LOADs are refused
    upstream by elf-snapshot);
  - more or fewer than one executable segment, and a writable one with no
    explicit range, as gen-fd-lemmas does;
  - any snapshot text outside elf-snapshot's own record syntax.
"""

from dataclasses import dataclass
from pathlib import Path
import argparse
import itertools
import json
import re


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES_DIR = ROOT / "theories/Examples"
ROLES = ("Source", "Target")
PREFIX = {"Source": "S", "Target": "T"}

# The rwx_flag_ns pilot's proof consumes three `store_ok` facts from its code
# module. They are a proof's lemmas, not facts about the image, and no other
# example needs them here: the Rocq proofs state store_ok beside the proof
# (`source_store_ok` in theories/Examples/rwx_flag_ns/rwx_flag_ns_defs.v is
# the pattern), which is where a Lean port of theirs puts it too, from the
# generated `_byte_ascii` lemmas. Kept so rwx_flag_ns regenerates exactly.
STORE_FACTS = {
    "rwx_flag_ns": (("Source", "source_store_environ", 0x100e8, 8),
                    ("Source", "source_store_flag", 0x100e4, 1),
                    ("Target", "target_store_flag", 0x10021a8, 1)),
}


@dataclass(frozen=True)
class Segment:
    name: str
    base: int
    size: int
    perms: str
    chunks: tuple[tuple[str, str], ...]

    def data(self) -> bytes:
        return bytes.fromhex("".join(content for _, content in self.chunks))


@dataclass(frozen=True)
class Image:
    example: str
    name: str
    role: str
    segments: tuple[Segment, ...]
    pc: int
    ph_addr: int
    ph_ent: int
    ph_num: int
    inputs: tuple[Path, ...]


def namespace(example: str) -> str:
    return "LinuxProcessSemantics.Examples." + example


def check_example_name(example: str) -> None:
    # The name becomes a Lean module component and a Rocq library path.
    if not re.fullmatch(r"[a-z][a-z0-9_]*", example):
        raise ValueError("unsupported example name: " + repr(example))


def one(pattern, text, label, flags=0):
    found = list(re.finditer(pattern, text, flags))
    if len(found) != 1:
        raise ValueError(f"expected exactly one {label}, found {len(found)}")
    return found[0]


def strip_comments(text: str) -> str:
    """Remove nested Rocq comments without treating quoted strings as comments.

    Rocq's lexer reads a string inside a comment as a string, so a `*)`
    within it does not close the comment; this reader does not, and would
    then read a different text than Rocq does. elf-snapshot writes no
    string in a comment, so one is refused rather than lexed."""
    out, index, depth, quoted = [], 0, 0, False
    while index < len(text):
        if not quoted and text.startswith("(*", index):
            depth += 1
            index += 2
        elif depth and text.startswith("*)", index):
            depth -= 1
            index += 2
            if not depth:
                out.append(" ")
        elif depth and text[index] == '"':
            raise ValueError("a string inside a Rocq comment, which elf-snapshot never "
                             "writes and this reader does not lex as Rocq does")
        elif depth:
            index += 1
        elif text[index] == '"':
            out.append('"')
            index += 1
            if quoted and index < len(text) and text[index] == '"':
                out.append('"')
                index += 1
            else:
                quoted = not quoted
        else:
            out.append(text[index])
            index += 1
    if depth or quoted:
        raise ValueError("unterminated comment or string in snapshot")
    return "".join(out)


def snapshot_skeleton(image: Image) -> str:
    """The complete supported elf-snapshot syntax, including exported bindings.

    Reading isolated definitions is insufficient: the exported Source/Target
    module could bind different data. Reject every unrecognized command rather
    than silently treating it as an irrelevant comment.
    """
    name = image.name
    lines = ["From Stdlib Require Import NArith List String PrimString.",
             "From ReadFile Require Import ReadFile.",
             "From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.",
             "Import ListNotations.", "Local Open Scope string_scope."]
    for seg in image.segments:
        for chunk_name, _ in seg.chunks:
            filename, alias = chunk_names(name, chunk_name)[:2]
            lines += [f'From {namespace(image.example)} Extra Dependency "{filename}" as {alias}.',
                      f"ReadFileString {alias} As {chunk_name}.",
                      f"Global Strategy 200 [{chunk_name}]."]
    for seg in image.segments:
        lines += [f"Definition {seg.name} : Segment := {{|",
                  f"seg_base := 0x{seg.base:x}%N; seg_size := 0x{seg.size:x}%N;",
                  f'seg_perms := "{seg.perms}";',
                  "seg_bytes := [" + "; ".join(n for n, _ in seg.chunks) + "] |}."]
    lines += [f"Definition {name}_loaded_segments : list Segment :=",
              "[" + "; ".join(s.name for s in image.segments) + "].",
              f"Definition {name}_init_pc : N := 0x{image.pc:x}%N.",
              f"Definition {name}_phdrs : PhdrInfo := {{| ph_addr := 0x{image.ph_addr:x}%N;",
              f"ph_ent := {image.ph_ent}%N; ph_num := {image.ph_num}%N |}}.",
              "Global Strategy 200 [" + " ".join(s.name for s in image.segments)
              + f" {name}_loaded_segments].",
              f"Module {image.role} <: MemImage.",
              f"Definition loaded_segments := {name}_loaded_segments.",
              f"Definition init_pc := {name}_init_pc.",
              f"Definition phdrs := {name}_phdrs.", f"End {image.role}."]
    return "\n".join(lines)


def snapshot_tokens(text: str) -> list[str]:
    token = re.compile(r'\s+|"(?:[^"]|"")*"|0x[0-9a-f]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|<:|:=|\{\||\|\}|[.;:%\[\]]')
    result, position = [], 0
    while position < len(text):
        match = token.match(text, position)
        if not match:
            raise ValueError("unsupported snapshot syntax at: " + repr(text[position:position + 40]))
        if not match[0].isspace():
            result.append(match[0])
        position = match.end()
    return result


DEPENDENCY_RE = re.compile(
    r'Extra Dependency\s+"(?P<file>[^"]+)"\s+as\s+(?P<dep>\w+)\.\s*'
    r'ReadFileString\s+(?P=dep)\s+As\s+(?P<definition>\w+)\.', re.DOTALL)
SEGMENT_RE = re.compile(
    r"Definition\s+\w+_segment_(?P<idx>\d+)\s*:\s*Segment\s*:=\s*\{\|"
    r"\s*seg_base\s*:=\s*0x(?P<base>[0-9a-f]+)%N;"
    r"\s*seg_size\s*:=\s*0x(?P<size>[0-9a-f]+)%N;"
    r'\s*seg_perms\s*:=\s*"(?P<perms>[^"]*)";'
    r"\s*seg_bytes\s*:=\s*(?P<bytes>.*?)\s*\|\}\.", re.DOTALL)
PHDRS_RE = re.compile(
    r"ph_addr\s*:=\s*0x(?P<addr>[0-9a-f]+)%N;"
    r"\s*ph_ent\s*:=\s*(?P<ent>\d+)%N;"
    r"\s*ph_num\s*:=\s*(?P<num>\d+)%N")


def chunk_names(name: str, definition: str) -> tuple[str, str, int, int | None] | None:
    """(file, dependency alias, segment, chunk) elf-snapshot gives a chunk
    definition (`_hex_file_name` and `_emit_coq` in tools/elf_snapshot.py):
    `<name>_seg_bytes_SSS` from `<name>_seg_SSS.hex` for a one-chunk
    segment, `<name>_seg_bytes_SSS_CCC` from `<name>_seg_SSS_chunk_CCC.hex`
    for each chunk of a longer one; None for any other name."""
    match = re.fullmatch(re.escape(name) + r"_seg_bytes_(\d{3})(?:_(\d{3}))?", definition)
    if not match:
        return None
    seg, chunk = match[1], match[2]
    if chunk is None:
        return f"{name}_seg_{seg}.hex", f"{name}_seg_dep_{seg}", int(seg), None
    return f"{name}_seg_{seg}_chunk_{chunk}.hex", f"{name}_seg_dep_{seg}_{chunk}", int(seg), int(chunk)


def read_image(directory: Path, role: str, example: str) -> Image:
    check_example_name(example)
    name = role + "MemImage"
    source = directory / (name + ".v")
    if not source.is_file():
        raise ValueError(f"missing snapshot file: {source}")
    text = strip_comments(source.read_text())
    deps = {}
    for dep in DEPENDENCY_RE.finditer(text):
        filename, definition = dep.group("file", "definition")
        if Path(filename).name != filename or not filename.endswith(".hex"):
            raise ValueError("snapshot chunks must be local .hex files")
        if definition in deps:
            raise ValueError("duplicate chunk definition: " + definition)
        names = chunk_names(name, definition)
        if names is None:
            raise ValueError("unsupported chunk definition name: " + definition)
        if filename != names[0]:
            raise ValueError("chunk filename does not match its definition")
        deps[definition] = directory / filename
    if len(deps) != len(re.findall(r"\bReadFileString\b", text)):
        raise ValueError("unsupported or duplicate snapshot dependency syntax")
    segments = []
    used = []
    for match in SEGMENT_RE.finditer(text):
        segment_name = f"{name}_segment_{match.group('idx')}"
        if not match.group(0).startswith("Definition " + segment_name + " :"):
            raise ValueError("unexpected segment name")
        raw_chunks = match.group("bytes").strip()
        if not re.fullmatch(r"\[\s*\w+(?:\s*;\s*\w+)*\s*\]", raw_chunks):
            raise ValueError("unsupported segment chunk list")
        chunks = []
        listed = re.findall(r"\w+", raw_chunks)
        # elf-snapshot's order: this segment's chunks, one unnumbered or
        # numbered from 000 in sequence.
        placed = [chunk_names(name, c)[2:] if chunk_names(name, c) else None for c in listed]
        index = int(match.group("idx"))
        if placed != ([(index, None)] if len(listed) == 1 else [(index, k) for k in range(len(listed))]):
            raise ValueError(f"{segment_name} lists chunks out of elf-snapshot's order: {', '.join(listed)}")
        for chunk_name in listed:
            if chunk_name not in deps:
                raise ValueError("unknown chunk: " + chunk_name)
            path = deps[chunk_name]
            if not path.is_file():
                raise ValueError(f"missing snapshot chunk file: {path}")
            content = path.read_bytes().decode("ascii", errors="replace")
            # Keep the primitive-string bytes exactly; no whitespace cleanup
            # or case normalization that could change the logical snapshot.
            if not re.fullmatch(r"(?:[0-9a-f]{2})*", content):
                raise ValueError("chunk is not exact lowercase hex: " + str(path))
            chunks.append((chunk_name, content))
            used.append(path)
        base, size = (int(match.group(k), 16) for k in ("base", "size"))
        if sum(len(chunk) // 2 for _, chunk in chunks) != size:
            raise ValueError("chunk length differs from seg_size: " + segment_name)
        perms = match.group("perms")
        if not re.fullmatch(r"[r-][w-][x-]", perms):
            raise ValueError("unsupported permission string: " + perms)
        segments.append(Segment(segment_name, base, size, perms, tuple(chunks)))
    if not segments or len(segments) != len(re.findall(r"\bseg_base\s*:=", text)):
        raise ValueError("unrecognized or missing segment record")
    ordered = sorted(segments, key=lambda s: s.base)
    for low, high in zip(ordered, ordered[1:]):
        if high.base < low.base + low.size:
            raise ValueError(f"overlapping segments: {low.name} [0x{low.base:x}, "
                             f"0x{low.base + low.size:x}) and {high.name} at 0x{high.base:x}")
    if any(s.size == 0 for s in segments):
        raise ValueError("empty segment record")
    loaded = one(rf"Definition {name}_loaded_segments\s*:\s*list Segment\s*:=\s*\[(.*?)\]\.",
                 text, "loaded segment list", re.S)
    listed = [x.strip() for x in loaded[1].split(";")]
    if listed != [s.name for s in segments]:
        raise ValueError("loaded segment order differs from the records")
    if set(used) != set(deps.values()):
        raise ValueError("unused snapshot byte dependency")
    pc = int(one(rf"Definition {name}_init_pc\s*:\s*N\s*:=\s*0x([0-9a-f]+)%N\.",
                 text, "entry point")[1], 16)
    ph = one(PHDRS_RE, text, "program headers")
    image = Image(example, name, role, tuple(segments), pc, int(ph["addr"], 16),
                  int(ph["ent"]), int(ph["num"]), tuple([source] + used))
    if snapshot_tokens(text) != snapshot_tokens(snapshot_skeleton(image)):
        raise ValueError("snapshot is outside the supported elf-snapshot syntax or exports different bindings")
    return image


def dune_text_ranges(dune_text: str, example: str) -> dict[str, tuple[int, int] | None]:
    """The explicit .text ranges the example's gen-fd-lemmas rule passes.

    Every example has exactly one such rule in theories/Examples/dune; a
    flag this tool does not interpret (another image module, say) is
    refused rather than ignored, since it would change which words the
    Rocq code file covers.
    """
    if "#|" in dune_text or "#;" in dune_text:
        # A block or datum comment can hide or split a rule, and this reader
        # strips only line comments; the file has neither today.
        raise ValueError("theories/Examples/dune has a #| or #; comment, which this reader does not strip")
    text = re.sub(r";[^\n]*", "", dune_text)
    rules = re.findall(r"\(run\s+python3\s+%\{project_root\}/tools/gen_fd_lemmas\.py\s+"
                       + re.escape(example) + r"(\s[^()]*)\)", text)
    if len(rules) != 1:
        raise ValueError(f"expected exactly one gen_fd_lemmas rule for {example} in "
                         f"theories/Examples/dune, found {len(rules)}")
    args = rules[0].split()
    ranges: dict[str, tuple[int, int] | None] = {"Source": None, "Target": None}
    index = 0
    while index < len(args):
        flag = args[index]
        value = args[index + 1] if index + 1 < len(args) else None
        if flag == "--examples-dir" and value != "..":
            # The rule runs in the example's own directory, so `..` is the
            # examples tree this tool reads; anything else points Rocq at
            # another snapshot.
            raise ValueError(f"unsupported --examples-dir value for {example}: {value!r}")
        if flag in ("--examples-dir", "--loadpath", "--out"):
            pass
        elif flag in ("--source-text", "--target-text"):
            match = re.fullmatch(r"0x([0-9a-f]+):0x([0-9a-f]+)", value or "")
            if not match:
                raise ValueError(f"unsupported {flag} value in the dune rule: {value!r}")
            lo, hi = int(match[1], 16), int(match[2], 16)
            if not lo < hi:
                raise ValueError(f"empty {flag} range in the dune rule: {value}")
            ranges["Source" if flag == "--source-text" else "Target"] = (lo, hi)
        else:
            raise ValueError(f"unsupported gen_fd_lemmas flag for {example}: {flag}")
        index += 2
    return ranges


def text_words(image: Image, explicit: tuple[int, int] | None):
    """(first pc, words, writable) of the image's .text.

    The locator is gen-fd-lemmas' `read_text_words`, restated over the
    validated image rather than re-reading the Rocq source: the maximal
    nonzero run inside the executable PT_LOAD's file extent, its end rounded
    up to a whole word. tools/test_gen_lean_example_image.py holds the two
    to the same answer on every committed example. They can differ on a
    snapshot elf-snapshot does not write: this reads it with its Rocq
    comments stripped and gen-fd-lemmas reads it raw, so a comment spelling
    a program header record ahead of the real one steers only gen-fd-lemmas.
    """
    executable = [seg for seg in image.segments if "x" in seg.perms]
    if len(executable) != 1:
        raise ValueError(f"{image.name}: {len(executable)} executable segments, expected exactly one")
    seg = executable[0]
    writable = "w" in seg.perms
    data = seg.data()
    if explicit is not None:
        lo, hi = explicit
        if not seg.base <= lo < hi <= seg.base + seg.size:
            raise ValueError(f"{image.name}: text range 0x{lo:x}:0x{hi:x} is outside "
                             "its executable segment")
    elif writable:
        raise ValueError(f"{image.name}: the executable segment is writable, so its .text "
                         "needs an explicit range in the example's gen_fd_lemmas rule")
    else:
        vaddr, filesz = exec_load_extent(image)
        lo, hi = max(vaddr, seg.base), min(vaddr + filesz, seg.base + seg.size)
        if lo >= hi:
            raise ValueError(f"{image.name}: the executable PT_LOAD misses its segment")
        while lo < hi and data[lo - seg.base] == 0:
            lo += 1
        while hi > lo and data[hi - 1 - seg.base] == 0:
            hi -= 1
        if lo == hi:
            raise ValueError(f"{image.name}: the executable segment is all zeroes")
        hi = lo + -(-(hi - lo) // 4) * 4
    if lo % 4 or (hi - lo) % 4 or hi > seg.base + seg.size:
        raise ValueError(f"{image.name}: text range 0x{lo:x}:0x{hi:x} is not a whole "
                         "number of aligned words")
    words = [int.from_bytes(data[pc - seg.base:pc - seg.base + 4], "little")
             for pc in range(lo, hi, 4)]
    return lo, words, writable


def exec_load_extent(image: Image) -> tuple[int, int]:
    """[p_vaddr, p_vaddr + p_filesz) of the one PT_LOAD with PF_X."""
    end = image.ph_addr + image.ph_ent * image.ph_num
    cover = [s for s in image.segments if s.base <= image.ph_addr and end <= s.base + s.size]
    if image.ph_ent < 56:
        raise ValueError(f"{image.name}: ph_ent {image.ph_ent} is shorter than an Elf64_Phdr (56 bytes)")
    if not cover:
        raise ValueError(f"{image.name}: the program header table is not inside a segment")
    table = cover[0].data()[image.ph_addr - cover[0].base:end - cover[0].base]
    loads = []
    for i in range(image.ph_num):
        entry = table[i * image.ph_ent:(i + 1) * image.ph_ent]
        p_type, p_flags = (int.from_bytes(entry[k:k + 4], "little") for k in (0, 4))
        if p_type == 1 and p_flags & 1:
            loads.append((int.from_bytes(entry[16:24], "little"),
                          int.from_bytes(entry[32:40], "little")))
    if len(loads) != 1:
        raise ValueError(f"{image.name}: {len(loads)} executable PT_LOAD entries, expected one")
    return loads[0]


@dataclass(frozen=True)
class Decoded:
    """One proposed instruction: an `instr` constructor and its fields.

    Field order is the constructor's argument order in
    lean/LinuxProcessSemantics/Riscv/Instr.lean. A field is a `Reg`, an
    `Imm` at its encoded width (no sign extension, as `Instr` keeps it), a
    `Small` (shift amounts and fence fields), or a `str` naming an enum
    constructor or a Bool literal.
    """
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
    """A shift amount or fence field, written in decimal."""
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

    Arm for arm the 32-bit `decode` of lean/LinuxProcessSemantics/Riscv/
    Decode.lean, which mirrors theories/Riscv/Decode.v's `decode`; the width
    dispatch is `decode_any` in lean/LinuxProcessSemantics/Riscv/DecodeC.lean
    (theories/Riscv/DecodeC.v's `decode_any`, less its unported RVC half).
    Every word Lean's decoder answers `none` for is refused, each with the
    reason, so nothing is emitted that the kernel would reject. Nothing
    depends on this being right: the generated theorem is the check.
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


# `rfl` between a chunk's literal and its character list recurses in
# proportion to the chunk's length. The file-wide maxRecDepth below is
# enough for a one-page chunk (8192 hex digits), which is every chunk of
# every example but tail1_ns's two zero-filled 24576-digit ones (Source
# seg_003, Target seg_002), where it fails with "maximum recursion depth
# has been reached". A longer chunk gets a limit of its own, sixteen per
# digit; 262144 was measured to be enough for Source's, and this gives
# each 393216.
PAGE_CHUNK_DIGITS = 8192
DEPTH_PER_DIGIT = 16


def chunk_depth(content: str) -> list[str]:
    if len(content) <= PAGE_CHUNK_DIGITS:
        return []
    return [f"set_option maxRecDepth {DEPTH_PER_DIGIT * len(content)} in"]


def image_module(image: Image) -> str:
    ns = namespace(image.example)
    # rwx_flag_ns's modules are the pilot's text to the byte, header included.
    tool = "gen_lean_image.py" if image.example == "rwx_flag_ns" else "gen_lean_example_image.py"
    lines = [f"-- Generated by tools/{tool}; edit the committed snapshot inputs.",
             "import LinuxProcessSemantics.Common.ImageBytes", "",
             f"namespace {ns}.{image.name}", "",
             "open LinuxProcessSemantics.LinuxProcessSem.MemImageType",
             "open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
             "open LinuxProcessSemantics.Common.ImageBytes", "",
             "set_option maxRecDepth 65536", "set_option maxHeartbeats 1000000", ""]
    for seg in image.segments:
        for name, content in seg.chunks:
            term = chars_term(content)
            # An argument the term gives simp nothing to rewrite with is a
            # linter warning (a lone `List.replicate` has no `++`).
            simp = ", ".join([f"{name}_chars"] + [lemma for lemma, shape in
                             (("List.all_append", " ++ "), ("List.all_replicate", "List.replicate "))
                             if shape in term])
            lines += [f"def {name} : String := {json.dumps(content)}",
                      f"def {name}_chars : List Char := {term}",
                      *chunk_depth(content),
                      f"theorem {name}_chars_eq : {name} = String.ofList {name}_chars := rfl",
                      f"theorem {name}_ascii : {name}_chars.all (fun c => c.utf8Size == 1) = true := by",
                      f"  simp only [{simp}]",
                      "  decide +kernel",
                      f"theorem {name}_hex : {name}_chars.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true := by",
                      f"  simp only [{simp}]",
                      "  decide +kernel",
                      f"theorem {name}_size : {name}.utf8ByteSize = {len(content)} := by",
                      f"  rw [{name}_chars_eq, utf8ByteSize_ofList_ascii _ {name}_ascii]",
                      "  decide +kernel", ""]
        lines += [f"def {seg.name} : Segment :=",
                  f"  {{ seg_base := 0x{seg.base:x}, seg_size := 0x{seg.size:x},",
                  f"    seg_perms := {json.dumps(seg.perms)},",
                  "    seg_bytes := [" + ", ".join(n for n, _ in seg.chunks) + "] }", ""]
        chunks = "[" + ", ".join(n + "_chars" for n, _ in seg.chunks) + "]"
        reprs = ", ".join(n + "_chars_eq" for n, _ in seg.chunks)
        hname = seg.name + "_ascii"
        lines += [f"private theorem {hname} :",
                  f"    ∀ cs ∈ ({chunks} : List (List Char)), cs.all (fun c => c.utf8Size == 1) = true := by",
                  "  intro cs h",
                  "  simp only [List.mem_cons, List.not_mem_nil, or_false] at h",
                  "  rcases h with " + " | ".join("rfl" for _ in seg.chunks)]
        for name, _ in seg.chunks:
            lines.append(f"  · exact {name}_ascii")
        lines += ["", f"theorem {seg.name}_read_ascii (off n : Nat) :",
                  f"    segment_read_bytes {seg.name}.seg_bytes off n =",
                  f"      ascii_segment_read_bytes {chunks} off n := by",
                  f"  change segment_read_bytes [{', '.join(n for n, _ in seg.chunks)}] off n = _",
                  f"  rw [{reprs}]",
                  f"  exact segment_read_bytes_ascii {chunks} {hname} off n", "",
                  f"theorem {seg.name}_byte_ascii (off : Nat) :",
                  f"    segment_byte_at {seg.name}.seg_bytes off = ascii_segment_byte_at {chunks} off := by",
                  f"  change segment_byte_at [{', '.join(n for n, _ in seg.chunks)}] off = _",
                  f"  rw [{reprs}]",
                  f"  exact segment_byte_at_ascii {chunks} {hname} off", ""]
    lines += [f"def {image.name}_loaded_segments : List Segment :=",
              "  [" + ", ".join(s.name for s in image.segments) + "]",
              f"def {image.name}_init_pc : Nat := 0x{image.pc:x}",
              f"def {image.name}_phdrs : PhdrInfo :=",
              f"  {{ ph_addr := 0x{image.ph_addr:x}, ph_ent := {image.ph_ent}, ph_num := {image.ph_num} }}",
              "", f"namespace {image.role}",
              f"abbrev loaded_segments := {image.name}_loaded_segments",
              f"abbrev init_pc := {image.name}_init_pc",
              f"abbrev phdrs := {image.name}_phdrs",
              "def image : Image := Image.mkImage loaded_segments init_pc phdrs",
              f"end {image.role}", "", f"end {ns}.{image.name}", ""]
    return "\n".join(lines)


def containing(image: Image, address: int, width: int) -> Segment:
    for seg in image.segments:
        if seg.base <= address and address + width <= seg.base + seg.size:
            return seg
    raise ValueError(f"{image.name}: [0x{address:x}, 0x{address + width:x}) is in no segment")


def code_module(images: tuple[Image, ...], ranges: dict) -> str:
    example = images[0].example
    ns = namespace(example)
    lines = ["-- Generated; every proposed fetch and decode is checked by Lean's kernel.",
             "import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
             "import LinuxProcessSemantics.EquivalenceDefinition.Equivalence",
             "import LinuxProcessSemantics.Riscv.DecodeC"]
    lines += [f"import {ns}.{image.name}" for image in images]
    lines += ["", f"namespace {ns}.{example}_code", "",
              "open LinuxProcessSemantics.Riscv.Prelude",
              "open LinuxProcessSemantics.LinuxProcessSem.MemImageType",
              "open LinuxProcessSemantics.LinuxProcessSem.BvBase",
              "open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
              "open LinuxProcessSemantics.Common.ImageBytes",
              "open LinuxProcessSemantics.EquivalenceDefinition.Equivalence",
              "open LinuxProcessSemantics.Riscv.DecodeC"]
    lines += [f"open {ns}.{image.name}" for image in images]
    lines += ["", "set_option maxRecDepth 65536", "set_option maxHeartbeats 1000000", ""]
    writable = {}
    for image in images:
        role, prefix = image.role.lower(), PREFIX[image.role]
        lines += [f"abbrev {role}_segs := {image.role}.loaded_segments",
                  f"abbrev {role}_phdrs := {image.role}.phdrs", ""]
        base, words, writable[image.role] = text_words(image, ranges[image.role])
        fetch = "fetch_word_wx" if writable[image.role] else "fetch_word"
        fetch_rule = fetch + "_of_bytes"
        for index, word in enumerate(words):
            pc = base + 4 * index
            try:
                term = decode(word).lean()
            except ValueError as exc:
                raise ValueError(f"{image.name} at pc 0x{pc:x}: {exc}") from None
            seg = containing(image, pc, 4)
            byte_args = " ".join(f"0x{b:02x}" for b in word.to_bytes(4, "little"))
            byte_list = "[" + ", ".join(f"0x{b:02x}" for b in word.to_bytes(4, "little")) + "]"
            chunks = "[" + ", ".join(name + "_chars" for name, _ in seg.chunks) + "]"
            lines += [f"theorem {prefix}F_{pc:x} : {fetch} {role}_segs 0x{pc:x} = some 0x{word:08x} := by",
                      f"  apply {fetch_rule} {role}_segs {seg.name} 0x{pc:x} {byte_args}",
                      "  · decide +kernel",
                      "  · rfl",
                      "  · decide +kernel",
                      "  · decide +kernel",
                      f"  · have hr : ascii_segment_read_bytes {chunks} {pc - seg.base} 4 = some {byte_list} := by",
                      "      decide +kernel",
                      f"    exact ({seg.name}_read_ascii {pc - seg.base} 4).trans hr",
                      f"theorem {prefix}D_{pc:x} : decode_any 0x{word:08x} = some ({term}, 4) := by",
                      "  decide +kernel", ""]
    by_role = {image.role: image for image in images}
    for role, name, address, width in STORE_FACTS.get(example, ()):
        image = by_role[role]
        seg = containing(image, address, width)
        raw = seg.data()
        lines += [f"theorem {name} : store_ok {role.lower()}_segs (fun _ => none) 0x{address:x} {width} = true := by"]
        indent = "  "
        for i in range(width):
            byte = raw[address + i - seg.base]
            lines += [f"{indent}apply store_ok_empty_step_of_byte {role.lower()}_segs {seg.name} _ {width - i - 1} 0x{byte:02x}",
                      f"{indent}· rfl", f"{indent}· decide +kernel",
                      f"{indent}· exact ({seg.name}_byte_ascii _).trans (by decide +kernel)",
                      f"{indent}·"]
            indent += "  "
        lines += [f"{indent}rfl", ""]
    lines += ["private theorem image_entry_of_wx (segs : List Segment) (pc : Nat) (w : BitVec 32)",
              "    (h : fetch_word_wx segs (Z_to_bv 64 (pc : Int)) = some w) :",
              "    image_entry_fetchable segs pc = true := by",
              "  cases hf : fetch_word segs (Z_to_bv 64 (pc : Int)) <;>",
              "    simp only [image_entry_fetchable, hf, h]", "",
              "private theorem image_entry_of_ro (segs : List Segment) (pc : Nat) (w : BitVec 32)",
              "    (h : fetch_word segs (Z_to_bv 64 (pc : Int)) = some w) :",
              "    image_entry_fetchable segs pc = true := by",
              "  simp only [image_entry_fetchable, h]", "",
              "private theorem image_phdrs_of_read (segs : List Segment) (ph : PhdrInfo)",
              "    (hn : 0 < ph.ph_num) (he : 0 < ph.ph_ent)",
              "    (hr : (memory_read segs (Z_to_bv 64 (ph.ph_addr : Int)) (ph.ph_num * ph.ph_ent)).isSome = true) :",
              "    image_phdrs_readable segs ph = true := by",
              "  simp [image_phdrs_readable, hn, he, hr]", ""]
    for image in images:
        role, prefix = image.role.lower(), PREFIX[image.role]
        ph_seg = containing(image, image.ph_addr, image.ph_ent * image.ph_num)
        base, words, _ = text_words(image, ranges[image.role])
        if not base <= image.pc < base + 4 * len(words) or image.pc % 4:
            raise ValueError(f"{image.name}: entry 0x{image.pc:x} is not a .text word")
        entry = "wx" if writable[image.role] else "ro"
        lines += [f"theorem {image.role}Wf : IMAGE_WF {image.role}.image := by",
                  "  constructor",
                  f"  · exact image_entry_of_{entry} {role}_segs {image.role}.init_pc _ {prefix}F_{image.pc:x}",
                  f"  · apply image_phdrs_of_read {role}_segs {role}_phdrs",
                  "    · decide +kernel", "    · decide +kernel",
                  f"    · apply memory_read_isSome_of_segment {role}_segs {ph_seg.name} _ _",
                  "      · rfl", "      · decide +kernel"]
        if len(ph_seg.chunks) == 1:
            chunk_name = ph_seg.chunks[0][0]
            lines += [f"      · exact (congrArg Option.isSome ({ph_seg.name}_read_ascii _ _)).trans",
                      f"          (ascii_segment_read_bytes_single_isSome {chunk_name}_chars",
                      f"            {chunk_name}_hex _ _ (by decide +kernel))"]
        else:
            lines += [f"      · exact (congrArg Option.isSome ({ph_seg.name}_read_ascii _ _)).trans (by decide +kernel)"]
        lines += ["  · decide +kernel", ""]
    lines += [f"end {ns}.{example}_code", ""]
    return "\n".join(lines)


def outputs(example: str, examples_dir: Path = EXAMPLES_DIR,
            dune: Path | None = None) -> dict[str, str]:
    """Every generated file of the example, by file name, in memory."""
    check_example_name(example)
    directory = examples_dir / example
    if not directory.is_dir():
        raise ValueError(f"no such example directory: {directory}")
    dune = dune or examples_dir / "dune"
    if not dune.is_file():
        raise ValueError(f"missing file: {dune}")
    ranges = dune_text_ranges(dune.read_text(), example)
    images = tuple(read_image(directory, role, example) for role in ROLES)
    result = {image.name + ".lean": image_module(image) for image in images}
    result[example + "_code.lean"] = code_module(images, ranges)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("example", help="an example under theories/Examples, e.g. cat1024_ns")
    parser.add_argument("--examples-dir", type=Path, default=EXAMPLES_DIR,
                        help="the examples tree holding <example>/ and dune (default: %(default)s)")
    parser.add_argument("--out-dir", type=Path, required=True,
                        help="directory the three files are written into")
    parser.add_argument("--module", help="write only this module (a file stem)")
    args = parser.parse_args()
    try:
        generated = outputs(args.example, args.examples_dir)
        if args.module and args.module + ".lean" not in generated:
            raise ValueError(f"{args.example} has no module {args.module}")
        args.out_dir.mkdir(parents=True, exist_ok=True)
        for filename, text in generated.items():
            if args.module and filename != args.module + ".lean":
                continue
            path = args.out_dir / filename
            if not path.exists() or path.read_text() != text:
                path.write_text(text)
    except (ValueError, OSError) as exc:
        parser.exit(1, "gen_lean_example_image.py: " + str(exc) + "\n")


if __name__ == "__main__":
    main()
