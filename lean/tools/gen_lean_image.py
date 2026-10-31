#!/usr/bin/env python3
"""Generate the rwx_flag_ns Lean images and checked fetch/decode facts.

The input is the committed snapshot, including every named .hex chunk. This
pilot deliberately accepts only elf-snapshot's record syntax and the integer
instructions in this example. The small decoder below proposes Lean terms;
the generated theorems check them against the actual Lean decoder. It is not
an ISA specification or an executable-checker replacement.
"""

from dataclasses import dataclass
from pathlib import Path
import argparse
import itertools
import json
import re

import gen_fd_lemmas


EXAMPLE = "rwx_flag_ns"
NAMESPACE = "LinuxProcessSemantics.Examples." + EXAMPLE
SOURCE_TEXT = (0x10078, 0x100E4)
TARGET_TEXT = (0x1001190, 0x10011A8)


@dataclass(frozen=True)
class Segment:
    name: str
    base: int
    size: int
    perms: str
    chunks: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class Image:
    name: str
    role: str
    segments: tuple[Segment, ...]
    pc: int
    ph_addr: int
    ph_ent: int
    ph_num: int
    inputs: tuple[Path, ...]


def one(pattern, text, label, flags=0):
    found = list(re.finditer(pattern, text, flags))
    if len(found) != 1:
        raise ValueError(f"expected exactly one {label}, found {len(found)}")
    return found[0]


def strip_comments(text: str) -> str:
    """Remove nested Rocq comments without treating quoted strings as comments."""
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
            index = chunk_name.removeprefix(name + "_seg_bytes_")
            filename, alias = f"{name}_seg_{index}.hex", f"{name}_seg_dep_{index}"
            lines += [f'From {NAMESPACE} Extra Dependency "{filename}" as {alias}.',
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


def read_image(directory: Path, role: str) -> Image:
    name = role + "MemImage"
    source = directory / (name + ".v")
    text = strip_comments(source.read_text())
    deps = {}
    for dep in gen_fd_lemmas.DEPENDENCY_RE.finditer(text):
        filename, definition = dep.group("file", "definition")
        if Path(filename).name != filename or not filename.endswith(".hex"):
            raise ValueError("snapshot chunks must be local .hex files")
        if definition in deps:
            raise ValueError("duplicate chunk definition: " + definition)
        if not re.fullmatch(re.escape(name) + r"_seg_bytes_\d{3}", definition):
            raise ValueError("unsupported chunk definition name: " + definition)
        if filename != definition.replace("_seg_bytes_", "_seg_") + ".hex":
            raise ValueError("chunk filename does not match its definition")
        deps[definition] = directory / filename
    if len(deps) != len(re.findall(r"\bReadFileString\b", text)):
        raise ValueError("unsupported or duplicate snapshot dependency syntax")
    segments = []
    used = []
    for match in gen_fd_lemmas.SEGMENT_RE.finditer(text):
        segment_name = f"{name}_segment_{match.group('idx')}"
        if not match.group(0).startswith("Definition " + segment_name + " :"):
            raise ValueError("unexpected segment name")
        raw_chunks = match.group("bytes").strip()
        if not re.fullmatch(r"\[\s*\w+(?:\s*;\s*\w+)*\s*\]", raw_chunks):
            raise ValueError("unsupported segment chunk list")
        names = re.findall(r"\w+", raw_chunks)
        chunks = []
        for chunk_name in names:
            if chunk_name not in deps:
                raise ValueError("unknown chunk: " + chunk_name)
            path = deps[chunk_name]
            content = path.read_bytes().decode("ascii")
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
    loaded = one(rf"Definition {name}_loaded_segments\s*:\s*list Segment\s*:=\s*\[(.*?)\]\.",
                 text, "loaded segment list", re.S)
    listed = [x.strip() for x in loaded[1].split(";")]
    if listed != [s.name for s in segments]:
        raise ValueError("loaded segment order differs from the records")
    if set(used) != set(deps.values()):
        raise ValueError("unused snapshot byte dependency")
    pc = int(one(rf"Definition {name}_init_pc\s*:\s*N\s*:=\s*0x([0-9a-f]+)%N\.",
                 text, "entry point")[1], 16)
    ph = one(gen_fd_lemmas.PHDRS_RE, text, "program headers")
    image = Image(name, role, tuple(segments), pc, int(ph["addr"], 16),
                  int(ph["ent"]), int(ph["num"]), tuple([source] + used))
    if snapshot_tokens(text) != snapshot_tokens(snapshot_skeleton(image)):
        raise ValueError("snapshot is outside the supported elf-snapshot syntax or exports different bindings")
    return image


def propose_instruction(word: int) -> str:
    """A bounded term proposer. Every result is checked by Lean's decode_any."""
    op = word & 0x7f
    rd, rs1, rs2 = (word >> k & 31 for k in (7, 15, 20))
    f3, f7, imm = word >> 12 & 7, word >> 25, word >> 20
    if op in (0x37, 0x17):
        return f".{ 'Lui' if op == 0x37 else 'Auipc'} {rd} 0x{word >> 12:x}"
    if op == 0x6f:
        j = ((word >> 31) << 20 | (word >> 12 & 255) << 12
             | (word >> 20 & 1) << 11 | (word >> 21 & 1023) << 1)
        return f".Jal {rd} 0x{j:x}"
    if op == 0x67 and f3 == 0:
        return f".Jalr {rd} {rs1} 0x{imm:x}"
    if op == 0x03 and f3 in (3, 4):
        size, signed = ("SZ8", "true") if f3 == 3 else ("SZ1", "false")
        return f".Load .{size} {signed} {rd} {rs1} 0x{imm:x}"
    if op == 0x23 and f3 in (0, 3):
        offset = (word >> 25) << 5 | word >> 7 & 31
        return f".Store .{'SZ1' if f3 == 0 else 'SZ8'} {rs1} {rs2} 0x{offset:x}"
    if op == 0x13 and f3 == 0:
        return f".OpImm .ALU_ADD {rd} {rs1} 0x{imm:x}"
    if op == 0x13 and f3 == 1 and word >> 26 == 0:
        return f".ShiftImm .ALU_SLL {rd} {rs1} {word >> 20 & 63}"
    if op == 0x33 and f3 == 0 and f7 == 0:
        return f".Op .ALU_ADD {rd} {rs1} {rs2}"
    if word == 0x73:
        return ".Ecall"
    raise ValueError(f"pilot term proposer does not support instruction 0x{word:08x}")


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


def text_words(image: Image, bounds: tuple[int, int]):
    """Select certificate addresses from validated image data only.

    These explicit ranges are the two existing pilot text sections. They
    choose facts to prove and impose no restriction on the execution model.
    Re-reading the raw Rocq source here would give comments a second, different
    interpretation and could introduce untracked byte dependencies.
    """
    lo, hi = bounds
    executable = [seg for seg in image.segments if "x" in seg.perms]
    if len(executable) != 1:
        raise ValueError("pilot requires exactly one executable segment")
    seg = executable[0]
    if not seg.base <= lo < hi <= seg.base + seg.size or lo % 4 or (hi - lo) % 4:
        raise ValueError("pilot text range is outside its executable segment or misaligned")
    data = bytes.fromhex("".join(content for _, content in seg.chunks))
    words = [int.from_bytes(data[pc - seg.base:pc - seg.base + 4], "little")
             for pc in range(lo, hi, 4)]
    return lo, words, "w" in seg.perms


def image_module(image: Image) -> str:
    lines = ["-- Generated by tools/gen_lean_image.py; edit the committed snapshot inputs.",
             "import LinuxProcessSemantics.Common.ImageBytes", "",
             f"namespace {NAMESPACE}.{image.name}", "",
             "open LinuxProcessSemantics.LinuxProcessSem.MemImageType",
             "open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
             "open LinuxProcessSemantics.Common.ImageBytes", "",
             "set_option maxRecDepth 65536", "set_option maxHeartbeats 1000000", ""]
    for seg in image.segments:
        for name, content in seg.chunks:
            lines += [f"def {name} : String := {json.dumps(content)}",
                      f"def {name}_chars : List Char := {chars_term(content)}",
                      f"theorem {name}_chars_eq : {name} = String.ofList {name}_chars := rfl",
                      f"theorem {name}_ascii : {name}_chars.all (fun c => c.utf8Size == 1) = true := by",
                      f"  simp only [{name}_chars, List.all_append, List.all_replicate]",
                      "  decide +kernel",
                      f"theorem {name}_hex : {name}_chars.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true := by",
                      f"  simp only [{name}_chars, List.all_append, List.all_replicate]",
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
              f"end {image.role}", "", f"end {NAMESPACE}.{image.name}", ""]
    return "\n".join(lines)


def code_module(images: tuple[Image, ...]) -> str:
    lines = ["-- Generated; every proposed fetch and decode is checked by Lean's kernel.",
             "import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
             "import LinuxProcessSemantics.EquivalenceDefinition.Equivalence",
             "import LinuxProcessSemantics.Riscv.DecodeC"]
    lines += [f"import {NAMESPACE}.{image.name}" for image in images]
    lines += ["", f"namespace {NAMESPACE}.rwx_flag_ns_code", "",
              "open LinuxProcessSemantics.Riscv.Prelude",
              "open LinuxProcessSemantics.LinuxProcessSem.MemImageType",
              "open LinuxProcessSemantics.LinuxProcessSem.BvBase",
              "open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics",
              "open LinuxProcessSemantics.Common.ImageBytes",
              "open LinuxProcessSemantics.EquivalenceDefinition.Equivalence",
              "open LinuxProcessSemantics.Riscv.DecodeC"]
    lines += [f"open {NAMESPACE}.{image.name}" for image in images]
    lines += ["", "set_option maxRecDepth 65536", "set_option maxHeartbeats 1000000", ""]
    for image, prefix in zip(images, ("S", "T")):
        role = image.role.lower()
        lines += [f"abbrev {role}_segs := {image.role}.loaded_segments",
                  f"abbrev {role}_phdrs := {image.role}.phdrs", ""]
        base, words, writable = text_words(image, SOURCE_TEXT if prefix == "S" else TARGET_TEXT)
        for index, word in enumerate(words):
            pc = base + 4 * index
            fetch = "fetch_word_wx" if writable else "fetch_word"
            term = propose_instruction(word)
            seg = next(s for s in image.segments if s.base <= pc and pc + 4 <= s.base + s.size)
            byte_args = " ".join(f"0x{b:02x}" for b in word.to_bytes(4, "little"))
            byte_list = "[" + ", ".join(f"0x{b:02x}" for b in word.to_bytes(4, "little")) + "]"
            chunks = "[" + ", ".join(name + "_chars" for name, _ in seg.chunks) + "]"
            fetch_rule = "fetch_word_wx_of_bytes" if writable else "fetch_word_of_bytes"
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
    for role, name, address, width in (("source", "source_store_environ", 0x100e8, 8),
                                       ("source", "source_store_flag", 0x100e4, 1),
                                       ("target", "target_store_flag", 0x10021a8, 1)):
        image = images[0 if role == "source" else 1]
        seg = next(s for s in image.segments if s.base <= address and address + width <= s.base + s.size)
        raw = bytes.fromhex("".join(content for _, content in seg.chunks))
        lines += [f"theorem {name} : store_ok {role}_segs (fun _ => none) 0x{address:x} {width} = true := by"]
        indent = "  "
        for i in range(width):
            byte = raw[address + i - seg.base]
            lines += [f"{indent}apply store_ok_empty_step_of_byte {role}_segs {seg.name} _ {width - i - 1} 0x{byte:02x}",
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
    for image, prefix in zip(images, ("S", "T")):
        role = image.role.lower()
        ph_seg = next(s for s in image.segments
                      if s.base <= image.ph_addr and image.ph_addr + image.ph_ent * image.ph_num <= s.base + s.size)
        lines += [f"theorem {image.role}Wf : IMAGE_WF {image.role}.image := by",
                  "  constructor",
                  f"  · exact image_entry_of_{'wx' if prefix == 'S' else 'ro'} {role}_segs {image.role}.init_pc _ {prefix}F_{image.pc:x}",
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
    lines += [f"end {NAMESPACE}.rwx_flag_ns_code", ""]
    return "\n".join(lines)


def outputs(directory: Path) -> dict[str, str]:
    images = tuple(read_image(directory, role) for role in ("Source", "Target"))
    result = {image.name + ".lean": image_module(image) for image in images}
    result[EXAMPLE + "_code.lean"] = code_module(images)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--example-dir", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--module", choices=("SourceMemImage", "TargetMemImage", EXAMPLE + "_code"))
    args = parser.parse_args()
    try:
        generated = outputs(args.example_dir)
        args.out_dir.mkdir(parents=True, exist_ok=True)
        for filename, text in generated.items():
            if args.module and filename != args.module + ".lean":
                continue
            path = args.out_dir / filename
            if not path.exists() or path.read_text() != text:
                path.write_text(text)
    except (ValueError, OSError) as exc:
        parser.exit(1, "gen_lean_image.py: " + str(exc) + "\n")


if __name__ == "__main__":
    main()
