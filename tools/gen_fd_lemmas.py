#!/usr/bin/env python3
"""gen_fd_lemmas.py — generate an example's Rocq fetch/decode lemma file.

For every instruction word in an example's two memory images, emit

    Lemma <P>F_<pc> : fetch_word <segs> 0x<pc> = Some <word>.
    Lemma <P>D_<pc> : decode_any (Z_to_bv 32 <word>) = Some (<AST>, <isz>%Z).

both proved by a VM-checked cast (vm_cast_no_check), wrapped in the
boilerplate header every theories/Examples/<name>/<name>_code.v shares.
The whole file is generated: dune builds it on demand (see
theories/Examples/dune), so it is not checked in.

WHERE THE WORDS COME FROM.  Not from the ELF binaries: those are build
products of the zig/musl toolchains and are .gitignore'd, so a clean
checkout has no disassembly to read.  What IS checked in — and what the
lemmas are actually about — are the memory images
(theories/Examples/<name>/{Source,Target}MemImage.v plus their .hex segment
bytes), so this script reads the instruction words straight out of those.
So the build needs no objdump: python3 and rocq are enough.

The .text of a snapshot is located as THE MAXIMAL RUN OF NONZERO BYTES
within the executable PT_LOAD's own extent [p_vaddr, p_vaddr + p_filesz),
read from the program header table the image maps (the same table the
model publishes through the auxv).  That is exact for every binary this
repo builds, and it is not a guess about ELF layout:

  - `-z separate-code` (source, see theories/Examples/README.md) and lld's
    default (target) both put code in a LOAD segment of its own, so the
    executable LOAD's file extent holds .text and nothing else.  The page-rounded SEGMENT
    holds more — its in-page slack maps the neighboring file bytes, e.g.
    the ELF header below a mid-page lld/zig .text — which is why the scan
    is bounded by the phdr-derived extent rather than the whole segment.
    (An image whose executable segment is WRITABLE — the merged w+x
    layout — holds headers and data inside the LOAD extent itself, so for it the range must be passed explicitly
    with --source-text/--target-text, and the emitted fetch lemmas are
    stated over the w+x static projection [fetch_word_wx]);
  - 0x00000000 is not a legal RISC-V encoding, so no instruction word inside
    .text can be zero and truncate the run early.

Each word is then required to decode, so a wrong range fails loudly here
rather than emitting lemmas that fail to compile later.  The decode AST is
obtained from Rocq itself (a generated Compute file running the
LinuxProcessSemantics.Riscv decoder), so there is no objdump-mnemonic ->
constructor mapping to get wrong.

The generated header defines an [Ltac vm_refl] that closes the emitted
equations (bv values carry a well-formedness proof whose vm-computed form
differs from the elaborated literal's, so the equation is decided via
bool_decide).  The canonical body is [vm_refl_bv], provided by the module
named with --steptac-module (default: Common/StepTac.v); the header aliases
it, so the idiom is defined in exactly one place.  (StepTac's [vm_refl_bv] is the twin of this tactic — keep the two in
sync.)

Usage:
  gen_fd_lemmas.py <name> [--examples-dir DIR] [--loadpath DIR] [--out FILE]
                   [--steptac-module MOD]
                   [--source-image NAME] [--target-image NAME]
      Emit theories/Examples/<name>/<name>_code.v to stdout (or FILE).

  --steptac-module names the module whose [vm_refl_bv] the generated
  [vm_refl] aliases (default: LinuxProcessSemantics.Common.StepTac).
  --source-image/--target-image name the memory-image modules to read,
  without the .v extension (defaults: SourceMemImage, TargetMemImage);
  the segment .hex files named by each image are found next to it.

Needs `rocq` on PATH, with the LinuxProcessSemantics library visible:
either installed (opam install .), or located by --loadpath, or discovered
from the current directory (a `_CoqProject`, then dune's `_build/default`
tree).  Nothing else — no cross-compiler, no objdump.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

# Definition <prefix>_segment_<nnn> : Segment := {| seg_base := 0x..%N;
# seg_size := 0x..%N; seg_perms := "r-x"; seg_bytes := ...;
# seg_kind := SegLoader |}, as
# elf-snapshot writes it.
SEGMENT_RE = re.compile(
    r"Definition\s+\w+_segment_(?P<idx>\d+)\s*:\s*Segment\s*:=\s*\{\|"
    r"\s*seg_base\s*:=\s*0x(?P<base>[0-9a-f]+)%N;"
    r"\s*seg_size\s*:=\s*0x(?P<size>[0-9a-f]+)%N;"
    r'\s*seg_perms\s*:=\s*"(?P<perms>[^"]*)";'
    r"\s*seg_bytes\s*:=\s*(?P<bytes>.*?);"
    r"\s*seg_kind\s*:=\s*SegLoader\s*\|\}\.", re.DOTALL)

DEPENDENCY_RE = re.compile(
    r'Extra Dependency\s+"(?P<file>[^"]+)"\s+as\s+(?P<dep>\w+)\.\s*'
    r'ReadFileString\s+(?P=dep)\s+As\s+(?P<definition>\w+)\.', re.DOTALL)

PHDRS_RE = re.compile(
    r"ph_addr\s*:=\s*0x(?P<addr>[0-9a-f]+)%N;"
    r"\s*ph_ent\s*:=\s*(?P<ent>\d+)%N;"
    r"\s*ph_num\s*:=\s*(?P<num>\d+)%N")

# Every example has BOTH images: an equivalence task is a pair of binaries,
# and theories/Examples/README.md's bring-up path reaches a compiling
# Proof.v (admit-first) rather than stopping at a lone reference program.
# A missing image is therefore an error, not an intermediate state.
# Each entry is (module, side, lemma prefix); the module (overridable with
# --source-image/--target-image) is both the .v file's basename and the
# prefix of its definitions (<module>_loaded_segments, <module>_phdrs,
# bounded hex payloads named by each image).
DEFAULT_IMAGES = [("SourceMemImage", "source", "S"),
                  ("TargetMemImage", "target", "T")]

HEADER = '''\
(** * {title}: fetch/decode facts for {subject}.

    AUTO-GENERATED — DO NOT EDIT, and not checked in.  Generated by
    gen-fd-lemmas from the committed memory {images} of
    theories/Examples/{name} ({image_list}, with the .hex segment bytes);
    dune builds it on demand, see theories/Examples/dune.  To regenerate by
    hand, from the repo root:

      gen-fd-lemmas {name}{regen_flags} --out {name}_code.v

    PROOF-SIDE FILE (not part of the trusted specification): every lemma is
    closed by a VM-checked cast, so nothing here is trusted — a wrong fact
    simply fails to compile. *)

From Stdlib Require Import NArith ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
{imports}
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
{steptac_import}
Import ListNotations.
Open Scope bv_scope.

{segs}

(** Each image's program-header record, published to the process through the
    auxv's AT_PHDR/AT_PHENT/AT_PHNUM (MemImageType.PhdrInfo): part of the
    initial stack image, hence of every stack read-back below. *)
{phdrs}
Global Strategy 200 [{segs_idents}].

(** [vm_refl] names [{steptac_name}.vm_refl_bv] (imported above) for the
    generated fetch/decode lemmas below — the VM-checked-cast-of-[eq_refl]
    idiom now lives in exactly one place.  Keep this alias in sync with
    gen-fd-lemmas, which documents it. *)
Ltac vm_refl := vm_refl_bv.
'''


def render_import(module):
    """A `From <library> Require Import <name>.` line for a dotted module."""
    library, _, base = module.rpartition(".")
    if library:
        return "From %s Require Import %s." % (library, base)
    return "Require Import %s." % base


def render_header(name, images, steptac_module, regen_flags):
    """The boilerplate above the lemmas, for the images this example has."""
    both = len(images) > 1
    return HEADER.format(
        name=name,
        title=name.replace("_", "-"),
        subject="both binaries" if both else "the source binary",
        images="images" if both else "image",
        image_list=" and ".join("%s.v" % m for m, _, _ in images),
        imports="\n".join(
            "From LinuxProcessSemantics.Examples.%s Require Import %s."
            % (name, module) for module, _, _ in images),
        steptac_import=render_import(steptac_module),
        steptac_name=steptac_module.rpartition(".")[2],
        regen_flags="".join(" " + f for f in regen_flags),
        segs="\n".join(
            "Definition %s_segs := %s_loaded_segments." % (side, module)
            for module, side, _ in images),
        phdrs="\n".join(
            "Definition %s_phdrs := %s_phdrs." % (side, module)
            for module, side, _ in images),
        segs_idents=" ".join("%s_segs" % side for _, side, _ in images))


def read_text_words(example_dir, module, text_range=None):
    """Return (base_pc, [word, ...], writable) for module <module>'s .text.

    The .text is the maximal nonzero run WITHIN the executable PT_LOAD's
    file extent [p_vaddr, p_vaddr + p_filesz), read from the program
    header table the image maps; see the module docstring for why that is
    exact here.  The page-rounded segment cannot be scanned whole: its
    in-page slack maps the neighboring file bytes (a mid-page .text has
    the ELF header in its head slack), which are not code.  For an image
    whose executable segment is WRITABLE (the w+x layout GNU ld's
    default -z noseparate-code merges), even the LOAD extent holds more
    than .text — the ELF headers, .rodata and .data, all inside
    p_filesz — so the caller must pass the .text address range explicitly
    (--source-text/--target-text); it is required for a w+x segment and
    honoured for any.  [writable] reports the segment's 'w' flag, which
    picks the fetch function the lemmas are stated over ([fetch_word]
    for immutable code, its w+x static projection [fetch_word_wx]
    otherwise).
    """
    image = os.path.join(example_dir, "%s.v" % module)
    if not os.path.isfile(image):
        sys.exit("gen_fd_lemmas.py: no such memory image: %s" % image)
    with open(image) as f:
        source = f.read()

    dependency_files = {
        dep.group("definition"): dep.group("file")
        for dep in DEPENDENCY_RE.finditer(source)
    }

    def load_hex(seg):
        byte_defs = [
            name for name in re.findall(r"\b\w+\b", seg.group("bytes"))
            if name in dependency_files
        ]
        if not byte_defs:
            sys.exit("gen_fd_lemmas.py: %s segment %s names no hex-byte "
                     "dependency" % (image, seg.group("idx")))
        hexfiles = [
            os.path.join(example_dir, dependency_files[name])
            for name in byte_defs
        ]
        parts = []
        for hexfile in hexfiles:
            if not os.path.isfile(hexfile):
                sys.exit("gen_fd_lemmas.py: no such segment file: %s" % hexfile)
            with open(hexfile) as f:
                parts.append(bytes.fromhex(f.read().strip()))
        seg_data = b"".join(parts)
        if len(seg_data) != int(seg.group("size"), 16):
            sys.exit(
                "gen_fd_lemmas.py: %s holds %d bytes across %d chunks, but "
                "%s declares seg_size 0x%x"
                % (
                    ", ".join(hexfiles),
                    len(seg_data),
                    len(hexfiles),
                    image,
                    int(seg.group("size"), 16),
                )
            )
        return seg_data

    segments = list(SEGMENT_RE.finditer(source))
    execs = [m for m in segments if "x" in m.group("perms")]
    if len(execs) != 1:
        sys.exit("gen_fd_lemmas.py: %s has %d executable segments, expected "
                 "exactly one" % (image, len(execs)))
    seg = execs[0]
    base = int(seg.group("base"), 16)
    size = int(seg.group("size"), 16)
    writable = "w" in seg.group("perms")
    data = load_hex(seg)

    def exec_load_extent():
        """[p_vaddr, p_vaddr + p_filesz) of the image's one executable
        PT_LOAD, read out of the program header table the image itself
        maps (the same bytes the model publishes through the auxv)."""
        m = PHDRS_RE.search(source)
        if m is None:
            sys.exit("gen_fd_lemmas.py: %s has no PhdrInfo record" % image)
        addr = int(m.group("addr"), 16)
        ent, num = int(m.group("ent")), int(m.group("num"))
        cover = [s for s in segments
                 if int(s.group("base"), 16) <= addr
                 and addr + ent * num
                 <= int(s.group("base"), 16) + int(s.group("size"), 16)]
        if not cover:
            sys.exit("gen_fd_lemmas.py: %s: the phdr table [0x%x, 0x%x) is "
                     "not inside any snapshotted segment"
                     % (image, addr, addr + ent * num))
        table = load_hex(cover[0])
        off = addr - int(cover[0].group("base"), 16)
        loads = []
        for i in range(num):
            e = table[off + i * ent : off + (i + 1) * ent]
            p_type = int.from_bytes(e[0:4], "little")
            p_flags = int.from_bytes(e[4:8], "little")
            if p_type == 1 and (p_flags & 1):  # PT_LOAD with PF_X
                vaddr = int.from_bytes(e[16:24], "little")
                filesz = int.from_bytes(e[32:40], "little")
                loads.append((vaddr, filesz))
        if len(loads) != 1:
            sys.exit("gen_fd_lemmas.py: %s: %d executable PT_LOAD entries "
                     "in the phdr table, expected exactly one"
                     % (image, len(loads)))
        return loads[0]

    if text_range is not None:
        lo, hi = text_range
        if not (base <= lo < hi <= base + size):
            sys.exit("gen_fd_lemmas.py: %s: --*-text range 0x%x:0x%x is not "
                     "inside the executable segment [0x%x, 0x%x)"
                     % (image, lo, hi, base, base + size))
        start, end = lo - base, hi - base
    elif writable:
        sys.exit("gen_fd_lemmas.py: %s's executable segment is writable "
                 "(w+x): it holds more than .text (ELF headers, .rodata, "
                 ".data), so the nonzero-run .text locator does not apply.  "
                 "Pass the .text range explicitly with "
                 "--source-text/--target-text 0xLO:0xHI." % image)
    else:
        vaddr, filesz = exec_load_extent()
        lo = max(vaddr, base)
        hi = min(vaddr + filesz, base + size)
        if lo >= hi:
            sys.exit("gen_fd_lemmas.py: %s: the executable PT_LOAD extent "
                     "[0x%x, 0x%x) does not intersect the executable "
                     "segment [0x%x, 0x%x)"
                     % (image, vaddr, vaddr + filesz, base, base + size))
        start, end = lo - base, hi - base
        while start < end and data[start] == 0:
            start += 1
        while end > start and data[end - 1] == 0:
            end -= 1
        if start == end:
            sys.exit("gen_fd_lemmas.py: %s's executable segment is all "
                     "zeroes" % image)
        # The run's START is exact: a 32-bit RISC-V encoding has 11 in its
        # two low bits, so no instruction's first (little-endian, lowest)
        # byte is zero.  Its END is not — the last instruction may well have
        # zero high bytes (an `ecall`, 0x00000073, is all but one) — so
        # round back up to the instruction boundary.  The bytes that
        # restores are the zeroes just trimmed.
        end = start + -(-(end - start) // 4) * 4
    if (base + start) % 4 or (end - start) % 4 or end > len(data):
        sys.exit("gen_fd_lemmas.py: %s's .text run 0x%x..0x%x is not a whole "
                 "number of aligned 4-byte instructions"
                 % (image, base + start, base + end))

    words = [int.from_bytes(data[i:i + 4], "little")
             for i in range(start, end, 4)]
    return base + start, words, writable


def rocq_loadpath(explicit):
    """`-Q` flags locating a built LinuxProcessSemantics, or [] if none is.

    Candidates, in order: --loadpath (what the dune rule passes, pointing at
    the theory's build directory), then the `-Q` lines of a `_CoqProject` in
    the current directory, then dune's build tree, then an in-source build.
    A candidate counts only if the decoder's .vo is there: the source
    `theories/` holds no .vo after a dune build, and a -Q that points at it
    makes rocq fail to find the library.  Returning [] uses the installed
    library (rocq-linux-process-semantics-core), which needs no -Q.  That is
    the case in a `dune build -p rocq-linux-process-semantics-examples`,
    where the dune rule passes a --loadpath that holds no .vo.
    """
    candidates = []
    if explicit:
        candidates.append((explicit, "LinuxProcessSemantics"))
    if os.path.isfile("_CoqProject"):
        with open("_CoqProject") as f:
            for line in f:
                parts = line.split()
                if len(parts) == 3 and parts[0] == "-Q":
                    candidates.append((parts[1], parts[2]))
    candidates += [(os.path.join("_build", "default", "theories"),
                    "LinuxProcessSemantics"),
                   ("theories", "LinuxProcessSemantics")]
    for d, prefix in candidates:
        if os.path.isfile(os.path.join(d, "Riscv", "Decode.vo")):
            return ["-Q", os.path.abspath(d), prefix]
    return []


def decode_words(words, loadpath):
    """Run one Compute per word inside rocq, return word -> AST string."""
    if shutil.which("rocq") is None:
        sys.exit("gen_fd_lemmas.py: `rocq` not found on PATH")
    lines = ["From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.",
             "Open Scope bv_scope.",
             "Set Printing Depth 10000.", "Set Printing Width 10000."]
    for w in words:
        lines.append(f"Compute (decode_any (Z_to_bv 32 {w})).")
    with tempfile.TemporaryDirectory() as tmpdir:
        vname = os.path.join(tmpdir, "gen_fd_decode.v")
        with open(vname, "w") as f:
            f.write("\n".join(lines) + "\n")
        try:
            out = subprocess.run(
                ["rocq", "c"] + loadpath + ["gen_fd_decode.v"], cwd=tmpdir,
                check=True, capture_output=True, text=True).stdout
        except subprocess.CalledProcessError as e:
            sys.exit("gen_fd_lemmas.py: rocq failed (is the "
                     "LinuxProcessSemantics library installed/built?):\n"
                     + e.stderr)
    results = []
    cur = None
    for line in out.splitlines():
        s = line.strip()
        if s.startswith("= "):
            cur = s[2:]
        elif cur is not None and s.startswith(":"):
            results.append(cur.strip())
            cur = None
        elif cur is not None:
            cur += " " + s
    assert len(results) == len(words), (len(results), len(words))
    return dict(zip(words, results))


def emit_lemmas(base, words, segs, prefix, dec, writable=False):
    # A w+x image's fetch facts are stated over the static projection
    # fetch_word_wx (the overlay-aware fetch_word_ov rewrites to it when
    # the overlay misses the fetched range — Common/WxExec.v); an
    # immutable-code image's over fetch_word, exactly as before.
    fetch_fn = "fetch_word_wx" if writable else "fetch_word"
    out = []
    for i, w in enumerate(words):
        pc = base + 4 * i
        out.append(
            f"Lemma {prefix}F_{pc:x} : {fetch_fn} {segs} {pc:#x} = Some {w}."
            " Proof. vm_refl. Qed.")
        # 0x73 is `ecall`: the semantics hands that word to the syscall
        # layer rather than the instruction decoder, so it gets no D lemma.
        if w != 0x73:
            out.append(
                f"Lemma {prefix}D_{pc:x} : decode_any (Z_to_bv 32 {w}) = {dec[w]}."
                " Proof. vm_refl. Qed.")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("name", help="example name, e.g. alloc_join_ns")
    ap.add_argument("--examples-dir", default="theories/Examples",
                    help="root of the examples tree (default: %(default)s)")
    ap.add_argument("--loadpath", default=None,
                    help="directory holding the built LinuxProcessSemantics "
                         "theory (default: autodetect)")
    ap.add_argument("--out", default=None,
                    help="write to FILE instead of stdout")
    ap.add_argument("--steptac-module",
                    default="LinuxProcessSemantics.Common.StepTac",
                    help="module providing [vm_refl_bv], imported by the "
                         "generated header (default: %(default)s)")
    ap.add_argument("--source-image", default=DEFAULT_IMAGES[0][0],
                    help="source memory-image module name, without .v "
                         "(default: %(default)s)")
    ap.add_argument("--target-image", default=DEFAULT_IMAGES[1][0],
                    help="target memory-image module name, without .v "
                         "(default: %(default)s)")
    ap.add_argument("--source-text", default=None, metavar="0xLO:0xHI",
                    help="explicit .text address range of the source image "
                         "(REQUIRED when its executable segment is w+x, "
                         "where the nonzero-run locator does not apply)")
    ap.add_argument("--target-text", default=None, metavar="0xLO:0xHI",
                    help="explicit .text address range of the target image")
    args = ap.parse_args()

    def parse_range(flag, value):
        if value is None:
            return None
        try:
            lo, hi = (int(part, 16) for part in value.split(":"))
        except ValueError:
            sys.exit("gen_fd_lemmas.py: %s wants 0xLO:0xHI, got %r"
                     % (flag, value))
        if not lo < hi:
            sys.exit("gen_fd_lemmas.py: %s: empty range %r" % (flag, value))
        return lo, hi

    text_ranges = [parse_range("--source-text", args.source_text),
                   parse_range("--target-text", args.target_text)]

    images = [(args.source_image,) + DEFAULT_IMAGES[0][1:],
              (args.target_image,) + DEFAULT_IMAGES[1][1:]]
    # Reproduced in the generated header so a by-hand regeneration matches.
    regen_flags = [
        "%s %s" % (flag, value)
        for flag, value, default in
        [("--steptac-module", args.steptac_module,
          ap.get_default("steptac_module")),
         ("--source-image", args.source_image, DEFAULT_IMAGES[0][0]),
         ("--target-image", args.target_image, DEFAULT_IMAGES[1][0]),
         ("--source-text", args.source_text, None),
         ("--target-text", args.target_text, None)]
        if value != default]

    example_dir = os.path.join(args.examples_dir, args.name)
    missing = [m for m, _, _ in images
               if not os.path.isfile(os.path.join(example_dir, "%s.v" % m))]
    if missing:
        sys.exit("gen_fd_lemmas.py: %s has no %s"
                 % (example_dir, ", ".join("%s.v" % m for m in missing)))
    texts = [read_text_words(example_dir, module, rng)
             for (module, _, _), rng in zip(images, text_ranges)]

    words = sorted({w for _, ws, _ in texts for w in ws if w != 0x73})
    dec = decode_words(words, rocq_loadpath(args.loadpath))
    bad = ["%#x" % w for w in words if dec[w] == "None"]
    if bad:
        sys.exit("gen_fd_lemmas.py: %s: word(s) %s do not decode; the .text "
                 "run located in the memory image is wrong"
                 % (args.name, ", ".join(bad)))

    out = [render_header(args.name, images, args.steptac_module, regen_flags)]
    for (module, side, prefix), (base, ws, writable) in zip(images, texts):
        out.append("(* ===== %s (%s) ===== *)" % (side, args.name))
        out.extend(emit_lemmas(base, ws, "%s_segs" % side, prefix, dec,
                               writable))
        out.append("")
    text = "\n".join(out)

    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
