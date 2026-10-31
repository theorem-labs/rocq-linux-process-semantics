#!/usr/bin/env python3
"""Real line spans of Rocq declarations, and a checker for the Lean port's citations.

Written for OSSV-265 slice K1 (review finding 1 and 2: wrong `file.v:<span>`
citations in the Lean twin).  Two modes:

    rocqspan.py spans <rocq-file> [name ...]
        print `name start end comment_start` for every declaration of the file
        (or only the named ones).

    rocqspan.py check [lean-file ...]
        parse every ``<path>.v:<span>`` citation of the Lean files, resolve the
        Rocq file, work out the span the citation ought to carry, and report
        every mismatch.  Exit status 1 if any citation is wrong.

A citation that sits in a ``/-- ... -/`` docstring of a Lean declaration is
expected, by default, to name the Rocq declaration of the same name (the
declaration alone, without its ``(** ... *)`` comment).  Every other citation —
a ``/-! ... -/`` section comment, a cross-reference, a span rather than a
declaration — needs a line in EXPECT below, which says what it should name:

    "decl:NAME"            the declaration NAME, alone
    "block:A..B"           from the comment of declaration A to the end of B
    "cblock:A..B"          same, with A's comment excluded
    "fixed:LO-HI"          a literal span, checked by reading both sides
                           (the note says what was read)

so that nothing is accepted merely because it is already there.

An EXPECT key is one of

    "<lean path>@<anchor>#<cited .v path>#<n>"   (preferred)
    "<lean path>:<line>:<cited .v path>"         (legacy, breaks on a line move)

where `<lean path>` is relative to LEAN_ROOT, `<anchor>` is the Lean
declaration (or namespace) the citation's comment block sits above, and `<n>`
counts citations of the same anchor and the same cited file, in file order,
from 1.  An unknown citation prints the anchor key to add, so `check` tells
you the line to paste.  The Rocq files are read from ROCQ_ROOTS below, which
hold the commit the Lean headers pin (`9b0ac6f0e6`); point them at the next
port's own copies and the checker serves that port unchanged.
"""

import os
import re
import sys

ROCQ_ROOTS = [
    ("theories/", "/mnt/nvme/sami/tmp/knockk1/released/theories/"),
    ("projects/libreac/fuzz_knock/", "/mnt/nvme/sami/tmp/knockk1/released/projects/libreac/fuzz_knock/"),
    ("lib/", "/mnt/nvme/sami/tmp/knockk1/rocq/projects/libreac/fuzz_knock/proofs/lib/"),
]

LEAN_ROOT = "/home/sami/src/lean-twin-k1/lean-proofs/libreac/fuzz_knock/"

DECL_KW = (
    "Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Variant|Class"
    "|Lemma|Theorem|Corollary|Remark|Fact|Proposition|Example|Instance"
    "|Ltac|Notation|Axiom|Parameter|Hypothesis|Variable|Let|Module|Section"
)
DECL_RE = re.compile(
    r"^\s*(?:(?:Local|Global|Program|Polymorphic|#\[[^\]]*\]\s*)\s+)*"
    r"(?P<kw>" + DECL_KW + r")\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)
PROOF_END_RE = re.compile(r"\b(Qed|Defined|Admitted|Abort)\s*\.")
PROVED_KW = {
    "Lemma", "Theorem", "Corollary", "Remark", "Fact", "Proposition",
    "Example", "Instance",
}


def code_lines(path):
    """Return the file's lines with (* ... *) comment text blanked out."""
    src = open(path, encoding="utf-8").read().split("\n")
    out, depth = [], 0
    for line in src:
        buf, i = [], 0
        while i < len(line):
            if line.startswith("(*", i):
                depth += 1
                i += 2
            elif line.startswith("*)", i) and depth:
                depth -= 1
                i += 2
            elif depth:
                i += 1
            else:
                buf.append(line[i])
                i += 1
        out.append("".join(buf))
    return src, out


def comment_start(src, decl_line):
    """First line of the (** ... *) block that ends just above decl_line (1-based)."""
    i = decl_line - 2            # 0-based index of the line above
    if i < 0 or "*)" not in src[i]:
        return decl_line
    depth = 0
    j = i
    while j >= 0:
        depth += src[j].count("*)") - src[j].count("(*")
        if depth <= 0:
            return j + 1
        j -= 1
    return decl_line


def parse(path):
    """Ordered list of declarations: dict(name, kw, start, end, cstart)."""
    src, code = code_lines(path)
    decls, i, n = [], 0, len(code)
    while i < n:
        m = DECL_RE.match(code[i])
        if not m:
            i += 1
            continue
        kw, name, start = m.group("kw"), m.group("name"), i + 1
        if kw in ("Module", "Section") and ":=" not in code[i]:
            depth, j = 1, i + 1
            while j < n and depth:
                if re.match(r"^\s*(Module|Section)\s+\w+", code[j]) and ":=" not in code[j]:
                    depth += 1
                elif re.match(r"^\s*End\s+\w+\s*\.", code[j]):
                    depth -= 1
                j += 1
            end = j
            inner = parse_range(src, code, i + 1, j - 1)
            decls.append(dict(name=name, kw=kw, start=start, end=end,
                              cstart=comment_start(src, start)))
            decls.extend(inner)
            i = j
            continue
        j, end = i, None
        while j < n:
            if kw in PROVED_KW:
                if PROOF_END_RE.search(code[j]) and j >= i:
                    end = j + 1
                    break
            elif re.search(r"\.\s*$", code[j]) and code[j].strip():
                end = j + 1
                # a Program/Equations style body closed by Qed/Defined
                k = end
                while k < n and not code[k].strip():
                    k += 1
                if k < n and re.match(r"^\s*(Proof|Next Obligation)\b", code[k]):
                    while k < n and not PROOF_END_RE.search(code[k]):
                        k += 1
                    end = k + 1
                break
            j += 1
        if end is None:
            end = j
        decls.append(dict(name=name, kw=kw, start=start, end=end,
                          cstart=comment_start(src, start)))
        i = end
    return decls


def parse_range(src, code, lo, hi):
    """Parse declarations in the 0-based half-open range [lo, hi)."""
    sub = code[:]
    for k in range(len(sub)):
        if k < lo or k >= hi:
            sub[k] = ""
    decls, i, n = [], lo, hi
    while i < n:
        m = DECL_RE.match(sub[i])
        if not m:
            i += 1
            continue
        kw, name, start = m.group("kw"), m.group("name"), i + 1
        if kw in ("Module", "Section") and ":=" not in sub[i]:
            depth, j = 1, i + 1
            while j < n and depth:
                if re.match(r"^\s*(Module|Section)\s+\w+", sub[j]) and ":=" not in sub[j]:
                    depth += 1
                elif re.match(r"^\s*End\s+\w+\s*\.", sub[j]):
                    depth -= 1
                j += 1
            decls.append(dict(name=name, kw=kw, start=start, end=j,
                              cstart=comment_start(src, start)))
            decls.extend(parse_range(src, code, i + 1, j - 1))
            i = j
            continue
        j, end = i, None
        while j < n:
            if kw in PROVED_KW:
                if PROOF_END_RE.search(sub[j]):
                    end = j + 1
                    break
            elif re.search(r"\.\s*$", sub[j]) and sub[j].strip():
                end = j + 1
                break
            j += 1
        if end is None:
            end = j
        decls.append(dict(name=name, kw=kw, start=start, end=end,
                          cstart=comment_start(src, start)))
        i = end
    return decls


_CACHE = {}


def decls_of(rel):
    if rel in _CACHE:
        return _CACHE[rel]
    path = resolve(rel)
    if path is None:
        _CACHE[rel] = None
        return None
    _CACHE[rel] = parse(path)
    return _CACHE[rel]


def resolve(rel):
    for prefix, root in ROCQ_ROOTS:
        if rel.startswith(prefix):
            p = root + rel[len(prefix):]
            if os.path.exists(p):
                return p
    for _, root in ROCQ_ROOTS:
        p = root + os.path.basename(rel)
        if os.path.exists(p):
            return p
    return None


def find(rel, name):
    ds = decls_of(rel)
    if ds is None:
        return None
    hits = [d for d in ds if d["name"] == name]
    return hits[0] if hits else None


# ---------------------------------------------------------------------------
# What each citation that is NOT "the declaration it is attached to" must name.
# Key: "<lean file relative to LEAN_ROOT>:<line>:<cited path>".  The citations
# marked `fixed:` were checked by reading both files; the note says what.
# ---------------------------------------------------------------------------
EXPECT = {
 # Core/Shapes.lean — section comments over a Rocq comment + declarations
 "OssFuzzTheorems/Core/Shapes.lean@Budgets#theories/Shapes.v#1": ("block:Budgets..Budgets", "Module Budgets with its comment"),
 "OssFuzzTheorems/Core/Shapes.lean@Env#theories/Shapes.v#1": ("block:Env..Env", "Module Env with its comment"),
 "OssFuzzTheorems/Core/Shapes.lean@may_fail_is#theories/Shapes.v#1": ("block:may_fail_is..forced_only_is", "the three reading lemmas with their comment"),
 "OssFuzzTheorems/Core/Shapes.lean@Exits#theories/Shapes.v#1": ("block:Exits..Exits", "Module Exits with its comment"),
 "OssFuzzTheorems/Core/Shapes.lean@agrees#theories/Shapes.v#1": ("block:agrees..agrees_is_lps", "shape-1 comment, agrees, agrees_is_lps"),
 "OssFuzzTheorems/Core/Shapes.lean@agrees_in#theories/Shapes.v#1": ("block:agrees_in..agrees_in_is_lps", "comment, agrees_in, agrees_in_is_lps"),
 "OssFuzzTheorems/Core/Shapes.lean@agrees_iff_agrees_in_may_fail#theories/Shapes.v#1": ("block:agrees_iff_agrees_in_may_fail..agrees_iff_agrees_in_may_fail", "lemma with its comment"),
 "OssFuzzTheorems/Core/Shapes.lean@agrees_abort_modelled#theories/Shapes.v#1": ("block:agrees_abort_modelled..agrees_abort_modelled_is_lps", "comment, definition, _is_lps"),
 "OssFuzzTheorems/Core/Shapes.lean@agrees_in_abort_modelled#theories/Shapes.v#1": ("block:agrees_in_abort_modelled..agrees_in_abort_modelled_is_lps", "comment, definition, _is_lps"),
 "OssFuzzTheorems/Core/Shapes.lean@agrees_rv64gc#theories/Shapes.v#1": ("block:agrees_rv64gc..agrees_in_rv64gc_is_lps", "the whole _rv64gc block with its comment"),
 "OssFuzzTheorems/Core/Shapes.lean@halts_within_budget#theories/Shapes.v#1": ("block:halts_within_budget..halts_within_budget_is_lps", "shape-2 comment, definition, _is_lps"),
 "OssFuzzTheorems/Core/Shapes.lean@halts_may_fail#theories/Shapes.v#1": ("block:halts_may_fail..halts_may_fail_is_lps", "comment, definition, _is_lps"),
 "OssFuzzTheorems/Core/Shapes.lean@halts_within_budget_mono#theories/Shapes.v#1": ("block:halts_within_budget_mono..halts_may_fail_mono", "comment and the two mono lemmas"),

 # Core/Images.lean — docstrings whose Lean name is the Rocq name
 "OssFuzzTheorems/Core/Images.lean@image_wf#theories/Images.v#1": ("decl:image_wf", ""),
 "OssFuzzTheorems/Core/Images.lean@image_wf_b#theories/Images.v#1": ("decl:image_wf_b", ""),
 "OssFuzzTheorems/Core/Images.lean@image_wf_of_memimage#theories/Images.v#1": ("decl:image_wf_of_memimage", ""),
 "OssFuzzTheorems/Core/Images.lean@image_wf_nil#theories/Images.v#1": ("decl:image_wf_nil", ""),

 # the vocabulary: docstrings that cite a declaration under another name
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Img0.lean@rsegs#lib/Img0.v#1": ("decl:rsegs", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Exec.lean@evt_cut#lib/Lib/Tac.v#1": ("fixed:250-253", "read: the `call` tactic, `eapply evt_cut; [eapply SPEC | post_call]`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Mem.lean@mrd#lib/Lib/Mem.v#1": ("decl:mrd", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Step.lean@rw_cells#lib/Lib/Step.v#1": ("decl:rw_cells", ""),

 # K1Harness: proofs/lib/Prog/LLVMFuzzerTestOneInput_c.lean (the contract)
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput_c.lean:16:lib/Prog/LLVMFuzzerTestOneInput_c.v": ("fixed:25-27", "read: the post-state `MS (mkR ...) F (ret_pc ra) fc None m' (seg_rom rsegs)`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput_c.lean:24:lib/Prog/LLVMFuzzerTestOneInput_c.v": ("fixed:12-12", "read: the `forall (ra sp gp tp ... t6 : word)` line of knock_main_contract"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput_c.lean:32:lib/Prog/LLVMFuzzerTestOneInput_c.v": ("fixed:19-19", "read: `bv_unsigned sp mod 16 = 0`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput_c.lean:58:lib/Prog/LLVMFuzzerTestOneInput_c.v": ("fixed:23-31", "read: the `fun ms' => exists ...` post-state inside knock_main_contract"),

 # K1Harness: proofs/lib/Prog/LLVMFuzzerTestOneInput.lean (the walk)
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:15:lib/Prog/LLVMFuzzerTestOneInput_c.v": ("decl:knock_main_contract", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:18:lib/Prog/LLVMFuzzerTestOneInput.v": ("fixed:424-425", "read: `if_cases EBIG.` and the `eapply knock_exit` it guards, inside knock_entry"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:28:lib/Prog/LLVMFuzzerTestOneInput.v": ("fixed:77-463", "read: from the `Variables (p : word) (data : list byte).` of line 77 to knock_entry's Qed on 463"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:64:lib/Lib/MState.v": ("decl:unsigned_lit", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:72:lib/Prog/LLVMFuzzerTestOneInput.v": ("decl:addr_eq_tac", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:82:lib/Lib/MState.v": ("decl:ret_pc", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:95:lib/Prog/LLVMFuzzerTestOneInput.v": ("fixed:48-48", "read: knock_exit's premise `rw_cells rsegs m1 (bv_unsigned sp + -144) (cs40 ++ saved)`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:168:lib/Lib/Frame.v": ("decl:munch", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:227:lib/Lib/Mem.v": ("decl:ro_addr", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:228:lib/Prog/knock_lib.v": ("decl:mem_inv_from_entry", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:306:lib/Prog/LLVMFuzzerTestOneInput.v": ("fixed:24-24", "read: the `Variables (ra sp gp tp s0 ... : word) ...` line of Section KnockRun, which binds sp"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:312:lib/Prog/LLVMFuzzerTestOneInput.v": ("decl:knock_exit", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:646:lib/Prog/LLVMFuzzerTestOneInput.v": ("decl:Qk", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:666:lib/Lib/Frame.v": ("decl:munch", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:674:lib/Lib/Frame.v": ("decl:wmono", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:677:lib/Lib/Mem.v": ("decl:mem_inv", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:679:lib/Lib/Frame.v": ("decl:stk", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:686:lib/Prog/LLVMFuzzerTestOneInput_c.v": ("decl:knock_main_contract", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.lean:690:lib/Prog/LLVMFuzzerTestOneInput.v": ("fixed:424-425", "read: `if_cases EBIG.` and the `eapply knock_exit` it guards, inside knock_entry"),

 # K1Citations: citations added while fixing review findings 1-4 and 9
 "OssFuzzTheorems/Core/Shapes.lean@OssFuzzTheorems.Core.Shapes#theories/Shapes.v#1": ("block:disagrees_at_most..agreement_decidable_rv64gc_of_classifier", "shapes 3 and 4, comment to last lemma"),
 "OssFuzzTheorems/Core/Images.lean@OssFuzzTheorems.Core.Images#theories/Images.v#1": ("decl:check_image_wf", ""),
 "OssFuzzTheorems/Core/Images.lean@image_entry_fetchable_nil#theories/Images.v#1": ("fixed:67-67", "read: `rewrite image_entry_fetchable_nil in H` inside image_wf_nil's proof"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Mem.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem#lib/Lib/Mem.v#1": ("decl:bytes_at_rdn", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Mem.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem#lib/Lib/Mem.v#2": ("decl:bytes_at_read", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Mem.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem#lib/Lib/Mem.v#3": ("decl:wr_at_store_ok", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Exec.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec#lib/Lib/Exec.v#1": ("decl:DA_Myrk", "the module of arithmetic lemmas and tactics"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_struct.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct#lib/Prog/reac_knock_struct.v#1": ("decl:knock_sx32_unsigned", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_struct.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct#lib/Prog/reac_knock_struct.v#2": ("decl:knock_sx32_eqb", ""),

 # K1Heard: proofs/lib/Prog/reac_knock_heard_c.lean (the contract)
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:55:lib/Prog/reac_knock_heard_c.v": ("fixed:25-25", "read: `(knock_cells (if Z.eqb st 0 then 2 else st) p1 opened due a1 g p2))`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:57:lib/Prog/reac_knock_struct.v": ("decl:knock_sx32_unsigned", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:58:lib/Prog/reac_knock_struct.v": ("decl:knock_sx32_eqb", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:78:lib/Lib/MState.v": ("decl:MS", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:80:lib/Lib/MState.v": ("decl:step_gen", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:86:lib/Lib/Frame.v": ("decl:mkR", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:90:lib/Lib/Cells.v": ("decl:cells_at_read", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:91:lib/Lib/Step.v": ("decl:rw_cells_read", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:94:lib/Lib/Step.v": ("decl:rw_cells_store_ok", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:101:lib/Prog/reac_knock_heard_c.v": ("fixed:24-25", "read: the `rw_cells rsegs m' (bv_unsigned a0) (knock_cells ...)` post conjunct"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:106:lib/Lib/Frame.v": ("cblock:munch..wmono", "the two frame definitions"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:107:lib/Prog/reac_knock_heard_c.v": ("fixed:22-23", "read: the `munch [...] m m'` and `wmono rsegs m m'` post conjuncts"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.lean:112:lib/Lib/MState.v": ("decl:ret_pc", ""),

 # K1Heard: proofs/lib/Prog/reac_knock_heard.lean (the walk)
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:10:lib/Prog/reac_knock_heard.v": ("fixed:14-28", "read: the tactic lines of reac_knock_heard_holds, `unfold ...` to `finish; try (...)`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:11:lib/Lib/Step.v": ("decl:step", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:12:lib/Lib/Step.v": ("decl:if_cases", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:12:lib/Lib/Tac.v": ("decl:finish", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:130:lib/Lib/Step.v": ("decl:rw_cells_store_ok", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:154:lib/Lib/Frame.v": ("decl:munch", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:168:lib/Lib/MState.v": ("decl:ret_pc", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:178:lib/Prog/reac_knock_struct.v": ("decl:knock_sx32_unsigned", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:179:lib/Prog/reac_knock_struct.v": ("decl:knock_sx32_eqb", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.lean:214:lib/Prog/reac_knock_heard_c.v": ("fixed:25-25", "read: `(knock_cells (if Z.eqb st 0 then 2 else st) p1 opened due a1 g p2))`"),

 # K1Step: proofs/lib/Prog/reac_knock_step_c.lean (the contract)
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step_c.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step_c#lib/Lib/Cells.v#1": ("decl:cells_at_read", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step_c.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step_c#lib/Lib/Step.v#1": ("decl:rw_cells_read", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step_c.lean@knock_step_mem#lib/Prog/reac_knock_step_c.v#1": ("fixed:35-35", "read: the post conjunct `rw_cells rsegs m' (bv_unsigned a0) (knock_cells st' p1 opened due' heard g' p2)`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step_c.lean@EOF#lib/Prog/reac_knock_step_c.v#1": ("fixed:25-25", "read: the premise `rw_cells rsegs m (bv_unsigned a0) (knock_cells st p1 opened due heard g p2)`"),

 # K1Step: proofs/lib/Prog/reac_knock_step.lean (the walk)
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step.lean@knock_sx32_unsigned#lib/Prog/reac_knock_struct.v#1": ("decl:knock_sx32_unsigned", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step.lean@ret_pc_jalr#lib/Lib/MState.v#1": ("decl:ret_pc", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step.lean@store_ok_of_wr_at#lib/Lib/Step.v#1": ("decl:rw_cells_store_ok", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step.lean@munch_store#lib/Prog/reac_knock_step_c.v#1": ("fixed:31-31", "read: the post conjunct `munch [(bv_unsigned a0, bv_unsigned a0 + 40)] m m'`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step.lean@EOF#lib/Prog/reac_knock_step_c.v#1": ("fixed:25-25", "read: the premise `rw_cells rsegs m (bv_unsigned a0) (knock_cells st p1 opened due heard g p2)`"),
 # memset.lean / memset_c.lean (K1Memset) — spans of `memset_body`'s proof and
 # of the `mkR` row of `memset_post`, which name no Rocq declaration.
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@k_val#R_memset.v#1": ("fixed:255-261", "read: `remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k` and its `assert (Rk : (0 <= k < 4 /\\ (A + k) mod 4 = 0)%Z)`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@n4_val#R_memset.v#1": ("fixed:263-267", "read: `rewrite land_align_down`, `remember (n - k - (n - k) mod 2^2)%Z as n4` and its `assert (Rn4 : (exists q, n4 = 4 * q)%Z /\\ (n - k - 3 <= n4 <= n - k)%Z)`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@k4_val#R_memset.v#1": ("decl:land4_of_aligned", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@k4_val#R_memset.v#2": ("fixed:285-288", "read: `remember (Z.land (A + k) 4) as k4` and its `assert (Rk4 : ((k4 = 0 \\/ k4 = 4) /\\ (A + k + k4 + 24) mod 8 = 0)%Z)`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@mulhu_splat#R_memset.v#1": ("fixed:268-268", "read: `zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@splat8_or#R_memset.v#1": ("fixed:296-296", "read: `zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@exit_ret#R_memset.v#1": ("fixed:178-186", "read: `Ltac fin_with cover` and `Ltac fin`, the two tactics that close every exit of the walk"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@blk_1ac04#R_memset.v#1": ("fixed:235-240", "read: the opening `zstep`/`if_cases K0`, the first byte's `ms_facts`/`ms_store_ok`/`ms_arr_store`, the `mst (n - 1)` and the `if_cases K3`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@blk_1ac1c#R_memset.v#1": ("fixed:241-246", "read: `mst 1`, `mst 2`, `mst (n - 3)`, `mst (n - 2)` and the `if_cases K7`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@blk_1ac34#R_memset.v#1": ("fixed:247-250", "read: `mst 3`, `mst (n - 4)` and the `if_cases K9`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@step_subw_at#R_memset.v#1": ("fixed:251-272", "read: from the `zstep. zstep.` after the `n < 9` exit, through the `k`, `c * BC4` and `n4` blocks, to the `if_cases K9'`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@blk_1ac6c#R_memset.v#1": ("fixed:270-272", "read: `mst k 4%nat`, `mst (k + n4 - 4)%Z 4%nat` and the `if_cases K9'`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@blk_1ac7c#R_memset.v#1": ("fixed:273-278", "read: `mst (k + 4)`, `mst (k + 8)`, `mst (k + n4 - 12)`, `mst (k + n4 - 8)` and the `if_cases K25`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@blk_1ac94#R_memset.v#1": ("fixed:279-294", "read: `mst (k + 12)` through `mst (k + 24)`, the `Z.land (A + k) 4` block, `mst (k + n4 - 28)` through `mst (k + n4 - 16)` and the `if_cases K32`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@step_or_at#R_memset.v#1": ("fixed:295-300", "read: the four `zstep`s that build `c * BC8`, the `replace (A + k + (k4 + 24))` and the `eapply memset_loop`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@loop_aux#R_memset.v#1": ("decl:memset_loop", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@memset_walk#R_memset.v#1": ("decl:memset_body", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset.lean@memset_holds#R_memset.v#1": ("decl:memset_spec", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset_c.lean@memset_clobber#lib/Prog/memset_c.v#1": ("fixed:13-13", "read: the `mkR` row of `memset_post`, whose fresh variables are t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/memset_c.lean@memset_frame#lib/Prog/memset_c.v#1": ("fixed:13-13", "read: the same `mkR` row, which keeps ra sp gp tp s0 s1 a0 s2..s11 and makes the caller-saved registers fresh"),

 # K1Init: proofs/lib/Prog/reac_knock_init_c.lean and reac_knock_init.lean
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init_c.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init_c#lib/Prog/reac_knock_init_c.v#1": ("fixed:32-33", "read: the start state `MS (mkR ra sp ... t6) F (Z_to_bv 64 REAC_KNOCK_INIT) fc None m (seg_rom rsegs)` of reac_knock_init_contract"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init_c.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init_c#lib/Prog/reac_knock_init_c.v#2": ("fixed:13-13", "read: the `forall (ra sp gp tp t0 ... t6 : word)` line of reac_knock_init_contract"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init_c.lean@init_clobbers#lib/Prog/reac_knock_init_c.v#1": ("fixed:23-24", "read: the post-state `ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' ... t6')` of reac_knock_init_contract's Q"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init#lib/Prog/reac_knock_init.v#1": ("fixed:30-50", "read: the tactic script of reac_knock_init_holds, from `intros MEMS.` to the closing `reflexivity.`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init#lib/Lib/Exec.v#1": ("decl:msteps_trans", ""),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init#lib/Lib/Tac.v#1": ("fixed:250-253", "read: the `call` tactic, `eapply evt_cut; [eapply SPEC | post_call]`"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init.lean@OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init#lib/Prog/memset_c.v#1": ("cblock:MEMSET..memset_contract", "the whole of memset_c.v, MEMSET to memset_contract"),
 "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init.lean@jalr_ret#lib/Lib/MState.v#1": ("decl:ret_pc", ""),
}


CITE_RE = re.compile(r"`?([A-Za-z0-9_./]+\.v):(\d+)(?:-(\d+))?")
LEAN_DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|partial\s+|noncomputable\s+)*"
    r"(?:def|theorem|lemma|abbrev|inductive|structure|instance|class|namespace)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)")


def next_decl(lines, k):
    """Name of the first Lean declaration at or after line index k, or 'EOF'."""
    while k < len(lines):
        m = LEAN_DECL_RE.match(lines[k])
        if m:
            return m.group("name")
        k += 1
    return "EOF"


def lean_citations(path):
    """Yield one dict per `<file>.v:<span>` citation.

    `anchor` is the Lean declaration the citation's comment block sits above,
    so an EXPECT key built from it survives a line move; `attached` is that
    name only when the block is a `/-- ... -/` docstring of the declaration.
    """
    lines = open(path, encoding="utf-8").read().split("\n")
    n = len(lines)
    seen = {}
    i = 0
    while i < n:
        line = lines[i]
        if "/--" in line or "/-!" in line:
            kind = "doc" if "/--" in line else "sec"
            start = i
            j = i
            while j < n and "-/" not in lines[j]:
                j += 1
            block = lines[start:j + 1]
            anchor = next_decl(lines, j + 1)
            attached = None
            if kind == "doc":
                k = j + 1
                while k < n and not lines[k].strip():
                    k += 1
                if k < n:
                    m = LEAN_DECL_RE.match(lines[k])
                    if m:
                        attached = m.group("name")
            for off, text in enumerate(block):
                for m in CITE_RE.finditer(text):
                    rel = m.group(1)
                    nth = seen[(anchor, rel)] = seen.get((anchor, rel), 0) + 1
                    yield dict(line=start + off + 1, rel=rel,
                               lo=int(m.group(2)),
                               hi=int(m.group(3) or m.group(2)),
                               attached=attached, anchor=anchor, nth=nth)
            i = j + 1
            continue
        # citations in ordinary `--` comments
        if "--" in line:
            for m in CITE_RE.finditer(line[line.index("--"):]):
                rel = m.group(1)
                anchor = next_decl(lines, i + 1)
                nth = seen[(anchor, rel)] = seen.get((anchor, rel), 0) + 1
                yield dict(line=i + 1, rel=rel, lo=int(m.group(2)),
                           hi=int(m.group(3) or m.group(2)),
                           attached=None, anchor=anchor, nth=nth)
        i += 1


def expected_span(spec, rel):
    kind, _, arg = spec.partition(":")
    if kind == "decl":
        d = find(rel, arg)
        return None if d is None else (d["start"], d["end"])
    if kind in ("block", "cblock"):
        a, _, b = arg.partition("..")
        da, db = find(rel, a), find(rel, b)
        if da is None or db is None:
            return None
        return ((da["cstart"] if kind == "block" else da["start"]), db["end"])
    if kind == "fixed":
        lo, _, hi = arg.partition("-")
        return (int(lo), int(hi or lo))
    raise SystemExit("bad EXPECT spec: " + spec)


def check(files):
    bad = 0
    total = 0
    for f in files:
        rel_lean = os.path.relpath(f, LEAN_ROOT)
        for c in lean_citations(f):
            line, rel, lo, hi = c["line"], c["rel"], c["lo"], c["hi"]
            akey = "%s@%s#%s#%d" % (rel_lean, c["anchor"], rel, c["nth"])
            lkey = "%s:%d:%s" % (rel_lean, line, rel)
            if akey in EXPECT:
                spec, note = EXPECT[akey]
            elif lkey in EXPECT:
                spec, note = EXPECT[lkey]
            elif c["attached"] and find(rel, c["attached"]):
                spec, note = "decl:" + c["attached"], "same name"
            else:
                print("UNDECLARED %s:%d  %s:%d-%d  (no EXPECT entry, no Rocq "
                      "declaration of the attached Lean name %r)\n"
                      "    add:  %r: (\"decl:NAME\", \"\"),"
                      % (rel_lean, line, rel, lo, hi, c["attached"], akey))
                bad += 1
                total += 1
                continue
            total += 1
            want = expected_span(spec, rel)
            if want is None:
                print("UNRESOLVED %s:%d  %s  spec %s" % (rel_lean, line, rel, spec))
                bad += 1
                continue
            if (lo, hi) != want:
                print("MISMATCH %s:%d  %s:%d-%d  should be %d-%d  [%s %s]"
                      % (rel_lean, line, rel, lo, hi, want[0], want[1], spec, note))
                bad += 1
    print("%d citations checked, %d wrong" % (total, bad))
    return 1 if bad else 0


DEFAULT_FILES = [
    "OssFuzzTheorems/Core/Shapes.lean",
    "OssFuzzTheorems/Core/Images.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/Images.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/Statements.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Img0.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Mem.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Cells.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Frame.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Exec.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/MState.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Lib/Step.lean",
    "OssFuzzTheorems/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_struct.lean",
]


def main(argv):
    if len(argv) > 1 and argv[1] == "spans":
        path = argv[2]
        if not os.path.exists(path):
            path = resolve(argv[2]) or argv[2]
        names = set(argv[3:])
        for d in parse(path):
            if names and d["name"] not in names:
                continue
            print("%-44s %-10s %4d-%-4d  (with comment %d-%d)"
                  % (d["name"], d["kw"], d["start"], d["end"], d["cstart"], d["end"]))
        return 0
    if len(argv) > 1 and argv[1] == "check":
        files = argv[2:] or DEFAULT_FILES
        files = [f if os.path.isabs(f) else LEAN_ROOT + f for f in files]
        return check(files)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
