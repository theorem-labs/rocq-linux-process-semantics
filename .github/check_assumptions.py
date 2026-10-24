#!/usr/bin/env python3
"""Check the assumptions of every example proof.

Run from the repository root after `dune build`.  For each
theories/Examples/<name>/ that has a Proof.v, compile the Checker.v that
dune generated, independently recheck its compiled proof closure with
rocqchk, read the output of its two Print Assumptions blocks, and fail if
an assumption is not permitted.

Permitted: functional_extensionality_dep and the primitives of the
PrimInt63, PrimString and PrimArray modules.
"""

import os
import re
import subprocess
import sys
import tempfile

BUILD = os.path.join("_build", "default", "theories")
PERMITTED_MODULES = ("PrimInt63", "PrimString", "PrimArray")
PERMITTED_NAMES = ("functional_extensionality_dep",)
BLOCK = re.compile(r"<PrintAssumptions>\s*(.*?)\s*</PrintAssumptions>", re.S)


def permitted(name):
    parts = name.split(".")
    return parts[-1] in PERMITTED_NAMES or any(
        m in parts[:-1] for m in PERMITTED_MODULES)


def assumptions(text):
    """Return the assumption names in one Print Assumptions output."""
    names = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line == "Closed under the global context":
            continue
        if line.endswith(":") and " " not in line.rstrip(":"):
            continue  # a section header, for example "Axioms:"
        if " : " in line:
            names.append(line.split(" : ", 1)[0].strip())
        elif not line.startswith(("Axioms", "Section Variables")):
            names.append(line)
    return names


def check(name, tmp):
    checker = os.path.join(BUILD, "Examples", name, "Checker.v")
    if not os.path.exists(checker):
        return ["%s does not exist; run dune build first" % checker]
    # rocq c requires the output file to have the source's base name.
    outdir = os.path.join(tmp, name)
    os.makedirs(outdir)
    vo = os.path.join(outdir, "Checker.vo")
    out = subprocess.run(
        ["rocq", "c", "-Q", BUILD, "LinuxProcessSemantics",
         "-o", vo, checker],
        capture_output=True, text=True)
    if out.returncode != 0:
        return ["rocq failed on %s:\n%s" % (checker, out.stderr)]
    checked = subprocess.run(
        ["rocqchk", "-silent", "-Q", BUILD, "LinuxProcessSemantics", vo],
        capture_output=True, text=True)
    if checked.returncode != 0:
        detail = checked.stdout + checked.stderr
        return ["rocqchk failed on %s:\n%s" % (vo, detail)]
    blocks = BLOCK.findall(out.stdout)
    if len(blocks) != 2:
        return ["%s: expected 2 Print Assumptions blocks, found %d"
                % (checker, len(blocks))]
    errors = []
    for block in blocks:
        for a in assumptions(block):
            if not permitted(a):
                errors.append("%s: assumption not permitted: %s" % (name, a))
    return errors


def main():
    examples = sorted(
        d for d in os.listdir(os.path.join("theories", "Examples"))
        if os.path.exists(os.path.join("theories", "Examples", d, "Proof.v")))
    if not examples:
        sys.exit("no examples found; run from the repository root")
    errors = []
    with tempfile.TemporaryDirectory() as tmp:
        for name in examples:
            e = check(name, tmp)
            print("%s: %s" % (name, "ok" if not e else "FAIL"))
            errors += e
    for e in errors:
        print(e)
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
