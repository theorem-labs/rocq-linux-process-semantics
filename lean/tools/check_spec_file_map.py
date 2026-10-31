#!/usr/bin/env python3
"""Every file holding a spec has a row in `Specs.v`'s WHERE A SPEC LIVES map.

`Specs.v` opens with a hand-written map from each `Sys/**/*.v` file to the
kernel source file it answers to, and each spec file's own header tells the
reader that `Specs.v` carries the whole map. Nothing checked that. `Sys/Fs/
EventPoll.v` landed with no row and no `Require Export` entry and the build
stayed green, because compiling `Specs.v` only needs `SyscallTable.v` to have
exported the module already.

The omission cannot be seen from either enumeration on its own. A reader that
starts from the map's rows finds every row's file present and agrees with
itself; a reader that starts from the files has nothing to compare them
against. The modeled side has to be read from the model: `spec_table` names
the `<name>_spec` each arm calls, and the file that defines that name is a file
the map owes a row.

So this compares three enumerations of one set of files:

  1. the files defining the specs `spec_table` dispatches to;
  2. the `Sys/...` paths the WHERE A SPEC LIVES rows name;
  3. the modules `Specs.v` lists under `Require Export`.

and fails when (1) has a file missing from (2) or (3), or when (2) names a path
that is not on disk.

THE SYSCALL-NAME COLUMN IS DELIBERATELY NOT CHECKED. It is free prose, not a
list: rows carry phrases like `dup dup3, and which descriptor an open gets`,
one row's path sits on its own line with its kernel file on the next, and a
file's syscall names are not recoverable from the file without parsing the
whole spec. Matching those exactly means either rewriting the column into
something a machine reads -- which costs the sentence the column is there to
carry -- or a pattern loose enough to accept anything, which is a check that
reports nothing. The row's absence is the defect that shipped; the row's
wording is not. Leaving the column to a reader is the choice, not an oversight.
"""
import os
import re
import sys

ARMS = "theories/LinuxProcessSem/Sys/SyscallTable.v"
SPECS = "theories/LinuxProcessSem/Specs.v"
SYS = "theories/LinuxProcessSem/Sys"

# The arm's spec is whatever it applies after `=>`; the arguments in between
# vary with arity and are not read.
ARM_SPEC = re.compile(r"=>\s*([A-Za-z0-9_']+_spec)\b")
DEFINES = re.compile(r"^(?:Definition|Fixpoint)\s+([A-Za-z0-9_']+_spec)\b")
MAP_HEADER = "WHERE A SPEC LIVES"
ROW_PATH = re.compile(r"\bSys/[A-Za-z0-9_/]+\.v\b")
EXPORT_HEADER = "From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export"


def arm_specs(root):
    """The `<name>_spec` every arm of spec_table calls."""
    path = os.path.join(root, ARMS)
    with open(path) as f:
        lines = f.readlines()
    # `mkSpecArm` is matched on a word boundary, not as a substring: a
    # renamed constructor is the vacuous pass below, and a substring test
    # would take `mkSpecArmV2` for it and report the wrong failure.
    written, read, named = 0, set(), 0
    for line in lines:
        n = len(re.findall(r"\bmkSpecArm\b", line))
        written += n
        if not n:
            continue
        m = ARM_SPEC.search(line)
        if m:
            named += 1
            read.add(m.group(1))
    if not read:
        sys.exit(f"{path}: read no specs out of spec_table. Either the table "
                 "is empty or its arm shape changed and this reader no longer "
                 "recognises it. Both mean this check is measuring nothing, "
                 "so it fails here rather than reporting that every spec file "
                 "is on the map.")
    if named != written:
        sys.exit(f"{path}: {written} arms are written and {named} name a spec "
                 "this reader could take. An arm it skips is one whose file it "
                 "would never ask the map for, which is the omission this "
                 "check exists to report.")
    return read


def defining_files(root, specs):
    """spec name -> the `Sys/...` file that defines it, refusing 0 and 2."""
    where = {}
    base = os.path.join(root, SYS)
    for dirpath, _, names in os.walk(base):
        for name in sorted(names):
            if not name.endswith(".v"):
                continue
            full = os.path.join(dirpath, name)
            rel = "Sys/" + os.path.relpath(full, base).replace(os.sep, "/")
            with open(full) as f:
                for line in f:
                    m = DEFINES.match(line)
                    if not m or m.group(1) not in specs:
                        continue
                    got = m.group(1)
                    if got in where and where[got] != rel:
                        sys.exit(f"{SYS}: {got} is defined in {where[got]} and "
                                 f"in {rel}. Which file owes a row is then not "
                                 "a question this check can answer, and the "
                                 "build takes whichever module is imported "
                                 "last.")
                    where[got] = rel
    missing = sorted(s for s in specs if s not in where)
    if missing:
        sys.exit(f"{ARMS}: no file under {SYS} defines "
                 f"{', '.join(missing)}. spec_table dispatches to it, so "
                 "either the definition moved out of Sys/ or this reader no "
                 "longer recognises how it is written -- and a spec with no "
                 "file is a spec whose row nothing can ask for.")
    return where


def map_rows(root):
    """The `Sys/...` paths the WHERE A SPEC LIVES rows name."""
    path = os.path.join(root, SPECS)
    with open(path) as f:
        lines = f.readlines()
    start = next((i for i, l in enumerate(lines) if MAP_HEADER in l), None)
    if start is None:
        sys.exit(f"{path}: no {MAP_HEADER} block. The map is what this check "
                 "compares the spec files against; without it every file "
                 "would read as missing a row, or -- worse -- as needing "
                 "none.")
    # A row is a line naming a `Sys/...v` path.  The kernel file and the
    # syscall names beside it are prose and are not read (see the module
    # docstring).  One row in the real file puts its path on its own line
    # with the kernel file on the next, so the block ends at the first blank
    # line AFTER a row rather than at the first blank line, which is the one
    # separating this header from its first row.
    rows = {}
    for i in range(start + 1, len(lines)):
        line = lines[i]
        if not line.strip():
            if rows:
                break
            continue
        for m in ROW_PATH.finditer(line):
            rows.setdefault(m.group(0), i + 1)
    if not rows:
        sys.exit(f"{path}:{start + 1}: the {MAP_HEADER} block names no "
                 "Sys/ path. An empty map agrees with every spec file "
                 "vacuously, so it fails here instead.")
    return rows


def exported(root):
    """The modules Specs.v re-exports, as dotted names below Sys/."""
    path = os.path.join(root, SPECS)
    with open(path) as f:
        lines = f.readlines()
    start = next((i for i, l in enumerate(lines) if EXPORT_HEADER in l), None)
    if start is None:
        sys.exit(f"{path}: no `{EXPORT_HEADER}` block. That list is the second "
                 "enumeration this check compares, and a missing one would "
                 "read as every module exported.")
    block = []
    for i in range(start + 1, len(lines)):
        block.append(lines[i])
        if lines[i].rstrip().endswith("."):
            break
    names = {t.rstrip(".") for t in
             re.findall(r"[A-Za-z][A-Za-z0-9_'.]*", "".join(block))}
    if not names:
        sys.exit(f"{path}:{start + 1}: the `Require Export` block lists no "
                 "modules. An empty list agrees with every spec file "
                 "vacuously, so it fails here instead.")
    return names


def module_of(rel):
    """`Sys/Fs/EventPoll.v` -> `Fs.EventPoll`, as Specs.v spells it."""
    return rel[len("Sys/"):-len(".v")].replace("/", ".")


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    specs = arm_specs(root)
    files = defining_files(root, specs)
    rows = map_rows(root)
    mods = exported(root)

    owed = sorted(set(files.values()))
    problems = 0

    for rel in owed:
        if rel not in rows:
            callers = ", ".join(sorted(s for s, f in files.items()
                                       if f == rel))
            print(f"{rel} defines {callers}, which spec_table dispatches to, "
                  f"and has no row in {SPECS}'s {MAP_HEADER} map",
                  file=sys.stderr)
            problems += 1
        if module_of(rel) not in mods:
            print(f"{rel} defines a spec spec_table dispatches to, and "
                  f"{SPECS} does not Require Export {module_of(rel)}",
                  file=sys.stderr)
            problems += 1

    for rel, lineno in sorted(rows.items()):
        if not os.path.exists(os.path.join(root, "theories/LinuxProcessSem",
                                           rel)):
            print(f"{SPECS}:{lineno}: the map has a row for {rel}, which is "
                  "not a file", file=sys.stderr)
            problems += 1

    if problems:
        plural = "" if problems == 1 else "s"
        sys.exit(f"check_spec_file_map.py: {problems} problem{plural} across "
                 f"{len(owed)} spec files and {len(rows)} map rows")

    print(f"check_spec_file_map.py: {len(owed)} spec files, each with a map "
          f"row and a Require Export, out of {len(rows)} rows")


if __name__ == "__main__":
    main()
