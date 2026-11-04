#!/usr/bin/env python3
"""Fail when new code builds a growing record by position.

A record that gains fields (the process record grew from 15 to 20 fields in
two days) breaks every place that applies its constructor by position, and a
place that compiles by accident binds a value to the wrong field: a bool
where the old field was a bool, a word where the old field was a word.  Code
that reads and writes such a record through its accessors and setters
(m_child_pids, with_child_pids) never breaks.

This check counts, in every tracked Rocq, Python and OCaml file, the
applications of the constructors below, and compares the count per file with
tools/record_builders.json.  A count above the recorded one, or a file not
recorded, FAILS: write the new code through the accessors and setters.  A
place that must build the record by position (the record's own setters, a
fixture that pins every field) is recorded by running this script with
--update in the same change, where a reviewer sees the new count.  A name in
square brackets (a coqdoc reference, [mkProcState]) is not counted.

  check_record_builders.py            check (CI)
  check_record_builders.py --update   rewrite tools/record_builders.json
"""
import json
import re
import subprocess
import sys

CONSTRUCTORS = [
    "mkProcState",       # State.ProcState
    "mkProcInput_full",  # State.ProcInput (mkProcInput is the defaulting smart constructor)
    "mkKernelBuild",     # State.KernelBuild
    "mkVmState",         # State.VmState
    "mkShared",          # Procs.shared
    "mkNsState",         # Ns.Tables.NsState
    "mkNsEnv",           # Ns.Tables.NsEnv
    "mkNsCtx",           # Ns.Tables.NsCtx
    "mkSeqEnd",          # State.SeqEnd (future queue fields append here)
]
BASELINE = "tools/record_builders.json"
PATTERN = re.compile(r"(?<![\[A-Za-z0-9_'.])(" + "|".join(CONSTRUCTORS) + r")(?![A-Za-z0-9_'\]])")


def counts():
    # a path in a conflicted index is listed once per stage; count each file once
    files = sorted(set(subprocess.run(["git", "ls-files", "*.v", "*.py", "*.ml"], capture_output=True, text=True,
                                      check=True).stdout.split()))
    out = {}
    for f in files:
        if f == "tools/check_record_builders.py":
            continue
        try:
            text = open(f, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for m in PATTERN.finditer(text):
            out.setdefault(m.group(1), {}).setdefault(f, 0)
            out[m.group(1)][f] += 1
    return {c: dict(sorted(out.get(c, {}).items())) for c in CONSTRUCTORS}


def main():
    now = counts()
    if "--update" in sys.argv:
        with open(BASELINE, "w") as h:
            json.dump(now, h, indent=1, sort_keys=True)
            h.write("\n")
        print("wrote %s" % BASELINE)
        return 0
    base = json.load(open(BASELINE))
    bad = []
    for c in CONSTRUCTORS:
        for f, n in now[c].items():
            allowed = base.get(c, {}).get(f, 0)
            if n > allowed:
                bad.append("%s: %s applied %d times, %d recorded" % (f, c, n, allowed))
    for line in bad:
        print("::error::" + line)
    if bad:
        print("Build the record through its accessors and setters, or record the new count with "
              "`python3 tools/check_record_builders.py --update` in this change.")
        return 1
    print("no new positional builders of %s" % ", ".join(CONSTRUCTORS))
    return 0


if __name__ == "__main__":
    sys.exit(main())
