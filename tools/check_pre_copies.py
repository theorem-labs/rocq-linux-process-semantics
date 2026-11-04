#!/usr/bin/env python3
"""Fail when a pre-change copy in Checks/SelfkillEmbedding.v differs from its source.

theories/LinuxProcessSem/Checks/SelfkillEmbedding.v proves that the
self-kill declaration (State.ProcInput field 24) changes no statement
written before it.  It proves that against COPIES: each `<name>_pre` is the
body of `<name>` at commit 604b5c3, and `spec_table_pre_numbers` lists the
syscall numbers of that commit's table.  A proof about a wrong copy says
nothing about the old definition, and Rocq cannot read an old commit, so
this script compares each copy with `git show 604b5c3:<file>`, ignoring
only whitespace, and FAILS on any difference, or on a copy or a source it
cannot find.

  check_pre_copies.py   check (CI; needs the history, so fetch-depth: 0)
"""
import re
import subprocess
import sys

BASE = "604b5c371ed04d9094df7e1d53346d0611e06975"
EMBEDDING = "theories/LinuxProcessSem/Checks/SelfkillEmbedding.v"
RUN = "theories/LinuxProcessSem/Run.v"
FIN_INPUT = "theories/EquivalenceDefinition/FinInput.v"
TABLE = "theories/LinuxProcessSem/Sys/SyscallTable.v"

# Each definition the change touched, and the file it lived in at BASE.
COPIES = [
    ("valid_input", RUN),
    ("valid_input_abort", RUN),
    ("valid_input_either", RUN),
    ("valid_input_sigpipe_ignored", RUN),
    ("valid_input_sigpipe_either", RUN),
    ("valid_input_channel_closed", RUN),
    ("valid_input_channel_either", RUN),
    ("valid_input_paths", RUN),
    ("valid_input_sigpipe_kills", RUN),
    ("valid_input_sv39", RUN),
    ("valid_input_sv57", RUN),
    ("valid_input_va_any", RUN),
    ("valid_input_hwcap_rv64gc", RUN),
    ("valid_input_hwcap_rv64gcv", RUN),
    ("valid_input_abort_hwcap_rv64gc", RUN),
    ("valid_input_abort_hwcap_rv64gcv", RUN),
    ("finite_input", FIN_INPUT),
]

# A Rocq sentence ends at a period followed by white space; the period of a
# qualified name (State.default_urandom) is followed by a letter.
END = re.compile(r"\.(\s|$)")


def show(path):
    out = subprocess.run(["git", "show", "%s:%s" % (BASE, path)],
                         capture_output=True, text=True)
    if out.returncode != 0:
        sys.exit("::error::git show %s:%s failed (is the history fetched?): %s"
                 % (BASE[:7], path, out.stderr.strip()))
    return out.stdout


def definition(text, name):
    """The sentence `Definition <name> ... .`, or None."""
    start = re.search(r"^Definition\s+%s(?![A-Za-z0-9_'])" % re.escape(name), text, re.M)
    if not start:
        return None
    end = END.search(text, start.end())
    return text[start.start():end.start() + 1] if end else None


def words(text):
    return " ".join(text.split())


def main():
    copy_text = open(EMBEDDING, encoding="utf-8").read()
    sources = {}
    bad = []
    for name, path in COPIES:
        if path not in sources:
            sources[path] = show(path)
        old = definition(sources[path], name)
        new = definition(copy_text, name + "_pre")
        if old is None:
            bad.append("%s at %s has no Definition %s" % (path, BASE[:7], name))
            continue
        if new is None:
            bad.append("%s has no Definition %s_pre" % (EMBEDDING, name))
            continue
        want = words("Definition %s_pre" % name + old[len(re.match(r"Definition\s+\S+", old).group(0)):])
        if words(new) != want:
            bad.append("%s_pre in %s differs from %s in %s at %s"
                       % (name, EMBEDDING, name, path, BASE[:7]))

    table = re.search(r"^Definition spec_table\b(.*?)^\s*nil\.", show(TABLE), re.M | re.S)
    numbers = re.search(r"Lemma\s+spec_table_pre_numbers\s*:\s*arm_numbers\s+spec_table_pre\s*=\s*"
                        r"\[([^\]]*)\]%Z\s*\.", copy_text)
    if table is None:
        bad.append("%s at %s has no Definition spec_table ... nil." % (TABLE, BASE[:7]))
    elif numbers is None:
        bad.append("%s has no Lemma spec_table_pre_numbers with a literal list" % EMBEDDING)
    else:
        table_numbers = [int(n) for n in re.findall(r"mkSpecArm\s+(\d+)%Z", table.group(1))]
        try:
            got = [int(n) for n in numbers.group(1).split(";")]
        except ValueError:
            got = None
        if got != table_numbers:
            bad.append("spec_table_pre_numbers in %s is not the number list of %s at %s"
                       % (EMBEDDING, TABLE, BASE[:7]))

    for line in bad:
        print("::error::" + line)
    if bad:
        print("Copy each definition word for word from `git show %s:<file>`." % BASE[:7])
        return 1
    print("%d pre-change copies and the table's %d numbers match %s"
          % (len(COPIES), len(table_numbers), BASE[:7]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
