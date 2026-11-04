#!/usr/bin/env python3
"""Bind the field-25 preservation predicates and option body to their source.

The existing check_pre_copies.py still checks all 604b5c3 copies unchanged.
This check additionally requires each pre24 predicate to be exactly its
pre23 body with the self-kill false conjunct appended, as it was before
field25. The inherited-input predicate and the no-hook setsockopt body
are compared directly with that immutable pre-field source.
"""

from pathlib import Path
import re
import subprocess
import sys

from check_pre_copies import COPIES, EMBEDDING, RUN, definition, words

BASE = "62437f65293650e1002b55535d16d6b62c20c541"
BPF_EMBEDDING = "theories/LinuxProcessSem/Checks/CgroupBpfEmbedding.v"
SOCKET = "theories/LinuxProcessSem/Sys/Net/Socket.v"


def rename(sentence, name):
    return re.sub(r"^Definition\s+\S+", "Definition " + name, sentence, count=1)


def compare(sources, embedding, bpf_embedding, socket):
    bad = []
    for name, path in COPIES:
        old = definition(sources[path], name)
        pre = definition(embedding, name + "_pre")
        if old is None or pre is None:
            bad.append(name + ": missing pre-field definition or pre23 copy")
            continue
        want = rename(pre, name)[:-1] + " /\\ in_selfkill_terminal inp = false."
        if words(old) != words(want):
            bad.append(name + ": pre24 is not the checked pre23 body plus selfkill=false")

    for name, path, text, copy_name in [
        ("valid_input_inherited", RUN, bpf_embedding, "valid_input_inherited_pre24"),
        ("setsockopt_spec", SOCKET, socket, "setsockopt_no_cgroup_bpf_spec"),
    ]:
        old = definition(sources[path], name)
        copy = definition(text, copy_name)
        if old is None or copy is None:
            bad.append(copy_name + ": missing pre-field source or current copy")
        elif words(copy) != words(rename(old, copy_name)):
            bad.append(copy_name + ": differs from its pre-field source")
    return bad


def main():
    sources = {}
    for path in sorted({path for _, path in COPIES} | {RUN, SOCKET}):
        result = subprocess.run(
            ["git", "show", BASE + ":" + path], capture_output=True, text=True
        )
        if result.returncode:
            print("::error::cannot read pre-field source " + BASE + ":" + path)
            return 1
        sources[path] = result.stdout
    bad = compare(
        sources,
        Path(EMBEDDING).read_text(encoding="utf-8"),
        Path(BPF_EMBEDDING).read_text(encoding="utf-8"),
        Path(SOCKET).read_text(encoding="utf-8"),
    )
    for error in bad:
        print("::error::" + error)
    if bad:
        return 1
    print("17 pre24 predicate compositions, the inherited predicate and setsockopt body match " + BASE)
    return 0


if __name__ == "__main__":
    sys.exit(main())
