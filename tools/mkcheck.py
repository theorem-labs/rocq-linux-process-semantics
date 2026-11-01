#!/usr/bin/env python3
"""Regenerate theories/LinuxProcessSem/ProcsCheck.v from Procs.v.

check_one.py compiles ONE file against the INSTALLED library, and
Ns/Tables.v is new on this branch, so the scratch copy inlines the real
file rather than a hand-written imitation: its records grow, and an
imitation would drift silently. Everything above Tables.v's own imports
is dropped, since Procs.v already imports more than it needs.

The scratch is for the one-second check only and is never committed.
"""
import re
import sys

TABLES = 'theories/LinuxProcessSem/Ns/Tables.v'
IMPORT = '''(** [NsState] and [NsCtx].  This file DEPENDS ON [Ns/Tables.v] and does not
    vendor it: two representations of one thing are what diverge. *)
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.
'''
ANCHOR = 'Local Open Scope bool_scope.'

src = open('theories/LinuxProcessSem/Procs.v').read()
if IMPORT not in src:
    sys.exit('mkcheck.py: the Ns/Tables import block is not where expected')

tables = open(TABLES).read()
# Drop Tables.v's own Require/Import lines: Procs.v has already issued them,
# and a second `Import ListNotations` is harmless but a second `From ...
# Require` inside a file body is not where we want surprises.
body = '\n'.join(l for l in tables.split('\n')
                 if not re.match(r'\s*(From|Require|Import)\b', l))

out = src.replace(IMPORT, '').replace(
    ANCHOR,
    ANCHOR + '\n\n(* SCRATCH ONLY -- Ns/Tables.v inlined verbatim; see tools/mkcheck.py. *)\n'
    + body + '\n', 1)
open('theories/LinuxProcessSem/ProcsCheck.v', 'w').write(out)
print('ProcsCheck.v regenerated (Tables.v inlined verbatim)')
