#!/usr/bin/env python3
"""Regenerate theories/LinuxProcessSem/ProcsCheck.v for the one-file check.

tools/check_one.py compiles ONE file against the INSTALLED library, and
three files of this branch are new: Ns/Tables.v, Procs.v and
EquivalenceDefinition/MustExitP.v. So the scratch copy concatenates all
three, verbatim apart from their own Require/Import blocks, which the
header below issues once.

Verbatim on purpose: an imitation of Ns/Tables.v would drift, and its
records grew from two fields to seven within an hour of being written.

The scratch is for the check only and is never committed.
"""
import re

FILES = ['theories/LinuxProcessSem/Ns/Tables.v',
         'theories/LinuxProcessSem/Procs.v',
         'theories/EquivalenceDefinition/MustExitP.v',
         'theories/Examples/forkwait/Measure.v']

HEAD = '''From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.
'''

START = re.compile(r'\s*(From|Require|Import)\b')


def strip_requires(text):
    """Drop whole Require/Import commands, continuation lines included.

    A Rocq command runs to its terminating period, and this repository
    writes `From X Require Import` with the module list on the next line,
    so dropping only the first line leaves a bare list behind and the next
    command is a syntax error.
    """
    out, skipping = [], False
    for line in text.split('\n'):
        if skipping:
            if line.rstrip().endswith('.'):
                skipping = False
            continue
        if START.match(line):
            if not line.rstrip().endswith('.'):
                skipping = True
            continue
        out.append(line)
    return '\n'.join(out)


parts = [HEAD] + [strip_requires(open(f).read()) for f in FILES]
open('theories/LinuxProcessSem/ProcsCheck.v', 'w').write('\n'.join(parts))
print('ProcsCheck.v regenerated from', ', '.join(FILES))
