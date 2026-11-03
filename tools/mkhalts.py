#!/usr/bin/env python3
"""Build theories/Examples/forkwait/HaltsCheck.v, a one-file scratch.

check_one.py cannot answer for anything under theories/Examples/: the
labelled image installs rocq-linux-process-semantics-core only, so
LinuxProcessSemantics.Common is off its load path. SymExec's scratch tree
has Common built, but it cannot have MY new files either, because
Ns/Tables.v, Ns/Ext.v, Procs.v, MustExitP.v and Measure.v are not in the
installed package and their logical prefix is already bound to it.

So those five are concatenated into one file that lives where the Examples
load path can see it, and ForkwaitSteps is imported normally because it IS
a real file in that tree.

Scratch only; never committed.
"""
import re

INLINE = ['theories/LinuxProcessSem/Ns/Tables.v',
          'theories/LinuxProcessSem/Ns/Ext.v',
          'theories/LinuxProcessSem/Procs.v',
          'theories/EquivalenceDefinition/MustExitP.v',
          'theories/Examples/forkwait/Measure.v',
          'theories/Examples/forkwait/Halts.v']

HEAD = '''From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From LinuxProcessSemantics.Examples.forkwait Require Import
  ForkwaitMemImage ForkwaitSteps.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.
'''

START = re.compile(r'\s*(From|Require|Import)\b')


def strip_requires(text):
    """Drop whole Require/Import commands, continuation lines included."""
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


parts = [HEAD] + [strip_requires(open(f).read()) for f in INLINE]
open('theories/Examples/forkwait/HaltsCheck.v', 'w').write('\n'.join(parts))
print('HaltsCheck.v regenerated from', ', '.join(INLINE))
