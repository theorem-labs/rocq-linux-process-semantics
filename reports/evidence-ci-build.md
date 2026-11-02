# The `tests` theory's undeclared dependency: reproduced, and a one-line fix

**`dune build` fails, reproducibly, after `dune build tests/StartState….vo`**
— which is the command `reports/a4-start-state.md` tells a reader to run.
`tests/dune` does not name the theory one of its files requires; the build
normally works because the required files sit under the directory the main
theory is rooted at, and dune, having no dependency edge, is free to schedule
that file before they exist. From a cold tree it does not; from a tree whose
`tests/` targets were built first, it does.

**CI is green and stays green** — the gate builds from cold and never runs a
`tests/` target first — so nothing published is blocked. **But the
recommendation is now a fix, not a hardening**: add
`LinuxProcessSemantics.Common` to `tests/dune`'s `(theories …)` list.

This report exists because a run of mine disagreed with the gate, and the
disagreement had to be settled before anyone edited a model file on it. It
is settled: both runs were right about what they ran.

## What the two files say

`tests/dune`, last stanza, byte-identical at `8368b4d0`, `d4d2d93e` and
`1b5b834917b7fbcf74542f06a7642f10c50dd440`:

```
(rocq.theory
 (name LinuxProcessSemantics.Tests)
 (theories Stdlib stdpp ReadFile LinuxProcessSemantics))
```

`tests/VdsoReservedWitness.v:45`, present at all three:

```coq
From LinuxProcessSemantics.Common Require Import AxSymExec3 AsanPlan AsanPlanSound.
```

`theories/Common/dune` declares a theory of its own, and it depends on the
main theory rather than the other way about:

```
(rocq.theory
 (name LinuxProcessSemantics.Common)
 (package rocq-linux-process-semantics-core)
 (theories Stdlib stdpp ReadFile Ltac2 Flocq LinuxProcessSemantics))
```

So `LinuxProcessSemantics.Common` is **not** reachable by naming
`LinuxProcessSemantics` in a `(theories …)` list, and the `Tests` theory names
nothing else that would bring it in.

**Why it builds all the same.** `theories/dune` declares the main theory over
`theories/` with `(include_subdirs qualified)`, so dune roots it at that
directory and passes `-R <…>/theories LinuxProcessSemantics`. That root is
recursive, and `theories/Common/` is inside it — so a consumer of the main
theory can resolve `LinuxProcessSemantics.Common.AxSymExec3` **by path**, from
the same `.vo` files the `Common` theory builds. Nothing declares that, and
dune has no dependency edge from `Tests` to `Common` to order the two.

## The runs

Four clean `git archive --prefix=lps/` exports of
`1b5b834917b7fbcf74542f06a7642f10c50dd440` (tarball sha256
`31c98f4948605ed2bf82271df4e2cc9db3b8a8df11e1ab2d31e9adc8e3a6fcb5`), each in
its own directory with its own `_build`, on one build machine
(n2d-highmem-32), in `rc2-checker:1b59b23d`
(`sha256:e9fa8b19d7cbab6127dfa522f9b9a02ad8c086febd809e58510ad96e78e24e14`):

| variant | command | exit |
| --- | --- | --- |
| A | `dune build --display short` (CI's own form, dune's default parallelism) | **0** |
| B | `dune build --display short -j 16` | **0** |
| C | the same, twice, the second from a warm tree | **0** |
| D | the same, after `rm -rf "$(rocq c -where)/user-contrib/LinuxProcessSemantics"` — the image carries an installed copy of the library and CI does not | **0** |

Logs: `~/ci-check/ci-{A,B,C,D}.log` on that VM.

GitHub's own check runs agree: on `d4d2d93e` and on `1b5b8349`, `Build and
check (Rocq 9.2)`, `(9.3)`, `(dev)` and `opam install` are all `success`, and
those jobs install dependencies only (`opam install -y -j 2 --deps-only .`)
before running the same `dune build --display short`.

**So the head builds, in CI's environment and in the pinned image, with and
without an installed copy of the library, at default parallelism and at
`-j 16`.**

### The failure, reproduced

One run failed first: a clean export of `d4d2d93e` in the same image on VM
the build machine, where `dune build -j 16` exited 1 after 769.8 s with

```
tests/VdsoReservedWitness.v:45:
Error: Unable to locate library AxSymExec3 with prefix LinuxProcessSemantics.Common
```

All twelve `tests/StartState*.vo` built in that tree; only that file failed.
Log: `~/claim3-build.log` on that build machine, copied to scratch.

**The one thing that run did differently** is that it had already built the
twelve generated test files on their own, in the same build directory, before
it ran the default target. Two further exports of `d4d2d93e` on the same build
machine, each in its own directory with its own `_build`, test
exactly that (`~/ci-variant-e.sh`, logs `~/ci-check/ci-{E,F}.log`):

| variant | command | exit |
| --- | --- | --- |
| E | `dune build -j 16 tests/StartState*.vo` **then** `dune build --display short -j 16` | **0**, then **1** |
| F | `dune build --display short -j 16` alone | **0** |

**E reproduces it**, and dune's own log shows the race it is:

```
        rocq theories/EquivalenceDefinition/FinInput.{glob,vo}
        rocq theories/LinuxProcessSem/OmniRun.{glob,vo}
        rocq theories/Common/ListFacts.{glob,vo}
        rocq tests/VdsoReservedWitness.{glob,vo} (exit 1)
File "./tests/VdsoReservedWitness.v", line 45, characters 49-59:
Error: Unable to locate library
AxSymExec3 with prefix LinuxProcessSemantics.Common (while searching for a .vos file).

        rocq theories/Common/Footprint.{glob,vo}
        rocq theories/Common/LiaFast.{glob,vo}
```

`tests/VdsoReservedWitness.v` is compiled **while `theories/Common` is still
being built**, because nothing declares that it must not be. Six variants in
all: A, B, C, D and F build from a tree with no `tests/` target already made
and all exit 0; E, the one that builds a `tests/` target first, exits 1.

**So the failure is not intermittent and not unexplained: it is what the
documented single-file command leaves behind.** `reports/a4-start-state.md`'s
own "How to reproduce" tells a reader to run
`dune build tests/StartStateNorandmapsSeed1Fixture.vo`, and a `dune build`
after that in the same tree fails.

## What to do

**Add `LinuxProcessSemantics.Common` to `tests/dune`'s `(theories …)` list.**
One line. It makes the dependency a declaration instead of a coincidence of
layout, and it gives dune the edge it needs to order the two — which is what
turns variant E green. Without it the build depends both on
`theories/Common/` staying inside the directory the main theory is rooted at
and on nobody having built a `tests/` target first.

That file is outside `reports/`, so this report does not make the change.

## A near-miss in the measuring, worth more than the finding

The second attempt at this experiment **measured the first attempt's tree**,
and nearly reported it as the rebased branch's result.

The runner unpacked its export only when the target directory was absent:

```bash
if [ ! -d "$W/lps-$v" ]; then … tar -x … ; fi
```

A `rm -rf` that was meant to clear it had not run — its output went to a
shell whose result was never read — so the run reused the previous export
**and its `_build`**, and came back red. The tarball on the machine was the
right one; the tree was not. It was caught only by reading **which file the
error named**: the failure quoted `Placement.linux_place_is`, which exists at
the commit the first attempt used and not at the commit the second was
supposed to be measuring.

**That is the same defect this revision keeps finding, in the instrument
rather than in the subject**: a step whose correctness rests on a condition
nothing states — here, that the directory was empty. It has appeared in a
build cache key that did not cover the installed libraries, a copy that only
ever added, a removal that failed silently as the wrong user, a harness that
copies only when absent, and now twice in this lane's own scripts.

**It would have been invisible in a green run.** A reused tree that happens
to pass looks exactly like a fresh tree that passes, and every number taken
from it would have been reported with the wrong commit beside it.

The three runners used for the measurements in this report and in
`reports/evidence-initmodel-timing.md` were rewritten to `rm -rf` the
directory unconditionally and to print the tarball's checksum at the top of
every log, so each log says which bytes it measured.

## Who reads this

Nobody imports these reports. The six evidence files under `reports/` are
read by people: nothing in the build, in CI or in any proof refers to them,
and a change to any of them cannot break anything. That is said here rather
than left to be assumed, because "who imports it" is a question this revision
asks of everything else it ships, and a reports-only branch is the one case
where the honest answer is nobody.
