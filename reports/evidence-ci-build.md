# The `tests` theory's undeclared dependency, and why the build is green anyway

**The build is green. This is not a blocker.** `tests/dune` does not name the
theory that one of its files requires, and the build works because the
required files happen to sit under the directory the main theory is rooted at.
That is a dependency satisfied by directory layout rather than by declaration:
it would break the day `theories/Common` moves, and nothing would warn anyone.
**The recommendation is a one-line hardening, not a fix.**

This report exists because a run of mine disagreed with the gate, and the
disagreement had to be settled before anyone edited a model file on it.

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
its own directory with its own `_build`, on GCE VM `ossv-lpsrev-verify`
(n2d-highmem-32, northamerica-northeast1-a), in `rc2-checker:1b59b23d`
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

### The one run that failed, and what is known about it

One run did fail: a clean export of `d4d2d93e` in the same image on VM
`ossv-lpsev-start`, where `dune build -j 16` exited 1 after 769.8 s with

```
tests/VdsoReservedWitness.v:45:
Error: Unable to locate library AxSymExec3 with prefix LinuxProcessSemantics.Common
```

All twelve `tests/StartState*.vo` built in that tree; only that file failed.
Log: `~/claim3-build.log` on that VM, copied to
`/mnt/durable/scratch/lpsev/claim3/`.

**The one thing that run did differently** is that it had already built the
twelve generated test files on their own, in the same build directory, before
it ran the default target. That first build produces no `.vo` under
`theories/Common/`. Since nothing declares that `Tests` depends on `Common`,
dune is free to schedule `VdsoReservedWitness.v` before `Common`'s files
exist, and in a tree where the rest is already built there is little else to
schedule first.

**That is a hypothesis with one run behind it, not a settled cause.** The
experiment that separates it is running on `ossv-lpsrev-verify` as this is
written — two further exports of `d4d2d93e`, one building the twelve test
files first and then the default target, one building the default target
straight away:

```
bash ~/ci-variant-e.sh      # logs ~/ci-check/ci-{E,F}.log, driver ~/ci-variant-e.log
```

If E fails and F passes, the cause is the undeclared edge and the build order,
and the hardening below becomes a fix for a real intermittent failure rather
than a precaution. If both pass, the failure is unexplained and should be
recorded as such rather than attributed.

## What to do

**Add `LinuxProcessSemantics.Common` to `tests/dune`'s `(theories …)` list.**
One line. It costs nothing, it makes the dependency a declaration instead of a
coincidence of layout, and it gives dune the edge it needs to order the two.
Without it the build depends on `theories/Common/` staying inside the
directory the main theory is rooted at — which is exactly the kind of
condition this revision exists to turn into something checked.

That file is outside `reports/`, so this report does not make the change.
