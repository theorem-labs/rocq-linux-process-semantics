# The Lean twin of this Rocq model

This directory holds a Lean 4 copy of the Linux process model that
`theories/` defines in Rocq. It was imported from
theorem-labs/linux-process-semantics `lean/` at commit `ff0313ba4f`
(`UPSTREAM` has the commit, the date and the import command), and it is
being moved, file by file, to say what this repository's Rocq files say.

We keep it here, beside the Rocq files it copies, so that a reader can put
a Lean definition and the Rocq definition it comes from side by side, and
so that one pull request can change both.

## What `lean/twin` is not

`lean/twin` is the branch this directory lives on. It is not a revision of
the model. The revision of the model is pull request #38 on this
repository; when #38 merges, a later slice moves the twin onto it.

Nothing on `lean/twin` is published. It installs no opam package, it is in
no release, and no proof we have released depends on it.

The branch is cut from `f1006fe8178338a499b5e5c41be83006c4edd058` because
that commit is the Rocq model that the proofs we have released pin.
A Lean statement is only worth proving if it says what the released Rocq
statement says, so the twin ports the Rocq text our proofs were checked
against, and not a newer one. That reference does not move while phase 1
runs.

## The three rules

1. **The Rocq definition is the source.** Where the Lean file and the Rocq
   file disagree, the Rocq file wins, and the Lean file is changed. When
   the Rocq file is the one that is wrong about Linux, say so to the
   OSSV-266 lane with the Rocq symbol and the Linux source line; the fix
   goes into pull request #38, not into the Lean file.

2. **The twin never gates a Rocq change.** The job that builds this
   directory (`.github/workflows/lean-twin.yml`) is its own job. It runs
   on a pull request that touches `lean/` or that workflow file, on a push
   to `lean/twin`, and when someone starts it by hand; and it cannot fail
   a run. A red Lean build never stops a Rocq pull request from merging.

3. **Every Lean file a slice adds or changes names the Rocq file it
   ports**, as its first line:

   ```
   -- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Run.v
   ```

   The commit is `f1006fe8` throughout phase 1. A file that is still at
   its imported bytes carries no such header; its provenance is upstream's
   commit in `UPSTREAM`.

## References in a Lean file

The imported files cite upstream's tree. The rule:

1. Leave every machine-read metadata line exactly as upstream has it: a
   `probe:` line, a `divergence:` header line (both `-- inherited` and
   `-- fixed: <theorem>`) and an `inherited-divergence:` tag.
   `linux-process-semantics@ff0313ba4f:tools/lean_replay.py` (`:1476-1531`)
   and `linux-process-semantics@ff0313ba4f:tools/check_lean_pin_evidence.py`
   (`:1053-1055`) parse them with exact patterns, and they open the paths
   under `--root`. A rewritten line breaks a parser or a register entry.
2. Prose that cites a file this repository does not have names the
   repository and the commit instead of being deleted: a sentence citing
   `bugs/x.md` or `AGENTS.md` becomes
   `linux-process-semantics@ff0313ba4f:bugs/x.md`.
3. A difference with no `SCOPE.md` entry still gets a row in the slice's
   gaps file.

The twin's tools run with `--root` at a linux-process-semantics checkout,
which is also where the corpus and the harness are, so a `bugs/` or
`testing/` path in such a line resolves although this repository has
neither. The twin has nine `divergence:` lines today
(`EquivalenceDefinition/Equivalence.lean` 2, `.../FinInput.lean` 1,
`LinuxProcessSem/Sys/Fs/EventFd.lean` 1, `.../Sys/Mm/Mmap.lean` 5), all
`-- inherited`, which key to no syscall number and forgive nothing. A
`-- fixed: <theorem>` line is in the replay's verdict path: an entry of
`testing/syscall-check/traces/lean-divergences/` rests on it and forgives
a differing verdict
(`linux-process-semantics@ff0313ba4f:tools/lean_replay.py:1534,1587-1592`).
That register is empty at `ff0313ba4f`.

## Build it

Lean comes from elan, which reads `lean/lean-toolchain`
(`leanprover/lean4:v4.34.0`).

```sh
cd lean && lake build
```

Run it on a build VM, not on a shared box. A cold build of 653 jobs took
26 minutes on 64 CPUs (2026-10-31). Its three slowest modules are
`Checks.Cases.Fs.ReadWrite` (628 s),
`Checks.Cases.Checks.Sys.Net.Socket` (268 s) and the example image
`Examples.tail1_ns.SourceMemImage` (358 s).

`lake build` runs Python generators that render the syscall table, the
checked table and the example images. They are in `lean/tools/`, and the
image bytes of the twelve examples beside `rwx_flag_ns` are in
`lean/examples-rocq/`; upstream keeps both outside its `lean/`, and
`lean/UPSTREAM` says which file came from where. The generators read this
repository's Rocq tree, so what they render follows the Rocq model, which
is rule 1.

Upstream's own checks over this tree (`tools/check_lean_policy.py` and the
rest) are listed in `README.upstream.md`. They live in upstream's
repository, not here, so they run against upstream's checkout.

## Run the replay

The replay asks whether the Lean model gives the same verdict as the
recording on each of the 4,291 recorded traces. The traces, the OCaml
harness and the replay tool are all in linux-process-semantics; none of
them is copied here.

You need a checkout of linux-process-semantics `ff0313ba4f` (call it
`lps-ff03`) and its own OCaml checker, `main.exe`. Build that checker in
two steps, because the two halves need different compilers: its Rocq
theory extracts under Rocq 9.2 on OCaml 4.14, and `testing/syscall-check`
links under OCaml 5.2 or newer (`trace.ml` digests a post-state with
`Digest.BLAKE256`, which arrived in 5.2).

```sh
# 1. in lps-ff03, with Rocq 9.2:
dune build --only-packages linux-process-semantics @install
./testing/syscall-check/extract.sh          # writes syscall_model.ml
# 2. in lps-ff03/testing/syscall-check, with OCaml 5.3:
dune build --root . ./main.exe
# 3. in this repository:
cd lean && lake build lps_runner
# 4. back in lps-ff03:
python3 tools/lean_replay.py --root . \
    --lean-src <twin>/lean \
    --runner <twin>/lean/.lake/build/bin/lps_runner \
    --ocaml testing/syscall-check/_build/default/main.exe \
    -j 24 --max-report 100000 --json replay.json
```

`lps-ff03` must be a git repository: `lean_replay.py` resolves each
`rests_on` path with `git ls-files`, and an unpacked tarball has no `.git`.

`lean_replay.py` exits 0 when no occurrence disagrees, 1 on a Lean
disagreement, 2 on a run it could not judge as declared, 3 when the OCaml
checker does not reproduce a record of the corpus.

The import's own run exited 0: 4,291 of 4,291 traces reproduced by the
OCaml checker with no corpus defect, 18,662 of 19,693 recorded occurrences
reproduced by the Lean model, and **0 disagreements**. The remaining 1,031
occurrences are not failures and not passes: they are the port frontier,
320 unjudged (72 whose syscall number neither table carries, 244 declared
declines, 2 reader refusals, 2 runs declaring an address space other than
sv48) and 711 that come after one of those in their trace and so are never
compared.

Two things the replay does not tell you. It compares the Lean model with
the recording and with upstream's OCaml checker, not with this
repository's Rocq model, so it says the import is faithful to
`ff0313ba4f` and nothing yet about agreement with `f1006fe8`; that is what
the slices after this one change, area by area. And it cannot record: a
recording is a live run on the pinned kernel machine, which no build VM
has.
