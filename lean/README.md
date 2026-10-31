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
repository, owned by the OSSV-266 lane; when #38 merges, a later slice
moves the twin onto it.

Nothing on `lean/twin` is published. It installs no opam package, it is in
no release, and no proof we have released depends on it.

The branch is cut from `f1006fe8178338a499b5e5c41be83006c4edd058` because
that commit is the Rocq model our released statements pin
(`release.yaml`, `semantics.commit`, in theorem-labs/oss-verify-proofs-internal).
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
   directory (`.github/workflows/lean-twin.yml`) is its own job, it runs
   only when a pull request touches `lean/`, and it cannot fail a run. A
   red Lean build never stops a Rocq pull request from merging.

3. **Every Lean file a slice adds or changes names the Rocq file it
   ports**, as its first line:

   ```
   -- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Run.v
   ```

   The commit is `f1006fe8` throughout phase 1. A file that is still at
   its imported bytes carries no such header; its provenance is upstream's
   commit in `UPSTREAM`.

## Build it

Lean comes from elan, which reads `lean/lean-toolchain`
(`leanprover/lean4:v4.34.0`).

```sh
cd lean && lake build
```

Run it on a build VM, not on sami-rocqperf. The measured cold build is in
`sdd/ossv-265/scale/task-Z1-report.md` of the oss-verifier checkout.

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

The replay answers one question: does the Lean model give the same verdict
as the OCaml checker on each of the 4,291 recorded traces? The traces, the
OCaml harness and the replay tool are all in linux-process-semantics; they
are not copied here.

Get a tree of linux-process-semantics `ff0313ba4f` (call it `lps-ff03`),
build its `main.exe` as
`sdd/ossv-265/slice-D-data/README.md` describes, build this directory's
runner, then:

```sh
cd lean && lake build lps_runner
cd <lps-ff03>
python3 tools/lean_replay.py --root . \
    --lean-src <twin>/lean \
    --runner <twin>/lean/.lake/build/bin/lps_runner \
    --ocaml <lps-ff03>/testing/syscall-check/_build/default/main.exe \
    -j 24 --max-report 100000 --json replay.json
```

`lean_replay.py` exits 0 when every trace agrees, 1 on a Lean
disagreement, 2 on a run it could not judge, 3 when the OCaml checker
itself does not reproduce a record. The import's own run gave 4,291 of
4,291 identical verdicts.

The traps the replay has (the tree must be a git repository, which image
builds what, why the OCaml link needs OCaml 5.2 or newer) are written once,
in `sdd/ossv-265/slice-D-data/README.md` of the oss-verifier checkout.
