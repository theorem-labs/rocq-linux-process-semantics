# Claim 1: the corpus replay of `revision/features`, measured

**The difference the merge commit claims is right and every absolute number
around it is wrong.** `revision/features` moves the corpus by **+32 traces**,
which is exactly what `ba8a152` says — but the corpus at `ff0313ba4f` holds
**4,291** traces and not 4,063, the base reproduces **3,896** and not 3,694,
and the branch **3,928** and not 3,726. The exclusive-append figure "34 of the
35" is 33 of 34 measured here, with the 34th mover in a different directory;
the one that does not move is named in [section 4](#4-the-one-that-did-not-move).

**4,063 is not this corpus's trace count at any commit of its last two hundred
that touched a trace.** That is stronger than "it cannot be reproduced": the
figure was never measured on this corpus. [Section 2](#2-the-corpus-and-the-4063).

## 1. What ran, where, and how

Every figure below is **a difference from the branch's own base**, never an
absolute count. The absolute counts are given only so the difference can be
checked: the corpus was recorded against the *other* repository's model tree,
so replayed against this repository the two disagree on hundreds of traces
whatever any branch does.

| | |
| --- | --- |
| base | `6692dfb52dbfd5c638dee49af544b6428001dc68` (`ba8a152^1`), export sha256 `ec2e668285da53476043784076c372880c9c11c7ae77b92cb4437a772fa1a808` |
| branch head | `83756dac794a54f4ae64e04220bfeb694854b85c` (`ba8a152^2`), export sha256 `25bae2d7a7c7f0a236190ae2ffb56d07997bd8b9af0ad5e54856d06f60ebf9d4` |
| the branch | three commits: `dddd2d3` (fcntl F_GETFD), `ccd80f6` (openat `O_WRONLY|O_CREAT|O_EXCL|O_APPEND`), `83756da` (a comment) |
| corpus | theorem-labs/linux-process-semantics at `ff0313ba4f2e9baffcf5b5f50bc9d31628ae8556`, working tree clean, `testing/syscall-check/traces/**/*.jsonl` |
| machine | a GCE build machine, n2-highmem-32, 32 vCPU, us-central1-a |
| image, build and extract | `rc2-checker:1b59b23d`, `sha256:e9fa8b19d7cbab6127dfa522f9b9a02ad8c086febd809e58510ad96e78e24e14` |
| image, link | `ocaml/opam:debian-12-ocaml-5.3` — the harness's `trace.ml` uses `Digest.BLAKE256`, which arrived in OCaml 5.2, and the checker image has 4.14.3 |
| harness | the Lean comparison lane's: `vm-rocq2.sh`, `build-main2.sh`, `harness-adapt.sh`, `rocqdiff.py`, taken unchanged |

Both traps the lane names are respected. **The harness lives outside the tree**
(`/work/harness-<tree>`), because this repository has no root dune workspace
and a `testing/syscall-check` copy inside it is part of the root dune project.
**The link needs OCaml 5.3.** And the third, which the pull request's owner
named: `vm-rocq2.sh` copies the harness only when the directory is absent, so
each tree got its own `harness-<tree>` and its own extraction.

**One change to the method, and it is why this finished.** `vm-rocq2.sh`
builds the whole `rocq-linux-process-semantics-core` package. Both of these
trees are **before** the `init_model` flattening of `5cfae0c`, so their
`Checks/Cases` files still carry the setter-chain term, and that build spent
forty minutes inside `Checks/Cases` without reaching the extraction. Nothing
under `Checks/Cases` and nothing under `theories/Common` is needed to extract
the checker, so the cone is both the cheap path and the same artifact; the
script run here, `vm-rocq2-cone2.sh`, builds

```
theories/LinuxProcessSem/{BvBase,Fs,Monad,State,Specs}.vo
theories/LinuxProcessSem/Checks/ExecutableSpecs.vo
```

and `Checks/CheckedInput.vo` only on a tree that has it — these two do not.
Everything else is the lane's script unchanged. The cone finished in about
four minutes a tree.

The commands:

```
docker run --rm -u 0 -e J=12 -v $HOME/replay-E:/work -w /work \
  rc2-checker:1b59b23d bash /work/vm-rocq2-cone2.sh <tree>
docker run --rm -u 0 -v $HOME/replay-E:/work -w /work \
  ocaml/opam:debian-12-ocaml-5.3 bash /work/build-main2.sh \
  harness-features-base harness-features-head
cd lps-ff03 && python3 rocqdiff.py --root . --out <json> -j 16 \
  base=<…/harness-features-base/_build/default/main.exe> \
  head=<…/harness-features-head/_build/default/main.exe>
```

and the same again with `LPS_REPLAY_IGNORE_POST_STATE=1`.

A trace "reproduces" for a checker exactly when `main.exe --replay <trace>`
exits 0, which is when every record's verdict word matched the recording.

**`harness-adapt.sh` reported, on both trees:** "the extracted `ProcInput`
carries no launch field — no declaration needed", and "the model does NOT
reserve the vDSO/vvar pair — keeping the `[vvar]` start". So neither of its
two model-dependent steps fired here; only `LPS_REPLAY_IGNORE_POST_STATE` was
added, and it changed nothing (below).

## 2. The corpus, and the 4,063

```
testing/syscall-check/traces/**/*.jsonl at ff0313ba4f:  4,291 traces
```

counted two ways, `git ls-files` and the working tree, both 4,291; the
checkout is clean at that commit. 23,984 syscall records.

**4,063 is not this corpus's trace count at any of its last two hundred
commits that touched a trace.** Counted with `git ls-tree -r --name-only <c> --
testing/syscall-check/traces` over all of them, the distinct counts are

```
3861 3868 3873 3875 3877 3889 4029 4056 4065 4066 4079 4083 4087 4090 4111
4114 4121 4125 4138 4146 4194 4230 4266 4270 4276 4290 4291
```

— it steps 4,056 → 4,065 and never passes through 4,063. So the published
figure is not a corpus version: it was never the number of traces in this
corpus, at `ff0313ba4f` or anywhere near it.

The published absolutes are each **202 lower** than the measured ones
(3,694 against 3,896; 3,726 against 3,928), on a count 228 lower. Whatever set
of traces was replayed, it was 228 traces short of `ff0313ba4f` and 202 of
those 228 would have reproduced. **The difference the two runs report is the
same, +32, which is the figure that means anything; the denominator and the
two absolutes are not reproducible.**

## 3. The measurement

**Digest-tolerant (`LPS_REPLAY_IGNORE_POST_STATE=1`):**

```
base   6692dfb5:  3896 of 4291 reproduced,  395 did not
head   83756dac:  3928 of 4291 reproduced,  363 did not

DIFFERENCE head - base = +32
BROKE 2 | REPRODUCES 34 | verdict-word lists identical on 4254 of 4291
```

**Strict, the harness exactly as it ships:**

```
base   6692dfb5:  3896 of 4291 reproduced,  395 did not
head   83756dac:  3928 of 4291 reproduced,  363 did not

DIFFERENCE head - base = +32
BROKE 2 | REPRODUCES 34 | verdict-word lists identical on 4254 of 4291
```

**Identical.** Unlike `revision/entry`, this branch moves no post-state digest:
it changes what `fcntl` and `openat` answer, not what `init_model` reserves, so
the digest-tolerant replay was not needed here. Saying so is the point —
`reports/corpus-replay.md`'s rule for the next merge predicted exactly this,
and a branch touching `Sys/Fs/*` and not `State.v`'s initial ledger is the case
it says is safe.

Every one of the 37 traces whose verdict-word list moved is one of the 36 the
two sets below name, and the moves are only two kinds:

```
unmodeled -> ok      21 records
unmodeled -> reject  16 records
```

Nothing moves from `ok`, `reject` or `fault` to anything. **The branch answers
calls the base declined; it changes no answer the base already gave.**

### 3a. Where the +32 is

| directory | traces | base reproduces | head reproduces | moved |
| --- | --- | --- | --- | --- |
| `openat_excl_append/` | 36 | **2** | **35** | **+33** |
| `openat_append/` (one trace, `045`) | 50 | 49 | 50 | **+1** |
| `fcntl*/` | 33 | **33** | **31** | **−2** |
| everything else | 4,172 | — | — | 0 |

+33 +1 −2 = **+32**.

### 3b. The two that broke, and why they are not regressions

Both are `fail-closed` cases of the F_GETFD cherry-pick, and both move
`unmodeled -> ok`:

| trace | case | what the record says |
| --- | --- | --- |
| `fcntl_spec/015.jsonl` | `fail-closed -- getfd   # F_GETFD reads the bit F_SETFD deliberately does not record` | record 1, `fcntl(3, F_GETFD)` → 0, recorded verdict **`unmodeled`** |
| `fcntl_spec/029.jsonl` | `fail-closed -- sockgetfd   # F_GETFD declines on the very fd kind F_GETFL is answered on: the two getters are not symmetric` | record 2, `fcntl(3, F_GETFD)` → 1, recorded verdict **`unmodeled`** |

The recorded word is `unmodeled` — **the old model's own decline, written down
as a decline.** Linux answered 0 and 1; the model had no arm and said so. The
branch adds the arm, answers, and the recording's `unmodeled` is no longer
what the model says. That is the recording being stale about the model, not the
branch being wrong about Linux, and it is exactly what `ba8a152` says: "the two
that move the other way were recorded as the old model's decline, not as a
kernel fact". **Measured, that sentence is right.** The two `fail-closed`
CASE lines in `testing/syscall-check/tests/fcntl_spec.c` are the edit that
belongs with this branch, in the corpus repository.

## 4. The one that did not move

Of the 36 traces under `openat_excl_append/`, two already reproduce at the
base — `035.jsonl` (`fail-closed --expect-unmodeled openat -- rdwr`, flags
`0x4c2`) and `036.jsonl` (`… -- no-creat`, flags `0x481`) — because both are
recorded `unmodeled` and both trees decline them. **So 34 are candidates, 33
move, and one does not:**

```
openat_excl_append/024.jsonl
  case: conform --mutate openat:ret=-EISDIR -- dot   # -EISDIR, the answer of v4.17 through v5.6
  record 0: openat(".", 0x4c1) -> 18446744073709551595   (= -EISDIR)   recorded ok
```

The base answers `unmodeled` (no exclusive-append arm at all); the branch
answers **`reject`**. It refuses because **it is right to**: the mutation asks
the model to admit `-EISDIR` for `openat(".", O_WRONLY|O_CREAT|O_EXCL|O_APPEND)`,
which is what Linux v4.17 through v5.6 answered, and `ba8a152` says in its own
body why that is not written:

> The directory reference answers EEXIST alone. Linux v6.18.46 fs/namei.c
> do_open returns -EEXIST at (open_flag & O_EXCL) && !(file->f_mode &
> FMODE_CREATED), before the directory test. The EISDIR answer of v4.17 to
> v5.6 is not written: the model describes v6.18.46 only.

So the single exception is the decision the stream owner took, landing exactly
where the decision says it should, and the trace it leaves unreproduced is a
mutation of a kernel the model does not describe. Its twin `022.jsonl`
(`conform -- dot`, the unmutated EEXIST case) moves to reproduced.

**The published sentence and the measurement, side by side:** "34 of the 35
exclusive-append traces move to reproduced" against **33 of the 34
exclusive-append candidates move**, with the 34th mover being
`openat_append/045.jsonl`, which is not an exclusive-append trace. The total
34 is right; its composition is not.

## Where this report disagrees with what was published

| published in `ba8a152` and the pull request's body | measured here |
| --- | --- |
| "the 4,063 recorded traces … at ff0313ba4f" | **4,291** traces at that commit, and 4,063 is not this corpus's count at any of its last 200 trace-touching commits |
| "3,726 reproduce against 3,694 for the base" | **3,928 against 3,896** — each 202 higher, on 228 more traces |
| the difference, +32 | **+32** — the same, and it is the only one of the four figures that is reproducible |
| "34 of the 35 exclusive-append traces move to reproduced" | **33 of the 34** exclusive-append candidates move; the 34th mover is `openat_append/045.jsonl`. The one that does not is `openat_excl_append/024.jsonl`, the `-EISDIR` mutation the branch deliberately refuses |
| "the two that move the other way were recorded as the old model's decline, not as a kernel fact" | **right**: `fcntl_spec/015` and `fcntl_spec/029`, both `fail-closed` cases whose recorded word is `unmodeled` |
