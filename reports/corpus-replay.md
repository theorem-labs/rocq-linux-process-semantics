# The recorded corpus against `revision/entry`

**Five traces broke.** Here they are, before anything else:

| trace | record | syscall | recorded | `revision/entry` |
| --- | --- | --- | --- | --- |
| `kernel_vma_range/001.jsonl` | 1 of 2 | `mmap` | `reject` | `unmodeled` |
| `kernel_vma_range/002.jsonl` | 1 of 2 | `munmap` | `reject` | `unmodeled` |
| `kernel_vma_range/003.jsonl` | 1 of 2 | `mmap` | `reject` | `unmodeled` |
| `mremap_shapes/037.jsonl` | 1 of 3 | `mremap` | `ok` | `reject` |
| `mremap_shapes/089.jsonl` | 1 of 3 | `mremap` | `ok` | `reject` |

I read all five. **Three of them are the documented closure condition of a known
bug, and two of them are the corpus being wrong about the machine it was
recorded on.** Neither group is a regression I can show. No sixth trace changed
a verdict word in either direction, on either pair of heads I measured.

The same five, and only these five, come out of both measurements: the pair the
branch was forked from (`75ad9d79` against `25e591a`) and the current pair
(`b1a36516` against `36811ec`).

---

## 1. The commands, and where each runs

From the Lean comparison lane's scripts at
`/mnt/nvme/sami/oss-verifier/sdd/ossv-265/slice-D-data/` on sami-rocqperf. The
lane did not answer in time, so these are read from the scripts themselves and
then run; every number below is from a run, not from the lane's recorded output.

Both traps the lane names are real and are respected here:

* **The harness lives OUTSIDE the tree under test.** `vm-rocq2.sh` puts it at
  `/work/harness-<tree>`, because `rocq-linux-process-semantics` has no root
  dune workspace and a `testing/syscall-check` copy inside the tree is part of
  the root dune project, which fails before `extract.sh` has run.
* **The link needs OCaml 5.3**, not the checker image's 4.14.3: `trace.ml` uses
  `Digest.BLAKE256`, which arrived in OCaml 5.2.

A third one, which the pull-request owner also named: **`vm-rocq2.sh` copies the
harness only when `$H` is absent**, so a second tree in the same harness
directory silently reuses the first tree's extraction. Every tree here got its
own `harness-<tree>` directory and its own extraction.

| step | machine | command |
| --- | --- | --- |
| build + extract | GCE VM `lpsrev-entry`, 32 vCPU | `docker run --rm --cpus 8 --user $(id -u):$(id -g) -v $HOME/replay-D:/work -w /work rc2-checker:1b59b23d bash /work/vm-rocq2-j8.sh <tree>` |
| link | same VM | `docker run --rm --cpus 8 --memory 32g --user 0:0 -v $HOME/replay-D:/work -w /work ocaml/opam:debian-12-ocaml-5.3 bash /work/build-main2.sh harness-<tree>` |
| replay | same VM, host python3 | `cd lps-ff03 && python3 rocqdiff.py --root . --out <json> -j 8 NAME=<main.exe> [NAME=...]` |

`-j 8` throughout, never two Rocq builds at once, and nothing built on
sami-rocqperf (load 252 on 64 cores when this started).

**The corpus.** theorem-labs/linux-process-semantics at `ff0313ba4f`,
`testing/syscall-check/traces/**/*.jsonl`: **4,291 traces, 55 MB** of trace data
in a 363 MB checkout (238 MB of which is `.git`).

**What `rocqdiff.py` calls a difference.** It runs `main.exe --replay <trace>`
per trace and reads the verdict line of each record, mapping `OK`,
`*** NOT ADMISSIBLE ***`, `*** UNMODELED (fail closed) ***` and
`*** MODELED MEMORY FAULT ***` to `ok`, `reject`, `unmodeled` and `fault`. It
writes one row per trace holding the recorded words, each checker's words and
each checker's exit status, and prints two summaries: exit status per checker,
and on how many traces each pair of checkers produced identical word lists.
Exit 0 means the replay reproduced the recording; exit 1 means it did not.

**Nobody had replayed a branch whose `ProcInput` grew a field.** It does not
work without a patch, and the patch is in section 6.

## 2. The reference: what a clean run looks like

The only way to tell a difference that belongs to a branch from one that belongs
to the harness is to replay the tree the corpus was recorded against.

```
ref-ff03 (linux-process-semantics @ ff0313ba4f):  4291 of 4291 reproduced
```

Nothing else. So the harness, the corpus and this rebuild of them agree
completely, and every disagreement reported below is between two model trees.

## 3. The baseline, measured here and not taken from anyone

The corpus was recorded against the OTHER repository's model tree. Replayed
against this repository the two disagree on hundreds of traces whatever any
branch does, so **every figure below is the difference from the branch's own
base.** The absolute counts are given only so the difference can be checked.

Base `b1a36516` (`Merge revision/linux-only (0a1180b6) into revision/all-fixes`):

```
base:   3939 of 4291 reproduced;  352 stopped on a verdict word
```

The branch it was forked from, `75ad9d79`, measured the same way, gives
`3930 / 361`. The 352 and the 361 are the distance between this repository and
`ff0313ba4f`, not anything about this branch: mostly `unmodeled -> ok`, i.e.
calls this repository models that the recording's model did not.

**Timings on `lpsrev-entry` at `-j 8`:** the whole `-core` package 11 min 50 s;
`Checks/Extraction.v`'s dependency cone alone 4 min 22 s; extraction 2–4 s;
the OCaml 5.3 link 50 s; a two-checker replay of all 4,291 traces 20–42 s.

**The cone is enough.** `vm-rocq2.sh` builds only
`--only-packages rocq-linux-process-semantics-core @install` and then compiles
`Checks/Extraction.v`. Nothing under `theories/Common` and nothing in
`Checks/Cases` is needed to extract the checker, so the replay can run while
those are still red. That is why this ran early, and the cone build is less than
half the cost of the package build.

## 4. `revision/entry`, and what every difference IS

Measured on `36811ec` against base `b1a36516`.

### 4a. With the harness as it ships

```
base:    3939 reproduced,  352 differ
entry:   1196 reproduced, 3095 differ   (2929 on the post-state digest, 166 on a verdict word)

BROKE 0 | REPRODUCES 0 | CHANGED 2743 | HARNESS 186 | unchanged-reproducing 1196 | unchanged-differing 166
```

Read on its own this looks like a catastrophe, and it is not one. **2,743 of
those traces differ only because the model's POST-STATE DIGEST moved.**
`Trace.verdict_equal` compares the verdict word, the event count AND the digest
of the whole model state, and `--replay` stops at the first record where any of
the three moves (`main.ml:2485`). This branch changes what `init_model`
reserves, so the digest of every post-state moves while every verdict word
stays, and the replay stops at record 0 of almost every trace — testing no
syscall rule at all. A further 186 traces are *blinded*: the branch stops at an
earlier record than the base did, so the base's own disagreement is never
reached and nothing can be said about it.

Linux produces no digest. The digest is the model's own state, so the recording
cannot arbitrate it, and stopping on it throws away the one thing the recording
CAN arbitrate.

### 4b. With the digest-tolerant replay (section 6, change 3)

```
base:    3939 reproduced,  352 differ on a verdict word
entry:   3934 reproduced,  357 differ on a verdict word

BROKE 5 | REPRODUCES 0 | CHANGED 0 | HARNESS 0 | unchanged-reproducing 3934 | unchanged-differing 352
```

`entry` minus `base` = **five traces**, all five listed at the top.

Of the five: `mmap` 2, `mremap` 2, `munmap` 1; `reject -> unmodeled` 3,
`ok -> reject` 2; none at record 0, all at record 1.

**Re-measured under the Lean lane's own version of the patch, which is
stronger than mine.** The lane took the patch into
`slice-D-data/harness-adapt.sh` and improved it in two ways: every substitution
now asserts how many sites it matched and refuses on any other number, and
`words_equal` compares events with `Trace.events_equal` — byte for byte — where
mine compared only the event COUNT. Theirs can only stop in more places than
mine, never fewer, so the five had to be re-checked against it. Both checkers
were rebuilt from a pristine `main.ml` through the lane's script and relinked:

```
base:   3939 reproduced, 352 differ on a verdict word
entry:  3934 reproduced, 357 differ on a verdict word
BROKE 5 — the same five traces, the same five moves
```

Unchanged. No record in the corpus keeps its verdict word and its event count
while changing an event byte, so the weaker comparison cost nothing here; the
lane's is still the one to keep, because nothing guarantees that for the next
branch.

### 4c. The five, read

**`kernel_vma_range/001,002,003` — `reject` becomes `unmodeled`. This is a
documented bug closing, not a break.**

The probe takes a NULL-hint grant and then issues a one-page `MAP_FIXED`
`PROT_NONE` mapping (or a `munmap`) at the page directly above it. On a real
riscv64 exec that page is the vvar's first page, and Linux answers `-EINVAL`
from `special_mapping_split`. The base model holds no entry for the vDSO/vvar
pair, calls the range free, asserts the grant, and so rejects the recorded run.
`revision/entry` holds the pair and declines instead.

`bugs/mmap-fixed-and-munmap-over-the-vdso-pair-assert-success.md` in the corpus
repository states the closure condition in its own words:

> The decline above, landing with `tests/kernel_vma_range.c`'s three `reject`
> lines flipped to `fail-closed --expect-unmodeled`, its `conform` lines on the
> free page below the grant unchanged […]

Three `reject` lines; this branch flips exactly those three, and leaves the
`conform` lines alone. The recorded `reject` is the old model's wrong answer,
and the corpus had already recorded the case this branch fixes — the same shape
as the file-faults branch's 34.

It does not fully close the entry: Linux's answer is `-EINVAL`, which a decline
still does not produce. The bug record says the decline is what closes it, so
this is the landing it names, and `tests/kernel_vma_range.c`'s three lines are
the edit that belongs with it.

**`mremap_shapes/037,089` — `ok` becomes `reject`. The corpus is wrong about its
own machine.**

The case line is `tests/mremap_shapes.c:58`:

```
// CASE: conform --mutate mremap:ret-addr:a0,drop-zeros,drop-unmaps,drop-copies,smuggle-zeros:a0+4096:4096 -- grow   # canonical Linux in-place grow, the neighbour being free
```

The neighbour is not free. The unmutated twin of the same case,
`mremap_shapes/033.jsonl`, records what the kernel really did:

```
mmap   (hint 0, len 0x1000)                 -> 0x7fff9feb5000
mremap (0x7fff9feb5000, 0x1000 -> 0x2000, MREMAP_MAYMOVE)
       -> 0x7fff9feb3000,  unmaps [0x7fff9feb5000 +0x1000],  copies 0x7fff9feb5000 -> 0x7fff9feb3000
```

It MOVED, because `0x7fff9feb6000` — the page above the grant — is the vvar's
first page (the header's `effective_mmap_base`). The mutated case then rewrites
the return to `a0` and drops the unmaps and copies, which is to say it asks the
model to admit an in-place grow that Linux refused. The base admits it, because
its ledger is empty there. `revision/entry` refuses it.

So the recorded `ok` is the base model's blindness, the branch's `reject` is the
right answer, and the comment "the neighbour being free" on
`tests/mremap_shapes.c:58` is false about the machine the corpus came from. That
is a corpus defect worth fixing whatever happens to this branch; its `movegrow`
twin at line 76 already says "an in-place grow needs the neighbour free".

**And the two are the whole of it.** The corpus holds 64 `mremap` growths that
returned an address: **13 resolved in place and 51 moved**, and 14 of the 51
moved with the vvar as their immediate neighbour. Of the 13 in-place ones,
**six end one page PAST the vvar start** — that is, they record an in-place
grow overlapping a mapping no process can expand into:

| trace | case | recorded verdict | in the five? |
| --- | --- | --- | --- |
| `mremap_shapes/037` | `conform` | `ok` | **yes** |
| `mremap_shapes/089` | `conform` (`--alloc-limit 0x2000`) | `ok` | **yes** |
| `mremap_shapes/038` | `reject` (+ `smuggle-unmap`) | `reject` | no |
| `mremap_shapes/039` | `reject` (+ `smuggle-copy`) | `reject` | no |
| `mremap_shapes/040` | `reject` (+ `smuggle-write`) | `reject` | no |
| `mremap_shapes/088` | `reject` (`--alloc-limit 0x1000`) | `reject` | no |

The four that are not in the five are rejected by BOTH trees anyway — their
mutation smuggles an unmap, a copy, a write, or busts the budget, so the base
refuses them for a reason that has nothing to do with the neighbour and no
verdict word moves. **The corpus asserts `ok` for exactly the two overlapping
in-place grows whose only defect is the neighbour, and `revision/entry` catches
exactly those two.** Nothing is missed and nothing is over-caught.

The negative control is in the same list: `mremap_shapes/055` and
`scenarios/mmap_mremap_madvise/004` grow to end exactly AT the vvar start, and
`mremap_shapes/077` ends a page below it. Those neighbours really are free, and
the branch treats all three identically to the base.

**Why the branch's `reject` follows, in the spec's own shape.** `mremap_spec`
on a grow is `if mremap_inplace_grow_b … then alt (in-place resolution) move
else move`. Under the base the ledger is empty above the grant, so
`mremap_inplace_grow_b` holds and the `alt` admits the in-place resolution the
mutated effect claims. Under `revision/entry` the vDSO/vvar pair is in the
ledger, `mremap_inplace_grow_b` is false, only the move arm remains, and an
effect with `ret = a0` and no unmaps or copies is not a move. The branch does
not need a new claim about when Linux moves — it needs only the neighbour to be
in the ledger, which is what OSSV-257 puts there.

### 4d. Traces that newly reproduce

**Zero.** No trace that the base failed to reproduce is reproduced by
`revision/entry`. The 352 traces the base cannot reproduce are reproduced by
neither tree and disagree identically in both.

## 5. What this replay could NOT see

Three things, and two of them were found by reading the harness rather than by
running it.

**The process start state.** `main.ml` never calls `Run.init_machine_state`; it
says so itself at `main.ml:3922-3925` — "This harness never builds one: it seeds
`State.init_model` and folds the syscall specs over what the tracer observed".
So no recorded run evaluates the entry block's bytes, the stack-pointer rule,
the stack-top rule, the auxiliary vector or `Run.valid_launch`.

It DOES build a `ProcInput`: `main.ml:2363` (the `--replay` seeding) and
`main.ml:3934` (the live run's) both call
`M.init_model reserved brk0 mbase sp lim inp` with `inp` an OCaml record literal
naming all fifteen released fields. `init_model`'s arity is unchanged on this
branch, so the call still type-checks; the literal does not, because OCaml
requires a record literal to name every field. That is the harness patch, not a
model defect.

**The launch the corpus came from.** The trace format (`lps-syscall-trace/2`)
records `kernel_release` but no kernel BUILD and no exec file name, so the
harness must DECLARE them, and it declares `State.default_kernel` — the ordinary
launch: no transparent huge pages, vDSO image 1, ASLR on, a 256-page guard gap,
`mmap_rnd_bits` 0, rseq on, no vector unit, no cache leaves. Every recorded run
came from one real machine whose build the format never captured. **So this
replay cannot say the reserved ledger is right for that machine. It says the
branch does not break the recorded runs under an ordinary launch.**

**Anything in absolute terms**, and any boundary the harness does not call. The
harness links `State.init_model`, the raw entry point, not
`CheckedInput.init_model_checked`, so nothing here exercises the checked
boundary either.

### How much of the corpus can reach the start state at all

The start state reaches a verdict only through what a syscall rule reads out of
the model: the mmap base, the allocation top, the stack window.

**The set decides the number, so here is the set.** 808 traces of 4,291 contain
at least one call from
**{`mmap`, `munmap`, `mremap`, `brk`, `mprotect`, `madvise`}**, counted whatever
the call returned. `msync` and `mincore` were looked for and are absent.

| | traces | records |
| --- | --- | --- |
| at least one call from that set | **808 (18.8%)** | |
| `mmap` | 763 | 1138 |
| `munmap` | 200 | 207 |
| `mremap` | 137 | 139 |
| `mprotect` | 88 | 93 |
| `brk` | 61 | 235 |
| `madvise` | 24 | 24 |
| `msync`, `mincore` | 0 | 0 |
| `mmap` whose hint is 0 (the mmap base decides the address) | **696** | 796 |

A narrower set gives a smaller number, and none of them is wrong — they answer
different questions. Every union, measured
(`/mnt/durable/scratch/lps-start-state-replay/reach-subsets.py`):

| set | any return | excluding calls that returned an errno |
| --- | --- | --- |
| {`mmap`} | 763 | 735 |
| {`mmap`, `munmap`} | 776 | 743 |
| {`mmap`, `munmap`, `mremap`} | 777 | 743 |
| {`mmap`, `munmap`, `mremap`, `mprotect`} | **779** | |
| {`mmap`, `munmap`, `mremap`, `brk`} | 803 | 770 |
| + `mprotect` | 805 | 771 |
| + `madvise` (**the 808 above**) | **808** | 772 |

**The 779 row is the placement lane's figure, and the two reconcile exactly.**
CorpusReplay counts {`mmap`, `munmap`, `mremap`, `mprotect`} on the same 4,291
traces with the same filter — every return, mutated records included — and gets
779. Measured here: 26 traces hold a `brk` and none of those four, and 3 more
hold a `madvise` and neither those four nor a `brk`. 779 + 26 + 3 = 808, with
nothing left over. Both numbers are right about different sets. The `4,266`
figure quoted elsewhere in this stream is a third thing and is neither lane's
denominator.

The other 3,483 traces cannot distinguish a right start state from a wrong one.

### What a trace that DID test the entry block would look like

A header that records the kernel build and the exec file name beside the seeds
it already carries, plus the stack VMA's bounds and the bytes the kernel really
left from `sp` up to the stack top, and one replay assertion that
`Run.init_machine_state segs pc ph sp mbase draw inp` reproduces those bytes and
that block exactly — the same shape as a syscall record, with
`init_machine_state` in the place of the syscall rule and the recorded stack
image in the place of the recorded effect.

That is a gap in the pipeline rather than a fault of this branch. It went to the
Lean comparison lane with the patch below.

## 6. The harness patch

The harness could not read this model. It was patched, not skipped. Three
changes, in `harness-adapt.sh` (new) called from `vm-rocq2.sh`. Every step is
guarded and is a no-op against a model that does not need it, so one harness
still builds the released pins unchanged — confirmed: `ref-ff03` and the two
base trees were built through the patched script.

**1. Declare the grown `ProcInput`.** `pre`: add `State.default_kernel` and
`State.default_execfn` to the extraction roots of the BUILD COPY when
`ProcInput` carries `in_execfn` (neither is reachable from
`Checks/Extraction.v`'s roots). `post`: name them in main.ml's two record
literals. Without this the harness does not compile at all.

**2. Pass the real mmap base.** `main.ml` gives `init_model` the `[vvar]` start
(`vvar_start_of_image`, `main.ml:1242`), and `main.ml:1240` says why: a model
that does not reserve the vDSO/vvar pair "needs no entry for the pair", so
starting the ledger at the pair's bottom IS reserving it. A model that DOES
reserve it then reserves the pair a second time, six pages below the real one,
on address space the kernel really hands out.

**This is the fourth kind of difference, and it had a number: 465 traces.**
Before the fix, `revision/entry` refused the first top-down anonymous grant of
465 recorded runs — every one `mmap`, every one `ok -> reject`, every one at
record 0. Worked example, `errno_mprotect/001.jsonl`: header `mmap_base`
`0x7fffb3a2f000`, `effective_mmap_base` `0x7fffb3a29000`, difference 24576 bytes
= 4 vvar + 2 vdso text pages = `vdso_len default_kernel` exactly; Linux granted
`0x7fffb3a28000`, the first page below the vvar, and the doubled reservation
covered it. After the fix the ledger reads
`[[0x7fffb3a29000, 16384], [0x7fffb3a2f000-8192, 8192]]` — the real pair — and
all 465 reproduce. **These 465 were a harness difference, not a model one.**

**3. `LPS_REPLAY_IGNORE_POST_STATE=1`.** With it, a disagreement whose verdict
word and event count are the recorded ones and whose post-state digest is not is
reported and carried past, instead of stopping the replay. Default behaviour is
unchanged. This is what turns section 4a into section 4b: 2,743 unreadable
"changes" and 186 blinded traces become five readable verdict moves.

Sent to the Lean comparison lane (Envoy session
`01a175f1-a3bf-71f2-a9b8-4f18af2e8f51`) as message
**`de801a273c8a4523ab0c718e4274ba21`**, which supersedes the earlier
`632c443a15ca5d7c1b7851a1349dae33` (that one's `pre` step appended the new roots
after the `Extraction` command's terminating period, a syntax error). The diff
is at `/mnt/durable/scratch/lps-start-state-replay/harness-patch.diff`.

**The lane has landed it.** `slice-D-data/vm-rocq2.sh` now calls
`slice-D-data/harness-adapt.sh`, so
`/mnt/nvme/sami/oss-verifier/sdd/ossv-265/slice-D-data/` is the patched harness
and is the copy to take. It carries two improvements over what I sent: every
substitution asserts its match count and refuses on any other number — a
`perl -0pi -e s///` that matches nothing exits 0, so an un-asserted rewrite
reports success, leaves the file alone, and the build then fails tens of minutes
later for a reason the log does not name — and `words_equal` compares events
with `Trace.events_equal` rather than by count. Section 4b was re-measured
against that version and is unchanged.

## 7. One change to a model tree, and it was not needed in the end

At `25e591a`, `theories/LinuxProcessSem/Checks/CheckedInput.v` was
byte-identical to the one on `revision/all-fixes` and gave fifteen arguments to
`mkProcInput_full`, which takes seventeen:

```
has type "option (KernelBuild → list byte → ProcInput)"
while it is expected to have type "option ProcInput".
```

Nothing in the `-core` package compiled past it, so the checker could not be
extracted. A shim passing `default_kernel` and `default_execfn` was applied to
the scratch copy of the tree under
`/mnt/durable/scratch/lps-start-state-replay/rocq-entry` — never to
`/home/sami/src/lps-entry` — purely to let the extraction run, and it cannot
move a verdict because `main.ml` calls the unchecked `init_model`.

**The shim is not in the final measurement.** `36811ec` carries the real fix:
`RawProcInput` now has `rpi_kernel : RawKernelBuild` and `rpi_execfn : list Z`,
and `rocq-entry2` was built with no shim at all.

## 8. Disk

**0.44 GB** persistent, under `/mnt/durable/scratch/lps-start-state-replay/`
(437 MB: the 363 MB corpus checkout, four exported trees, the scripts and the
result JSON). **0 GB** added to `/mnt/nvme` — the Lean lane's scripts were read
there and copied out, never written to. 0.99 GB transient on the GCE VM
`lpsrev-entry`'s own 290 GB root disk (986 MB of `~/replay-D`, including four
dune build trees and four linked checkers), which goes when the VM does. No new
checkout of theorem-labs/oss-verify-proofs-internal was made.

## 9. Where the artefacts are

On `lpsrev-entry` under `~/replay-D`: `ref.json` (the reference run),
`final-strict.json` and `final-tolerant.json` (base `b1a36516` against entry
`36811ec`), `readstop.json`/`readstop2.json`/`readstop3.json` (the earlier pair),
`build-*.log`, and the four `harness-*/` directories with their checkers.

The readers are at `/mnt/durable/scratch/lps-start-state-replay/`:
`readstop.py` (why each replay stopped: verdict word, event count, post-state
digest, or the final file-system verdict), `verdicts.py` (the four kinds),
`corpus-reach.py` (section 5's table), and `harness-adapt.sh` with
`harness-patch.diff`.
