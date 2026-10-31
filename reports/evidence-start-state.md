# Claim 3: the start state's acceptance against real kernels, re-measured

**The reproducible figure is 100 verdicts over 10 records with 0 failures, not
110**, and the 110-verdict capture cannot be reproduced from the tree at all.
**The merge commit's block range "528 to 7,936 bytes" is wrong for the records
in the tree**, which give 528 to 8,352; 7,936 was the maximum of the capture
that was replaced. **The Rocq check reproduces exactly** — twelve files, thirty
lemmas over the ten records and two more for the negatives, every one `Qed` and
closed under the global context.

One thing found on the way that is not about this claim and matters more than
it: **the default `dune build` exits 1 at the head**, so CI's first command
does not pass. It is in [section 4](#4-what-else-the-run-found) and was sent to
the pull request's owner the hour it was measured.

## What ran, where

| | |
| --- | --- |
| commit under test | `d4d2d93e776c445bcbc44387bd3a0eaa04cee543`, a fresh `git archive --prefix=head/` export, sha256 `f6c9aea55090bb0032582aa681266f4bad2b38f8644ba2e03e3cfdd8c558ebd0`, with its own `_build` |
| the Python checker | not in that tree: taken from `revision/place` at `88f88a1083c7a47f4525cf0d3eb727bf849df6e9`, export sha256 `cf436dce6ce5b85b6a346f543cddcff6487596f8914efc3496e77ed2f5bced84` |
| machine | GCE VM `ossv-lpsev-start`, n2-highmem-16, 16 vCPU, 125 GiB, idle during the timing runs |
| image | `rc2-checker:1b59b23d`, `sha256:e9fa8b19d7cbab6127dfa522f9b9a02ad8c086febd809e58510ad96e78e24e14` (Rocq 9.2, OCaml 4.14.3, dune 3.23.0, Python 3.12.3) |
| raw logs | `/mnt/durable/scratch/lpsev/claim3/` on sami-rocqperf |

## 1. The Python evidence run, and why 110 is not reproducible

**`check_start_state.py` was not in the pull request's tree when this ran.** At
`d4d2d93e`, `tools/placement_conformance/` carries only
`start_state_to_rocq.py`. The checker lived on `revision/place`, and none of
that branch's commits was an ancestor of that head. The ten records and the
generator are byte-identical in both trees. So the command
`reports/a4-start-state.md` gives under "How to reproduce" **could not be run
against `d4d2d93e`**: it exits 2, file not found. **That is fixed in the
branch's later heads**: `revision/place` merged at `b9c82f0`, so from there on
`tools/placement_conformance/check_start_state.py` is in the tree and the
command runs where it is given.

**How the script counts.** It prints no total, one PASSED or FAILED line per
verdict: three for sub-check 1, four for sub-check 2, three for sub-check 3 —
**ten verdicts per record**. `--vdso FILE` adds an eleventh, `vdso is the
build's`, **only when FILE exists**; a path that does not exist is passed over
in silence. Ten records therefore give **100** verdicts without a `vdso.so` and
**110** with one.

Run with the checker from `revision/place` over the head's ten records:

```
python3 <place>/tools/placement_conformance/check_start_state.py \
    tests/placement/linux-6.18.46-*.log
```

```
100 verdicts, 0 failures, 0 disagreements, exit 0
```

Ten ways of calling it were run; the ones a reader might use are these:

| run | command | verdicts | failures | exit |
| --- | --- | --- | --- | --- |
| the ten records, one call | the command above | **100** | **0** | **0** |
| the ten records, the `{fixture,long}` spelling | `… linux-6.18.46-*-{fixture,long}.log` | 100 | 0 | 0 |
| the report's own two commands, no `--vdso` | defconfig+norandmaps, then thp | 80 + 20 | 0 | 0, 0 |
| the report's own two commands, with its `--vdso $PC_WORK/…` | the files are absent | 80 + 20 | 0 | 0, 0 |
| `--vdso` pointing at a wrong file (a page of zeros) | a control | 110 | **10** | 1 |

The last row is the control that shows the eleventh verdict is real and can
fail: with a `vdso.so` that is not the kernel's, all ten extra verdicts fail.
**With the kernel's own `vdso.so` the count would be 110 — and that file
(sha256 `0d85f358656558c9fc4a6a620d31bf9bfef7f6f4f3797e44ed39cab23958df36`) is
in neither tree and on no machine reachable here.** So 110 is not reproducible,
which is what `reports/a4-start-state.md` already says and what the merge
commit does not.

## 2. The ten block lengths, and the published range

`stack_end − sp_at_start` equals the length of the recorded `stack_bytes` in
every record. Measured twice, once on the VM and once on sami-rocqperf from the
git objects of `d4d2d93e`:

| record | bytes |
| --- | --- |
| `norandmaps-seed1-fixture` | 528 |
| `norandmaps-seed1-long` | 4,384 |
| `defconfig-seed1-fixture` | 3,072 |
| `defconfig-seed1-long` | 4,592 |
| `defconfig-seed2-fixture` | 3,824 |
| `defconfig-seed2-long` | **8,352** |
| `defconfig-cache-seed1-fixture` | 2,560 |
| `defconfig-cache-seed1-long` | 7,088 |
| `thp-seed1-fixture` | 2,784 |
| `thp-seed1-long` | 5,648 |

**528 to 8,352. No record is 7,936 bytes long.**

Where 7,936 came from: the **first** capture, at commit `98f1800`, whose ten
records are 816, 7,568, 3,440, 5,744, 1,008, 7,936, 528, 4,384, 1,824 and
6,128 bytes — maximum 7,936. Commit `39dc6fb` replaced those records and moved
the report to 100 verdicts and 528 to 8,352. **The merge commit `d4d2d93`
carries the first capture's range and the first capture's verdict count beside
the second capture's records.**

Every record carries a 464-byte auxiliary vector, twenty-nine pairs, in all
ten.

## 3. The Rocq check, which is the number the revision should cite

Twelve generated files: ten records and two negatives. Each record file states
three check lemmas (`launch_ok`, `block_ok`, `auxv_ok`) and two local helpers;
each negative states one (`block_differs`) and the same two helpers. **Thirty
check lemmas over the ten records, thirty-two with the negatives**, fifty-six
counting the twenty-four helpers. That is exactly what
`reports/a4-start-state.md` says.

- Every one is closed by `Qed`. No `Admitted`, `Axiom`, `admit`, `Parameter`,
  `Abort` or `Defined` appears in any generated file.
- `Print Assumptions` on all thirty-two check lemmas: **thirty-two of
  thirty-two "Closed under the global context"**.
- `rocqchk -o` over the twelve modules: exit 0, "Modules were successfully
  checked", 69.5 s. It lists the axioms of the whole loaded closure (the Int63
  and PrimString primitives, `functional_extensionality_dep`, `classic`,
  `sig_forall_dec`, `sig_not_dec`); `Print Assumptions` shows that none of the
  thirty-two lemmas uses any of them.

**The two negatives are the ones named**, and each states a disagreement
(`entry_stack_image … <> rec_stack_bytes`, by `vm_compute` and `discriminate`):

| file | byte moved | kernel's value → the file's | admitted neighbour |
| --- | --- | --- | --- |
| `StartStateNorandmapsSeed1FixtureMoved` | 0 of 528 | 1 → 2 | `StartStateNorandmapsSeed1Fixture` |
| `StartStateDefconfigSeed2LongMoved` | 7,000 of 8,352 | 120 → 121 | `StartStateDefconfigSeed2Long` |

**Serial timing**, each file compiled alone with dune's own `rocq compile`
flags into a fresh empty directory, five runs of the whole set, no failures
(seconds):

| file | r1 | r2 | r3 | r4 | r5 | median | published |
| --- | --- | --- | --- | --- | --- | --- | --- |
| NorandmapsSeed1Fixture | 1.008 | 0.987 | 0.980 | 0.974 | 0.976 | 0.980 | 0.87 |
| NorandmapsSeed1Long | 2.309 | 2.258 | 2.256 | 2.295 | 2.260 | 2.260 | 1.87 |
| DefconfigSeed1Fixture | 1.232 | 1.221 | 1.216 | 1.235 | 1.244 | 1.232 | 1.07 |
| DefconfigSeed1Long | 2.252 | 2.245 | 2.315 | 2.259 | 2.278 | 2.259 | 1.86 |
| DefconfigSeed2Fixture | 1.296 | 1.330 | 1.320 | 1.288 | 1.326 | 1.320 | 1.14 |
| DefconfigSeed2Long | 2.833 | 2.859 | 2.906 | 2.873 | 2.915 | 2.873 | 2.52 |
| DefconfigCacheSeed1Fixture | 1.171 | 1.156 | 1.189 | 1.178 | 1.188 | 1.178 | 1.04 |
| DefconfigCacheSeed1Long | 2.761 | 2.697 | 2.787 | 2.689 | 2.711 | 2.711 | 2.23 |
| ThpSeed1Fixture | 1.233 | 1.185 | 1.214 | 1.203 | 1.208 | 1.208 | 1.06 |
| ThpSeed1Long | 2.534 | 2.511 | 2.584 | 2.583 | 2.501 | 2.534 | 2.09 |
| NorandmapsSeed1FixtureMoved | 1.042 | 1.048 | 1.049 | 1.062 | 1.038 | 1.048 | 1.00 |
| DefconfigSeed2LongMoved | 4.784 | 4.847 | 4.814 | 4.877 | 4.872 | 4.847 | 4.08 |
| **the ten records** | 18.629 | 18.449 | 18.767 | 18.577 | 18.607 | **18.607** | 15.7 |
| **all twelve** | 24.455 | 24.344 | 24.630 | 24.516 | 24.517 | **24.516** | 20.8 |

Every file is 5 to 22 % slower here and both totals about 18 % slower, with the
files in the same order. The published times were measured on a different
32-vCPU VM, so **that is a machine difference and not a disagreement.** The
lemma count, which is not a machine difference, matches exactly.

**One piece of the published evidence should be dropped.**
`reports/a4-start-state.md` offers `python3 .github/check_assumptions.py` as
the check that no generated file carries an `Admitted`, `Axiom`, `admit` or
`Parameter`. Run here it prints `rwx_flag_ns: ok` and exits 0 — because it
reads `theories/Examples/*/Checker.v` and **never opens `tests/StartState*.v`**.
The thirty-two `Print Assumptions` results above are the evidence for those
files; `check_assumptions.py` is not.

## 4. What else the run found

**The default `dune build` exits 1 at `d4d2d93e`.** The cone of the twelve test
files builds (exit 0, 141.6 s), and all twelve `StartState*.vo` build; the
default target fails after 769.8 s at

```
tests/VdsoReservedWitness.v:45:
Error: Unable to locate library AxSymExec3 with prefix LinuxProcessSemantics.Common
```

`tests/dune`'s theory list is `(theories Stdlib stdpp ReadFile
LinuxProcessSemantics)` and does not name `LinuxProcessSemantics.Common`, which
`theories/Common/dune` declares as a theory of its own. The same two lines are
unchanged at `8368b4d0` and at `1b5b834917b7fbcf74542f06a7642f10c50dd440`. The
first of CI's five commands is `dune build`, so the merge commit's "LPS CI
passes on 8368b4d0, five commands on a clean export of that commit" does not
hold of the command as run here. GitHub's own check runs for `d4d2d93e` are
green, so the two disagree about one command on one commit, and
[`reports/evidence-ci-build.md`](evidence-ci-build.md) is the experiment that
separates them.

## Where this report disagrees with what was published

| published | where | measured |
| --- | --- | --- |
| "110 verdicts and 0 failures" | merge commit `d4d2d93` | **100** verdicts, 0 failures, exit 0 — and only with a checker that is not in this tree. 110 needs the kernel build's `vdso.so`, which is in neither tree. |
| "from 528 to 7,936 bytes" | merge commit `d4d2d93` | **528 to 8,352**. 7,936 is the maximum of the replaced first capture. |
| "30 lemmas, all `Qed`, 15.7 s; 20.8 s with the two negatives" | `reports/a4-start-state.md` | **30 + 2 lemmas, all `Qed`, all closed under the global context** — exact. 18.6 s and 24.5 s here, a machine difference. |
| `.github/check_assumptions.py` as the assumption check for the generated files | `reports/a4-start-state.md` | it does not read them; `Print Assumptions` over the thirty-two lemmas does. |
