# Claim 2: the `init_model` timing, re-measured

**The fix is right and the measurement confirms it.** Flattening `init_model`
into one `mkModelOf` makes `Checks/Cases/Prelude.v`'s
`fd_truncation_high_low_halves_all_ebadf` **9,935 times cheaper** — 441.1 s at
the parent against 0.0444 s after, five runs each — and
`init_model_is_the_setter_chain` proves the two forms equal by computation, so
nothing that reads the model changed. The six corrections below are to the
numbers and the reason given for the change, not to the change.

Two of them are worth more than the arithmetic. **"Over 120 seconds" was a
lower bound published as a measurement**, and the real figure is 441 s, so the
fix is about four hundred times better than it claimed and the claim was still
unsupported. And **the premise that the parent's CI passed is false** — it was
cancelled on `ba8a152`; the passing run is on `6692dfb5`, a different commit
that happens to carry the same file — so a later reader would have taken
"CI passed on the parent" as evidence that this file compiled in under two
minutes, and it is not.

The third structural one: the chain is **six** links at that commit and seven
only after a later merge, and the term holds the **product** of the
per-setter occurrences, 2,785,671 copies counted in Rocq, not a power of
seven. A reason that names the wrong mechanism survives into the next
reader's head and sends them looking for the wrong thing.

What was checked: merge commit `5cfae0c` ("Merge revision/initmodel (362d9b5b) into revision/all-fixes") of theorem-labs/rocq-linux-process-semantics. Its commit text and the comment above `State.init_model` say:

> Measured on `Checks/Cases/Prelude.v`'s `fd_truncation_high_low_halves_all_ebadf`: the model named once 0.012 s; the setter chain written out twice, with a seven-link chain, over 120 s, a timeout; this form 0.095 s.

The comment also says that each `with_*` setter "rebuilds `mkModelOf` from SEVEN projections of its argument, so a chain of n of them denotes a term with 7^n copies of the innermost model".

## Short answer

| Published | Measured here | Verdict |
|---|---|---|
| parent, chain written out twice: "over 120 s" | Example **437.6 to 445.6 s** (5 runs, mean 441.1 s); whole file 449.4 to 457.4 s | The lower bound is **true** but understates the real time by about 3.7×. It is not a before-time. |
| that chain is "seven-link" | the parent's `init_model`, and `init_model_setter_chain` at 5cfae0c, have **six** links | **Wrong** for this commit. |
| 5cfae0c form: "0.095 s" | Example **0.044 to 0.046 s** (5 runs) | Same order of magnitude. The published figure names no machine, so the two cannot be compared further. |
| model named once: "0.012 s" | **not measured** | That variant of the file is not in the tree. Measuring it means editing `Prelude.v`, which the brief scoped out. |
| "7^n copies", "SEVEN projections" | 17·17·7·9·9·17 = **2,785,671** copies, confirmed by Rocq | **Wrong.** That is 23.7× 7^6 and 3.4× 7^7. Only `with_nofile` takes 7 projections. |
| "the kernel converts both sides" | about 227 s in the tactic sentence and about 214 s in `Qed` | **Half right.** The elaborator's tactic step and the kernel's `Qed` check each pay about half. |
| (brief) "LPS CI passed on the parent, so it did not take over 120 s" | CI was **cancelled** on ba8a152. CI passed on 6692dfb5, which has the same `Prelude.v` and the same six-link chain, and CI has no per-file time limit (jobs have `timeout-minutes: 300`). | The premise does not hold. A passing CI run puts no 120 s bound on this file. |

The speedup is real: the Example costs about **9,935×** less after 5cfae0c (441.1 s against 0.0444 s, means of 5 runs each).

## Machine, image, method

- **Machine:** GCE VM `ossv-lpsev-time`, us-central1-a, n2-highmem-16 (16 vCPU, Intel Xeon @ 2.80 GHz, 125 GiB). Each run logs the 1/5/15-minute load average at its start (`load_before`). The 1-minute figure was 0.12 to 1.31 over the 30 measured runs; about 1.0 is the previous run's own compile. Each compile is single-threaded: user time equals wall time to within 0.5 s.
- **Image:** `rc2-checker:1b59b23d`, `sha256:e9fa8b19d7cbab6127dfa522f9b9a02ad8c086febd809e58510ad96e78e24e14`. Rocq 9.2, OCaml 4.14.3, dune 3.23.0.
- **Trees:** `git archive` exports, one directory and one `_build` each.
  - `initmodel-parent.tar` → `ba8a152746ad607b9d81c2ade59b432120737567`
  - `initmodel-head.tar` → `5cfae0cd82605b6bc976411b014df1c3ace9e793`
  - Commit ids checked with `git get-tar-commit-id`.
  - `Prelude.v` is byte-identical at the two commits (`cmp`; sha256 `84bdc827…afea`).
- **Warm cone:** in each tree, `dune build --display short -j 16 theories/LinuxProcessSem/Checks/Cases/Prelude.vo` in the image (`scripts/cone.sh`). Both exit 0.
- **One timed run** (`scripts/time_one.sh <tree> <variant> <n>`):
  1. Copy the variant file to `_build/default/theories/LinuxProcessSem/Checks/Cases/Prelude.v`.
  2. Delete its `.vo/.glob/.vos/.vok/.aux` (cold `.vo`).
  3. Run the exact `rocq compile` that dune ran for that file (read from `_build/trace.csexp`), with `-time` added so each sentence's own time prints, under `/usr/bin/time -v`. Nothing else is rebuilt.

  ```
  rocq compile -time -q -w -notation-incompatible-prefix -w -abstract-large-number -w +notation-for-abbreviation \
    -w -deprecated-native-compiler-option -w -native-compiler-disabled -native-compiler ondemand -boot \
    -R /home/opam/.opam/4.14/lib/coq/theories Corelib -Q /home/opam/.opam/4.14/lib/coq/user-contrib/Stdlib Stdlib \
    -Q /home/opam/.opam/4.14/lib/coq/user-contrib/stdpp stdpp -Q /home/opam/.opam/4.14/lib/coq/user-contrib/ReadFile ReadFile \
    -Q /home/opam/.opam/4.14/lib/coq/user-contrib/Flocq Flocq -R theories LinuxProcessSemantics \
    theories/LinuxProcessSem/Checks/Cases/Prelude.v
  ```
  (cwd `<tree>/_build/default`, inside `docker run --rm -u 0 -v $HOME/claim2:/work … rc2-checker:1b59b23d`)
- **Timers:** `/usr/bin/time -v` elapsed wall time for the whole file; Rocq's own `-time` line for each sentence.
- **Order:** 20 runs, one at a time, interleaved: for n in 1..5, head/full, head/noex, parent/noex, parent/full (`scripts/time_all.sh`). The machine had no other work during these runs.
- **`noex` variant:** `Prelude.v` with lines 296-303 deleted. Those lines are exactly `Example fd_truncation_high_low_halves_all_ebadf … Proof. repeat constructor; check_eq. Qed.`, nothing else (sha256 `a342c138…e010`). No other line names the Example.

## 1. Both times, raw

Whole-file wall time, seconds. Every run had rocq exit 0.

| run | parent full | parent noex | head full | head noex |
|---|---|---|---|---|
| 1 | 457.37 | 12.66 | 12.47 | 12.74 |
| 2 | 452.84 | 13.42 | 13.32 | 12.69 |
| 3 | 449.42 | 12.68 | 12.80 | 12.65 |
| 4 | 455.29 | 13.01 | 12.62 | 12.74 |
| 5 | 450.40 | 12.68 | 12.57 | 12.74 |
| mean (sd) | 453.064 (3.314) | 12.890 (0.330) | 12.756 (0.337) | 12.712 (0.041) |

**The Example's cost by subtraction:**
- parent: 453.064 − 12.890 = **440.17 s**. Paired by run: 444.71, 439.42, 436.74, 442.28, 437.72.
- head: 12.756 − 12.712 = **0.044 s**. Paired by run: −0.27, 0.63, 0.15, −0.12, −0.17. This is inside the run-to-run spread of 0.85 s, so subtraction **cannot resolve** the head's cost.

**A better isolation that measures the same thing:** the `-time` lines of the Example's own four sentences (statement, `Proof.`, `repeat constructor; check_eq.`, `Qed.`), read from the same full-file runs. No text changes.

| run | parent: tactic / Qed / sum (s) | head: tactic / Qed / sum (s) |
|---|---|---|
| 1 | 229.056 / 216.537 / 445.600 | 0.019 / 0.018 / 0.044 |
| 2 | 227.385 / 213.503 / 440.896 | 0.020 / 0.019 / 0.046 |
| 3 | 225.190 / 212.378 / 437.575 | 0.019 / 0.018 / 0.044 |
| 4 | 228.971 / 214.499 / 443.477 | 0.019 / 0.018 / 0.044 |
| 5 | 225.802 / 212.117 / 437.926 | 0.019 / 0.018 / 0.044 |
| mean | 227.281 / 213.807 / **441.095** | 0.019 / 0.018 / **0.0444** |

The statement sentence is 0.007 s and `Proof.` is 0 s in every run. These are in the sums.

On the parent, the per-sentence sum (441.10 s) and the subtraction (440.17 s) agree to within 1 s. On the head, only the per-sentence figure resolves the cost. Maximum RSS: parent 589 MB, head 535 MB.

**What "over 120 s" is the time of.** The parent's six-link chain alone takes about 441 s, so the published lower bound holds for the code the parent had. The commit text attributes it to "a seven-link chain". A seven-link chain existed on `revision/vdso` (`ca39bcd`, which adds `with_kernel`). The commit's evidence line names VM `lpsrev-vdso`, so [INFERENCE] the ">120 s" run was made on that chain. I could not measure it: `ca39bcd` does not build in this image (`Checks/Witness/Mm/Mprotect.v:51` and `Checks/Sys/Mm/Mprotect.v:90` fail; `logs/cone-initmodel-vdso7.log`).

## 2. Chain length and copy counts

**Links.** `init_model_setter_chain` at 5cfae0c (State.v:5505-5524), like `init_model` at ba8a152 (State.v:5448-5467), is **six** setters around `mkModel`: `with_abort_terminal`, `with_sigmask`, `with_nofile`, `with_net`, `with_urandom`, `with_creds`. The comment's "seven-link chain" is wrong for this commit.

At the pull request's head `d4d2d93e`, `init_model_setter_chain` has **seven** links (`with_kernel` was added by a later merge), and the comment is unchanged. So "seven-link" now names the kept chain, but the timing figures under it were not measured on any chain the tree holds.

**Occurrences of `m` in each setter body** (`scripts/count_m.py`, reading `git show 5cfae0c:theories/LinuxProcessSem/State.v`; identical at ba8a152):

| setter | `m` occurrences | why |
|---|---|---|
| `with_abort_terminal` | 17 | 6 `mkModelOf` arguments + 11 in the rebuilt `mkProcState` |
| `with_sigmask` | 17 | the same |
| `with_nofile` | 7 | 6 + 1 in `mkLimState` |
| `with_net` | 9 | 6 + 3 in `mkIoState` |
| `with_urandom` | 9 | the same |
| `with_creds` | 17 | 6 + 11 in `mkProcState` |

- **Product: 17·17·7·9·9·17 = 2,785,671** copies of the innermost model.
- 7^6 = 117,649, so the true count is 23.7× the comment's formula for n = 6.
- 7^7 = 823,543, so the true count is 3.4× the figure the comment's "seven-link" implies.
- At `d4d2d93e` the seven-link kept chain adds `with_kernel` (9) and gives 25,071,039, which is 30.4× 7^7.

**Rocq confirms it** (`variants/LpsevTermSize2.v`, compiled against the head tree's warm cone; `logs/termsize2-initmodel-head.log`):
- Method: an opaque section variable `MZERO : Model` stands where the chain has `mkModel …`. Each setter and each chain prefix, from the innermost setter out, is unfolded by `Eval cbv beta delta [<setters>] in …` and written with `Redirect` under `Set Printing Depth 100000000`. The occurrences of `MZERO` are counted outside Rocq.
- Single setters: 17, 17, 7, 9, 9, 17.
- Chain prefixes: 17, 153, 1,377, 9,639, 163,863, **2,785,671**.
- The full six-link term prints as **404,231,697 bytes**. The compile took 59.42 s wall and 3.49 GB maximum RSS. With `Time`, the six-link `cbv` alone took 55.0 s (`logs/termsize-initmodel-head.log`).
- An artifact of the first run (`LpsevTermSize.v`, with `Time` prefixes and the default printing depth):
  - The `Time` message overwrote the first bytes of each `Redirect` file and so dropped one `MZERO` from each single-setter count (16/16/6/8/8/16).
  - Default depth elided 18 subterms as `(...)` in the six-link term, which printed 2,785,653 occurrences.
  - The second run removes both causes and is the measurement.

**Cross-check.** These counts came from my own script (`scripts/count_m.py`) and from the Rocq term count above. They agree exactly with the counts `LpsEvidence` derived independently: six links in the same order; 17, 17, 7, 9, 9, 17; product 2,785,671.

**Corroboration from another lane, not measured here.** `LpsEvidence` reports a whole-package `dune build -j 32` of `6692dfb5` on a 32-vCPU VM. That commit has the same `Prelude.v` and the same six-link `init_model` as ba8a152. LpsEvidence says the build spent over forty minutes inside `Checks/Cases` without finishing, while the post-flattening head's build on the same machine finished. I did not see that run's log.

## 3. A guard, proposed and not added

Measured first: does one wrapping setter restore the defect? Scratch tree `initmodel-onesetter` is 5cfae0c with only `init_model`'s body changed to `with_abort_terminal (in_abort_terminal inp) (mkModelOf …)` (`variants/State_onesetter.v`). Its cone builds and `init_model_is_the_setter_chain` still holds. Five runs:
- whole file 12.59, 12.58, 12.71, 12.58, 12.69 s;
- Example 0.054, 0.054, 0.053, 0.053, 0.055 s, against 0.044 at 5cfae0c.

So **one wrap is invisible in the build time.** The cost comes from nesting, and the chain is already 0.054 s → 441 s between one link and six. A guard that watches time cannot see the first wrap. Only a guard on the term's shape can.

| guard | cost | catches | misses | false alarms |
|---|---|---|---|---|
| **A. `Timeout n` on the Example's tactic.** `Proof. Timeout 10 (repeat constructor; check_eq). Qed.` Measured in the image: head passes (Example 0.044 s); one-setter passes (0.053 s); parent fails with `Error: Timeout!` at Prelude.v:303 after 10.0 s (file 11.00 s, exit 1). With `Timeout 1`: 1.09 s (file 2.11 s, exit 1). | one line in the test file; costs nothing on a good tree | a long chain, once it costs more than n s in this one Example | the first one to several wraps (one wrap: +0.009 s); any regression that this Example's conversion does not expose; the `Qed` half of the cost (about 214 s on the parent), which is unguarded, although the build already fails on the tactic | Margin over the head's 0.019 s tactic: 50× at `Timeout 1`, 500× at `Timeout 10`. I did not verify whether Rocq's `Timeout` counts wall-clock or CPU time; on an idle VM the two were equal (`10. secs (9.996u)`). If it counts wall-clock, a heavily loaded runner shrinks the margin: unsafe at 1 s, safe at 10 s. |
| **B. A source-level script** that `init_model`'s body (comments stripped) starts with `mkModelOf` and names no `with_*` (`scripts/check_init_model_flat.py`, a prototype). Run: passes 5cfae0c and d4d2d93; fails ba8a152, ca39bcd and the one-setter variant, naming the setters (`logs-guard-source.txt`; 0.4 to 0.6 s each on the loaded host). | one more CI step and a script to maintain | any wrap that uses a `with_*` name, including the first; `with_*` inside a field argument | a wrapper not named `with_*`; a `let`-bound rebuild | a regex over source: reformatting, a renamed definition or a comment the stripper misreads can break it. **Correction to the brief:** `.github/check_assumptions.py` is not a source-level check. It compiles each example's `Checker.v`, rechecks it with `rocqchk` and reads `Print Assumptions`, so B would be a new kind of check, not one of its family. |
| **C. An in-build shape check** next to `init_model_is_the_setter_chain` in State.v: a section over the six arguments, then `Goal True. let t := eval cbv delta [init_model] beta in (init_model reserved brk0 mbase sp lim inp) in lazymatch t with mkModelOf _ _ _ _ _ _ _ => idtac \| _ => fail 0 "init_model is not one mkModelOf application" end. exact I. Qed.` Measured (`variants/LpsevGuardShape.v`, `logs/guardshape.log`): head passes (compile 0.71 s, the tactic 0.001 s); one-setter and parent both fail with `Tactic failure: init_model is not one mkModelOf application`. | about ten lines in the file the property lives in; about 1 ms per build; no CI change | **any** outer wrap, whatever its name, including the first | a setter wrapped around one **field** inside `mkModelOf` (B catches that if the setter is named `with_*`) | only if `mkModelOf` or `init_model` is renamed, and then it fails with its own message. It reads the term, not the clock. |

**Recommendation:** add guard C beside `init_model_is_the_setter_chain` in `State.v`, because it is deterministic, costs about a millisecond and no CI step, and it is the only measured guard that fails on the first wrapping setter, which the timing guard cannot see.

## Files (on sami-rocqperf, under /mnt/durable/scratch/lpsev/claim2/)

- `claim2-report.md`: this report. `report.md` is an earlier copy without the cross-check paragraph.
- `stats.txt`: means, sd and paired differences computed from `summary.tsv`.
- `logs-guard-source.txt`: guard B on five `State.v` versions.
- `State_{ba8a152,5cfae0c,ca39bcd,d4d2d93}.v`, `Prelude_{ba8a152,5cfae0c,ca39bcd,d4d2d93}.v`: `git show` copies.
- `from-vm/logs/`:
  - `run-initmodel-{parent,head}-{full,noex}-{1..5}.log`: the 20 timed runs, each with image id, variant sha, load, `/usr/bin/time -v` and every `-time` line.
  - `run-initmodel-onesetter-full-{1..5}.log`
  - `run-initmodel-{head,onesetter,parent}-guard{1,10}-1.log`
  - `summary.tsv`, `time_all.log`, `phase2.log`
  - `cone-initmodel-{head,parent,onesetter,vdso7}.log`
  - `termsize-initmodel-head.log`, `termsize2-initmodel-head.log`
  - `guardshape.log`
  - `dune-trace-prelude.txt`: dune's own record of the parent's Prelude compile during the cone build, 446.49 s, one sample.
- `from-vm/scripts/`, `from-vm/variants/`: every script and file variant used. Their sha256 sums are in the logs.
- `from-vm/initmodel-head/_build/default/lpsev-termsize2/{one_*,chain1..4}.out`: Redirect outputs. On the VM only, too large to copy: `chain5.out` (20,003,169 bytes, sha256 `c940888c…f7`) and `chain6.out` (404,231,697 bytes, sha256 `a0973109…84`) under `~/claim2/initmodel-head/_build/default/lpsev-termsize2/`.

The VM `ossv-lpsev-time` still holds `~/claim2` with the four warm trees for reruns. No repository file was changed, and no branch or pull request was opened.
