# Claim 4: is any recorded result void? The corpus through the checked entry point

**The prediction was zero refusals. It is one, and the one is right.** The
recorded corpus holds exactly one record whose value is outside the Rocq type,
`set_tid/022.jsonl`'s second `set_tid_address` with `ret = 2^64`, and the
corpus keeps it on purpose. The checked boundary refuses it, which is what the
boundary is for — but it means the sentence "the corpus passes the boundary"
is false, and the sentence the revision can say instead is in
[section 4](#4-what-the-revision-can-say).

**And the claim this report was asked to settle is contradicted.** The state
record of the extraction work says

> every caller was read in full, and each stayed in type by a hand-written
> habit that nothing checked

There is no habit. The reader that builds the checker's inputs accepts a value
at or above 2^64 **by design**, says so in a comment, and the corpus holds a
record that uses it. The callers and what each checks are in
[section 3](#3-the-callers-of-the-raw-entry-points).

The run that counts the refusals is [section 5](#5-the-run-the-corpus-through-the-checked-entry-point);
the machine, image and commits are there.

## 1. What the checked boundary is, and what it cannot hide

`theories/LinuxProcessSem/Checks/Extraction.v` at `d4d2d93e` says it in its
own words, and this is the sentence the review quotes against the state
record:

> `[check_syscall_for_run]`, `[init_model]`, `[mkInput]`, `[mkEffectU]`,
> `[mkCopy]` and `[net_silent]` are NOT roots any more: each is reached
> through its checked form, and naming one here would publish a way into the
> checker that no boundary guards.  (The generated .mli publishes everything
> the roots reach, these included, so no choice of roots can hide them; the
> roots are what this tree supports, and what a reader must use.)

So the raw entry points stay callable. The boundary is a **supported surface**,
not an access control, and the only thing that can say whether a caller stays
in type is a reading of the callers — or a run.

The boundary itself is `Checks/CheckedInput.v`:

```coq
Definition check_syscall_for_run_checked
    (ri : RawInput) (re : RawEffect) (m : Model) : checked_answer :=
  match input_of_raw ri, effect_of_raw re with
  | Some i, Some e => CheckedAnswer (check_syscall_for_run i e m)
  | _, _ => CheckedRefused
  end.
```

`CheckedRefused` is a third answer. `CheckedInput.v` says so: "it says the
boundary was handed something that is not a machine observation, and that the
checker was never asked. A caller that counts verdicts must count this
separately — it is neither a pass nor a conformance failure."

## 2. The corpus, read for values outside the type

Before running anything: every field of every record that the reader turns
into a model `word` was scanned for a decimal at or above 2^64 — `sysno`,
each of the six `args`, `effect.ret`, every `in_mem[].addr`, every `in_wmem`
range, every `writes[].addr`, and every entry of `zeros`, `unmaps`, `copies`
and `copyins`, plus the header's `alloc_limit`, `entry_sp`, `initial_brk`,
`mmap_base`, `effective_mmap_base`, `nofile`, `entry_sigmask`, `hwcap` and
every `load_segments` pair.

```
traces scanned: 4291   syscall records: 23984   unparsable lines: 0
traces holding a word field >= 2^64: 1
  set_tid/022.jsonl   record line 2:  effect.ret = 18446744073709551616
```

`18446744073709551616` is 2^64 exactly. The trace's header reads

```
case: reject --mutate set_tid_address#2:ret=2^64 -- two   # pinned: an out-of-range 2^64 answer
mutations: ["set_tid_address#2:ret=2^64"]
```

and the record's own recorded verdict is `reject`. The case is
`testing/syscall-check/tests/set_tid.c:64`.

**The corpus keeps that value deliberately, and its reader says why**
(`testing/syscall-check/trace.ml:269-279`):

> A word is any non-negative integer, NOT one below 2^64: the checker's word
> type is the model's `[bv]`, which is Z, and a case's --mutate may hand it a
> value no register holds — `ret=2^64` is in the op vocabulary (main.ml,
> `[parse_value]`) exactly so a spec can be pinned to reject an answer outside
> the width.  tests/set_tid.c's `two` case stages that, and the live run
> records the pair as the checker saw it.  A reader bounding the field at 2^64
> refused that record as malformed and so could not replay a verdict the
> checker really gave; the bound was the reader's own, and the corpus
> (traces/README.md) is what found it.

So the two repositories hold opposite positions about one record, and neither
is an oversight:

| | what it says about `set_tid/022` record 1 |
| --- | --- |
| theorem-labs/linux-process-semantics at `ff0313ba4f` | a recorded pair whose right verdict is `reject`, pinned so that a spec cannot drift into admitting an out-of-width answer |
| `Checks/CheckedInput.v` at `d4d2d93e` | not a machine observation at all; the checker is never asked, and the answer is `CheckedRefused` |

## 3. The callers of the raw entry points

Read at `ff0313ba4f2e9baffcf5b5f50bc9d31628ae8556` of
theorem-labs/linux-process-semantics. That tree's own `Checks/Extraction.v`
still names the raw functions as roots and contains no `CheckedInput`,
`_checked` or `mkRaw` text at all, so **every caller there is a raw caller**;
the checked boundary has no call site in that repository.

Only `testing/syscall-check/main.ml` and `trace.ml` use the extracted module
(`module M = Syscall_model`). A search of the whole repository for
`Syscall_model`, `init_model`, `mkProcInput` and `check_syscall_for_run` found
no other `.ml`, shell, Python or Lean caller; `extract.sh` and `run-tests.sh`
only run the extraction.

| # | file:line | entry point | fields passed | range-check before the call |
| --- | --- | --- | --- | --- |
| 1 | `main.ml:2083`, in `run_check` | `M.check_syscall_for_run input eff !model` | `in_sysno`, `in_args`, `in_mem`, `in_wmem`; `eff_ret`, `eff_writes`, `eff_zeros`, `eff_unmaps`, `eff_copies`, `eff_copyins` | **none here.** It is the one place every pair meets the checker, live and replayed. What its two sources check is rows 2, 3 and 6. |
| 2 | `main.ml:2435` (replay input) with `trace.ml:826-830` (replay effect) | builds the `M.syscallInput` / `M.syscallEffect` that row 1 receives | every input and effect field | **none.** `trace.ml:280` `as_word` checks only that the string is a non-empty run of decimal digits and then calls `Big_int_Z.big_int_of_string`. There is no `< 2^64` test, and `trace.ml:269-279` (quoted above) says the absence is deliberate. Bytes come from `bytes_of_string` and are 0..255. |
| 3 | `main.ml:5027` (live input), `:5041` and `:6457` (effect) | the same records, from the tracer | `in_sysno = nr_word`, `in_args`, `ret`, writes | **partial.** `guest.ml:161` `get_u64` reads eight bytes into a non-negative bignum, so a register-sourced value is below 2^64 by construction; `get_i64` (`:171`) subtracts 2^64. `main.ml:4445` checks only that a7 equals `nr_word`. The mutation operators in row 6 can undo even this. |
| 4 | `main.ml:2363-2380`, in `replay` | `M.init_model` | `h_load_segments`, `h_initial_brk`, `h_effective_mmap_base`, `h_entry_sp`, `h_alloc_limit`, and a `ProcInput` literal with `in_uid`, `in_gid`, `in_groups`, `in_nofile`, `in_sigmask`, `in_hwcap`, `in_stdin`, `in_net`, `in_va_size` | **none beyond the parser.** `trace.ml:775-790`: `h_alloc_limit`, `h_entry_sp`, `h_initial_brk`, `h_mmap_base`, `h_effective_mmap_base`, `h_nofile`, `h_entry_sigmask` and `h_hwcap` all use `as_word`; each `load_segments` pair uses `as_range = as_pair as_word as_word`. `h_uid`, `h_gid` and `h_groups` use `as_nonneg`, which refuses only a negative OCaml int. |
| 5 | `main.ml:3934-3955`, the live driver | `M.init_model` | `elf_load_reservations binary`, `image.start_brk`, `vvar_start_of_image`, `image.sp`, `alloc_limit_z`, `uid`, `gid`, `rlimit_nofile_cur`, `sig_blk`, `hwcap = 0x112D` | **partial.** `alloc_limit_z` (`:3498-3501`) is checked `n >= 0` only; `entry_sigmask` (`:3834-3842`) only that it blocks neither SIGKILL nor SIGSTOP; `mmap_base` goes through `assert_mmap_base_in_band` (`:3791`). `sp`, `start_brk`, `rlimit_nofile_cur` and `sig_blk` are guest values of unmeasured range. |
| 6 | the mutation operators, `main.ml:713-770` and `:830-845` | edit the raw records before row 1 | `eff_ret`, `in_args`, `eff_writes` addresses | **none, and worse.** `parse_value` (`:555`) maps the literal `2^64` to `two64` unreduced; `SetRet v` and `SetArg (i, v)` install `v` unchanged; `ShiftWrites` and `SmuggleUnmap` add with `Big_int_Z.add_big_int` and **no `wrap64`**, so a write address can leave `[0, 2^64)`. `wrap64` (`:457`) is applied only to `AddRet`, `resolve ad` and numeric literals. |
| 7 | `FinInput.lean:157`, `Examples/*.lean`, `Checks/*.lean`, `Cases/*.lean`, `FinInput.v:498` | Lean `ProcInput.mkProcInput` / `mkProcInput_full`, Rocq `mkProcInput_full` | fixture literals | not callers of the extracted code: the values are typed `word` (`Z_to_bv 64 …`), so each carries its own bound. |

**Two things that look like checks and are not.** `trace.ml:269-279` is a
comment, and it argues the opposite of a bound. `main.ml:133-135` says
`put_u64` takes non-negative OCaml ints, which is a statement about the
encoder, not a check on anything the model receives.

**Can a caller pass an out-of-range value?** Yes, three ways, all at
`ff0313ba`: a recorded trace whose `ret`, an arg, `sysno` or a write address is
a decimal at or above 2^64 — and the corpus holds one, section 2; a `--mutate`
spec such as `ret=2^64`; and a trace header whose `entry_sp`, `alloc_limit`,
`nofile`, `sigmask` or `hwcap` is at or above 2^64, which reaches `init_model`
unchecked.

**So "every caller stayed in type by a hand-written habit" is contradicted for
that repository at that commit.** Whether a later commit adopted
`CheckedInput` cannot be answered from what was read here, and a caller written
against `d4d2d93e` could not compile unchanged in any case: the `ProcInput`
literals of rows 4 and 5 name neither `in_kernel` nor `in_execfn`, both of
which `d4d2d93e`'s `State.v` has and `ff0313ba`'s has not.

## 4. What the revision can say

The stream owner decided all three of these on 2026-10-31, on this report's
first finding:

**The refusal is right and the boundary does not change.** No kernel produces
that answer; the record is a deliberate mutation; a value outside the Rocq
type must not reach a verdict. A refusal is strictly safer than a verdict, and
"not a machine observation" is a truer description of a forged return than "a
machine observation whose right verdict is reject". What changes is the story,
not the boundary.

**So the sentence to publish is this one, and not "the corpus passes the
boundary":** the recorded corpus holds exactly one record the checked entry
point refuses, it is the record the boundary exists for, and the refusal is not
a verdict.

**And the claim about the callers goes.** "Every caller was read in full, and
each stayed in type by a hand-written habit that nothing checked" is false.
There is no habit: the reader that builds the checker's inputs accepts any
non-negative decimal by design and says so in its own comment, the mutation
path installs the literal `2^64` unchanged, two mutators add addresses without
wrapping, and the replay path seeds `init_model` from eight header words
through the same unbounded reader. The callers are held in type by nothing, and
one recorded record exercises it.

### What this does and does not reach

**Does reach.** One record of 23,984, `set_tid/022.jsonl` record 1, carried a
value outside the Rocq type. Its recorded verdict is `reject`, and that verdict
was computed on an input no theorem of this model covers: the `word` the
extracted checker received was zarith's arbitrary-precision integer 2^64, which
inhabits no `bv 64`, so every statement the checker's verification rests on is
silent about that call.

**Does not reach.** That record is in theorem-labs/linux-process-semantics's
own test corpus. Nothing we publish is read against it: no OSS Verify
statement, no proof and no release artifact of this stream takes a verdict from
that trace. **So no published result of ours is void.** What is no longer
supported is the general claim that none could be — a reader that accepts an
out-of-range value exists, it is used, and the only thing that stopped a
published result from resting on one is that no published result goes through
that reader. One instance exists, it is named above, and it reaches nothing we
publish.

### For the other repository's maintainers

Routed to them through the Lean comparison lane (Envoy session
`01a175f1-a3bf-71f2-a9b8-4f18af2e8f51`, message
`ba1c53cfa2f91c5eaec6b8b595cd5ec2`), not sent from here.

`tests/set_tid.c:64`'s case — `reject --mutate set_tid_address#2:ret=2^64 --
two` — **cannot run against a checker with a typed boundary**, because it asks
for a verdict on a value that has no type. If they want to keep the case, it
should assert a **refusal** rather than a rejection. That is their call, and it
is worth knowing before they meet it.


## 5. The run: the corpus through the checked entry point

```
traces                                             4291
traces with no BOUNDARY line (the walk never ran)     0
records through the boundary's converters         19070
  REFUSED (CheckedRefused)                            1
records also through check_syscall_for_run_checked 17921
  its answer agreeing with the raw call           17918
  its answer DISAGREEING                              0

  refused: set_tid/022.jsonl record 2 set_tid_address ret=18446744073709551616
```

**One refusal, and it is the record section 2 names by reading.** Nothing else
in the corpus is outside the Rocq type, and on every record the boundary did
admit and the checker was re-run over, the checked answer is the raw answer:
**zero disagreements**.

| | |
| --- | --- |
| model | `d4d2d93e776c445bcbc44387bd3a0eaa04cee543`, `git archive --prefix=head/`, sha256 `f6c9aea55090bb0032582aa681266f4bad2b38f8644ba2e03e3cfdd8c558ebd0`, its own `_build` |
| corpus | theorem-labs/linux-process-semantics at `ff0313ba4f2e9baffcf5b5f50bc9d31628ae8556`, working tree clean |
| machine | GCE VM `ossv-lpsev-replay`, n2-highmem-32, us-central1-a |
| image, build and extract | `rc2-checker:1b59b23d`, `sha256:e9fa8b19d7cbab6127dfa522f9b9a02ad8c086febd809e58510ad96e78e24e14` |
| image, link | `ocaml/opam:debian-12-ocaml-5.3` |
| harness | the Lean comparison lane's `slice-D-data`, with `boundary-probe2.sh` added |
| run | `LPS_REPLAY_IGNORE_POST_STATE=1 python3 boundary-run.py --root . --exe <main.exe> --out <json> -j 16`, one pass, 4,291 traces |

19,070 of the corpus's 23,984 syscall records reach the boundary: `--replay`
stops a trace at its first unreproduced verdict, so the records after one are
never judged, by the raw path or by this one.

### What the probe does, and the one thing it does not

The probe sits beside the raw call in the `--replay` walk, on the same model
and the same recorded values, so the replay's own verdicts are unchanged. For
every record it builds a `CheckedInput.RawInput` out of the recorded `sysno`,
`args`, captured runs and writable ranges, and a `RawEffect` through the
model's own `raw_of_effect`, and asks the boundary.

**It asks the boundary's converters on every record and the whole checked
entry point on 17,921 of them, and the reason for the split is a measurement
worth keeping.** `CheckedInput.mem_view` is

```coq
Definition mem_view (runs : list (word * list byte)) : word -> option byte :=
  fun a => bvmap_get a (mem_of_runs runs).
```

`mem_of_runs runs` sits **inside** the lambda, so the extracted OCaml rebuilds
the whole byte map on **every byte the checker reads**. The raw harness hands
in a `Hashtbl` lookup instead. A first run that called
`check_syscall_for_run_checked` on every record was stopped after 50 minutes
with single traces at 38 minutes of CPU each, where the same corpus through
the raw path takes **21 seconds**. So the second probe calls the whole checked
entry point on every record whose captured memory is at most 256 bytes —
17,921 of 19,070 — and the boundary's own converters, `input_of_raw` and
`effect_of_raw`, on all of them.

**That is the same question, through the same code.** The refusal is decided
before the checker runs:

```coq
check_syscall_for_run_checked ri re m =
  match input_of_raw ri, effect_of_raw re with
  | Some i, Some e => CheckedAnswer (check_syscall_for_run i e m)
  | _, _ => CheckedRefused
  end
```

so a record on which either converter answers `None` is exactly a record the
entry point refuses. Both converters are published in the generated interface,
as `Extraction.v` says every name the roots reach is.

**The quadratic read is a finding of its own, and it is not about this
corpus.** `Checks/Extraction.v` offers `check_syscall_for_run_checked` as the
supported surface and says a caller "must" use it. A caller that does, with a
realistic capture, pays O(captured bytes) per byte read. Nothing in the file
says so, nothing measures it, and the only reader that would notice is one who
tried — this one. It is worth a line in `CheckedInput.v` at least, and a
`mem_of_runs` lifted out of the lambda at best; neither is this report's to
make.

