# The checked entry point is quadratic in captured memory

**The supported surface is too slow to run routinely, and the cause is one
`let`.** `Checks/Extraction.v` tells a reader that
`CheckedInput.check_syscall_for_run_checked` is what this tree supports and
what a reader must use. Replaying the recorded corpus through it was stopped
after 50 minutes with single traces at **38 minutes of processor time each**,
where the same corpus through the raw entry point takes **21 seconds**.

That is not a curiosity. A boundary nobody can afford to run is a boundary
that stops being run, and this one is the thing standing between the verified
checker and a value no theorem covers.

**A cheap fix is visible and measured.** `mem_of_runs runs` sits inside
`mem_view`'s lambda and is rebuilt on every byte the checker reads; lifting it
into a `let` is a definitional change that alters no proposition and no proof.
With it the whole corpus goes through the whole checked entry point in
**65 seconds** — 19,070 records against the 17,921 the bounded run could
manage, the same single refusal, zero disagreements.
[Section 3](#3-the-fix-and-what-it-measures) has the run. **It is a branch
worth having, and the fix widens the evidence as well as the speed.**

## 1. What was measured

| | |
| --- | --- |
| model | `d4d2d93e776c445bcbc44387bd3a0eaa04cee543`, `git archive` export, its own `_build` |
| corpus | theorem-labs/linux-process-semantics at `ff0313ba4f2e9baffcf5b5f50bc9d31628ae8556`, 4,291 traces, working tree clean |
| machine | a GCE build machine, n2-highmem-32, us-central1-a, 16 replay workers |
| images | `rc2-checker:1b59b23d` (`sha256:e9fa8b19d7cbab6127dfa522f9b9a02ad8c086febd809e58510ad96e78e24e14`) to build and extract; `ocaml/opam:debian-12-ocaml-5.3` to link |

Three runs of the same corpus through the same linked harness, differing only
in which entry point each record goes through:

| run | what each record does | wall time |
| --- | --- | --- |
| the raw path alone | `ExecutableSpecs.check_syscall_for_run`, the harness as it ships | **21 s** |
| the raw path **plus** `check_syscall_for_run_checked` on **every** record | the whole checked boundary | **stopped after 50 min**; 16 worker processes each at 2,288 s of CPU at 99.9 %, no trace finished |
| the raw path plus the boundary's converters on every record, and `check_syscall_for_run_checked` on the 17,921 records whose captured memory is at most 256 bytes | the boundary, bounded | **about 1 min**, 4,291 of 4,291 traces |

The third run is the one `reports/evidence-checked-entry.md` reports: one
refusal, zero disagreements. **It had to be bounded to finish at all**, and
that bound is this report's subject.

## 2. The cause, read in the source

`theories/LinuxProcessSem/Checks/CheckedInput.v`:

```coq
Fixpoint mem_of_runs (runs : list (word * list byte)) : bvmap 64 byte :=
  match runs with
  | [] => bvmap_empty
  | (base, bs) :: r => mem_insert_bytes base bs (mem_of_runs r)
  end.

Definition mem_view (runs : list (word * list byte)) : word -> option byte :=
  fun a => bvmap_get a (mem_of_runs runs).
```

`mem_of_runs runs` is **inside the lambda**. Extraction produces OCaml of the
same shape, so every application of the view rebuilds the whole radix map:
one `bvmap_set` per captured byte, each costing the width of the address. A
record whose capture is *b* bytes and whose checking reads *r* of them costs
`O(b · r · 64)` rather than `O((b + r) · 64)`.

The raw path has no such cost: the harness hands `init_model`'s input a
`Hashtbl.find_opt` closure over a table it builds once per record.

**And the file says the opposite, in a comment immediately above:**

> this builds the model's `[word -> option byte]` from them, through the
> radix map of `[Riscv.Prelude]` so a lookup costs the width of the address
> and not the length of the run.

That sentence is true of `bvmap_get` and false of `mem_view` as written. It is
the same shape as every other defect this revision has collected — a property
asserted in prose that the code's own structure defeats, with nothing checking
it — and it is why the boundary's cost had never been noticed: the comment
answers the question, so nobody measured it.

**Three traces of the corpus make it concrete.** The capture of a record is
whatever the tracer read: a `pathname` is tens of bytes, an `iovec` payload or
an `fstat` buffer is hundreds, and a `write` of a page is 4,096. Three
processes were still inside their first trace after 38 minutes, so the records
that bite are the ones with the largest captures — exactly the records a
memory-safety checker exists to look at.

## 3. The fix, and what it measures

```coq
Definition mem_view (runs : list (word * list byte)) : word -> option byte :=
  let m := mem_of_runs runs in fun a => bvmap_get a m.
```

**It changes no proposition.** A `let` is definitional, so `mem_view runs` and
the old body are convertible: every lemma in the file about `mem_view` —
`mem_view_sound`'s family, and `checked_answer_is_the_checker` above them —
closes by the same proof. Extraction turns it into
`let m = mem_of_runs runs in fun a -> bvmap_get a m`, which builds the map once
per `input_of_raw`, that is once per record, which is what the raw path's
`Hashtbl` already costs.

The same `let` belongs on `wmem_view`'s neighbour only if it has the same
shape; it does not — `wmem_view p = fun a => if p (bv_unsigned a) then …` holds
no structure to build — so this is one line in one definition.

**Measured.** The variant above was built from a copy of the `d4d2d93e`
export, extracted and linked the same way, and the corpus replayed with the
probe's size threshold removed — every record through
`check_syscall_for_run_checked`, which is the run that could not finish before:

```
traces                                             4291
traces with no BOUNDARY line (the walk never ran)     0
records through the boundary's converters         19070
  REFUSED (CheckedRefused)                            1
records also through check_syscall_for_run_checked 19070
  its answer agreeing with the raw call           19067
  its answer DISAGREEING                              0

  refused: set_tid/022.jsonl record 2 set_tid_address ret=18446744073709551616

Elapsed (wall clock) time:  1:05.20
User time (seconds):        197.89
System time (seconds):      21.13
Maximum resident set size:  648,760 kB
```

**Every one of the 19,070 records now goes through
`check_syscall_for_run_checked`, and the whole corpus takes 65 seconds.** The
same run on the unfixed boundary was stopped after 50 minutes without
finishing a single trace in three of its sixteen workers. The answers are
unchanged: the same one refusal, the same record, and zero disagreements with
the raw call over 19,067 admitted records — against 17,918 before, because the
bounded run could only re-check the records with small captures. **So the fix
both makes the boundary runnable and widens the evidence for it.**

Measured on the build machine, from a copy of the `d4d2d93e` export with
that one definition changed and nothing else, its own `_build`, extracted and
linked through the same two images, 16 replay workers. Logs:
`~/replay-E/memview-fix.txt`, `~/replay-E/headfix-build.log`,
`~/replay-E/memview-fix.json`.

## 4. What this means for the boundary

**It is not a correctness finding.** The checked entry point gives the right
answer; `reports/evidence-checked-entry.md` measures it agreeing with the raw
call on 17,918 of 17,918 records and refusing exactly the one record outside
the Rocq type.

**It is a finding about whether the boundary can be used.** Two things follow.

- **Nobody should put the checked path in a gate on today's `mem_view`.** A
  conformance run that takes seconds through the raw entry point does not
  terminate in any useful time through the checked one, and a gate that cannot
  run is a gate that gets removed.
- **The harness's follow-up in `reports/corpus-replay.md` section 6a — that
  the replay harness should build a `RawProcInput` and call
  `init_model_checked` — costs nothing by itself, but the same change on the
  per-record path does.** If that follow-up is taken, this `let` goes first.

Whoever owns `CheckedInput.v` makes the change; this report does not, because
that file is outside `reports/`.
