# Backing the vDSO pages: what is done, what is left, and the five shapes

This branch, `revision/vdso-back-the-pages`, gives the model the Linux vDSO's
two areas as ordinary segments carrying **measured bytes**, so that the
address the auxiliary vector has always published under `AT_SYSINFO_EHDR`
finally has something behind it. The image data and the segment plumbing come
from `revision/vdso` at `1a1828e`; this branch is cut from the revision head
`5aa37523` and merges that work into it.

Read this file before you touch anything. It exists because the remaining work
is **mechanical and bounded**, and because the one thing most likely to mislead
you is reaching for the wrong lever.

## What was wrong, in one paragraph

Every launch published an auxiliary vector whose first entry was
`(AT_SYSINFO_EHDR, mmap_base - vdso_text_pages * 4096)`, unconditionally and
never equal to the base — and nothing in the model mapped a byte of the vDSO.
`State.vdso_reserved` recorded the vvar pages and the text as (address,
length) RESERVATIONS with no backing, and no step dispatched a vDSO call. A
program that followed the published address read an ELF header that was not
there: the load missed every mapping and was a `RiscvSemantics.MachineFault`,
the model's SIGSEGV analogue, for a program that runs on Linux. A plain run
that seeds a hash table hit it inside the C library's clock initialisation, on
its first `clock_gettime`. **This branch makes the two halves agree**: the
publication stays and the bytes arrive.

The alternative — withdrawing the publication — was written, measured and
**refused**. It is on `revision/vdso-publish`, tip
`6b6b344cf7ad9e0eaef2b19887c1c862fc8a7d91`, which must not merge: it makes
twenty lemmas FALSE in the ten `tests/StartState*.v` files generated from
recorded real Linux v6.18.46 launches, whose vectors all carry 29 entries with
the vDSO pair first. `launch_ok` stays true at all ten; `block_ok` and
`auxv_ok` do not. That measurement is why this branch exists.

## THE CALL STEP IS NOT THE COST OF ANY OF THIS

Twenty-five files of the simulation library need repair on this branch. The
first thing a reader does with that number is reach for `Run.sstep`'s three
vDSO arms — `sstep_vdso_call`, `sstep_vdso_materialization_fault`,
`sstep_vdso_unmodeled` — and the `State.with_vdso` wrapper, and propose
removing them. **Do not.** Three independent readings settled it:

- `Run.v` compiles with the arms present; they were never the frontier.
- The arms each require `mi_account_step … = MachineUnmodeled`, and the one
  `sstep` inversion in the files that broke removes them with its existing
  `discriminate` against a `MachineOk` step.
- `with_vdso` rebuilds only the VM subsystem and keeps `m_fd` and `m_proc`
  (`State.v`), so it is transparent by conversion wherever it appears.

Removing them would fix nothing and would cost a second merge. The breakage is
the segment list growing a tail and the initial model growing a wrapper —
nothing more.

## The five shapes

Twenty of the twenty-five files are green, and **each green file is a worked
example of one of these**. When a build names a file, decide which shape the
error is and copy the named example.

### Shape 1 — a run-level statement must name the run's segment list

A lemma whose conclusion is `omni_run`, `omni_corun`, `omni_cosafe`,
`omni_strong_equiv`, `Equivalence.modeled` or `Equivalence.equiv` of
`(mkImage segs pc ph)` now unfolds to `Run.run_segments segs inp sp mb`, which
is `segs ++ vdso_segments (in_kernel inp) sp mb`. Its `to_*` and
`init_machine_state` hypotheses must be over that list, and its model
hypothesis under the wrapper.

Finished: `Common/AllocSim.v` (`alloc_omni_run`, `alloc_obs_iff`,
`alloc_no_error_run`, and both pair lemmas — the whole block in one pass),
`Common/CatSim.v` (`cat_omni_run_te` and the three `cat_kill_*`),
`Common/WallSim.v`, `Common/FileSim.v`, `Common/ErrEscape.v` (its seven
run-level escape lemmas).

### Shape 2 — a statement over `init_config segs …` keeps its segments

`Run.init_config` now wraps the model in
`State.with_vdso (Vdso.vdso_run_init (ed_vdso rnd))`. A lemma stated directly
over `init_config segs …` therefore keeps `segs`; only the model gains the
wrapper, in the statement and in each `assert` that reads a field of it.

Finished: `Common/AllocSim.v` `alloc_obs_iff`, `Common/MmapSim.v`
`mmap_obs_iff_te`, `Common/AllocMixSim.v` `alloc_mix_obs_iff`.

### Shape 3 — a Section with one segment list cannot conclude an `omni_*`

`omni_corun` reads `run_segments` of the image's segments, while these
sections are parameterised by a single `segs`. Restate the lemma at
`OmniRun.coexec segs (init_config segs …)` / `OmniRun.cosafe segs
(init_config segs …)`, and let the callers outside the section instantiate
`segs` at `run_segments source_segs inp rsp rmb` — which is exactly what
`omni_corun` unfolds to.

Finished: `Common/StreamSim.v` (`stream_omni_corun`, `stream_omni_cosafe` and
both pair lemmas), `Common/DrainSim.v` (the same four).

### Shape 4 — an `sstep` inversion must cover the three vDSO arms

A proof that inverted `sstep` and closed the leftovers with `try congruence`
plus a `match` on `mi_account_step … = MachineOk _` now leaves the vDSO arms
open. They carry `MachineUnmodeled`, so they close the same way: widen the
`match` to `mi_account_step … = _` and chain it after the `try congruence`.

Finished: `Common/ErrEscape.v` (`illegal_exec`, `illegal_all_traces_error`,
`fault_no_unmodeled`), `Common/AllocMixSim.v` (`illegal_no_snext`).

### Shape 5 — `unmodeled_at` has THREE disjuncts

The vDSO split made the first shape two: pc is not an exported entry, or it is
and the call is uncovered. A two-branch destructuring fails with *Expects a
disjunctive pattern with 2 branches*; the pattern is
`(_ & [(_ & Hum & _) | [(_ & Hum & _) | (x8 & Hsvc & _)]])`, and the new middle
case closes exactly as the first.

Finished: `Common/ErrEscape.v` (`fault_covered_at`, `instr_no_unmodeled`),
`Common/AllocMixSim.v`, `Checks/ErrorFreeInput.v`, `Checks/SpuriousCfg.v`,
`Checks/GatedSize.v`, `Checks/HaltsAllowed.v`, `Common/SrcShape.v`.

### Two internal lemmas take the vDSO's own rule as a premise

Not a shape, but the same cause, and each is the vDSO's rule rather than a
weakening. **No published statement gains a premise anywhere on this branch.**

- `Common/ErrEscape.v` `step_lbu_fault` and `step_ld_fault` gain
  `range_meets_vvar segs addr n = false`. Without it they are FALSE at any
  segment list carrying the pair: the four vvar pages are readable on Linux
  and the model has no term for their contents, so a load that meets them is
  `MachineUnmodeled` — the model declining — and not a fault.
- `Checks/Examples.v` `unmodeled_no_next` gains
  `vdso_entry_fn segs (ms_pc ms) = None`. Without it it is FALSE: the vDSO
  arms fire at `MachineUnmodeled`, which is the point of them, so a
  configuration the decoder declines can still step when its pc is an
  exported entry.

## The one design step, approved

**`cs_ok` gains a last field, `co_vdso`:**

```
incl (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model)))
     (vm_reserved (m_vmmaps model))
```

**Why it exists** — say this in its text, or the next reader takes it for
bookkeeping. `Sys/Mm/Mprotect.check_mprotect` now answers `CheckUnmodeled`
when the range meets the vDSO pair. `Common/RefNodes.mprotect_check` and
`Common/AsanNodesMmLib.srz_mprotect2` take "the range is `region_free` of that
pair" as a premise, and their caller `AsanNodesMmA.node_mprotect_sound2` cannot
supply it: the ASan state invariant says only
`vm_reserved = segments_reserved SEGS ++ rx` for some `rx`, and nothing ties
`rx` to the vDSO pair or mentions `m_kernel` at all. `co_vdso` is what lets the
soundness lemma see the new branch; the caller then gets the premise from
`slice_args`, which already gives `region_free (vm_reserved …) addr n`. It is
true of every state the model reaches — `State.init_reserved` appends exactly
that pair — so it constrains nothing real.

**Approved by the OSS Verify stream lead** (this session, 2026-11-01), on the
reading that `cs_ok` is the ASan checker's own state invariant and no published
statement moves.

**The ten sites**: the two proofs in `AsanInit` (from `vm_reserved_init_model`
and `m_kernel_init_model`); `AsanPlanSound.cs_ok_frame` and the second frame
lemma near line 1505, **each needing an `m_kernel model' = m_kernel model`
fact** — the `State.m_kernel_with_*` lemmas carry `Hint Rewrite … : model`, so
`autorewrite with model` should discharge them; `AsanNodesMmB` near 745 and
1549; `AsanNodesMmLib` near 2033, 3226 and 3757; `AsanPlanSoundSums` near 778.

## The reduction trap — read this before you raise a memory cap

A fixture that computes over a segment list whose tail is the **measured vDSO
image** does not finish. It is a reduction problem, not a size problem, and
**raising the cap does not help.**

`Checks/Cases/EntryWitness.v`'s high block is the worked case. Its last
instruction is `ld t1, 0(zero)`, a load from address 0 that misses the stack
image and misses the image's own segment, so it falls through to the tail —
once in `memory_read` and eight more times in `range_meets_vvar`'s per-byte
`vvar_byte_at`. Over an **abstract** tail those nine `find_segment` queries are
stuck matches, and every reduction strategy normalises BOTH branches of each.
One worker reached **164 GB** and never finished.

Two fixes, both in the tree:

- **Concrete tail with a local transparency.** `EntryWitness.v` now defines its
  high tail as `vdso_segments (in_kernel witness_input) witness_sp
  witness_mbase` and says `Local Transparent vdso_segments.` — `Run.v` seals it
  `Global Opaque` so that nobody else's `vm_compute` forces the image. Over the
  concrete pair each query fails on the bases, no image byte is decoded, and the
  step reduces to the constant `MachineFault`.
- **Abstract the memory first.** `Checks/Omni.v`'s own
  `undecodable_step_unmodeled_here` does this: `rewrite (with_mem_eta …)`,
  `generalize (ms_mem …)`, then `vm_compute`.

`Checks/Omni.v` was OOM-killed at a 48 GB cap on this branch and needs one of
those two before it can even report a real error.

And the matching reading rule, which cost a lane an hour tonight: **an
OOM-killed `rocq` leaves no `.vo` and no `exit 1`.** Grep a build log for
`\(exit [0-9]+\)|signal`, never `\(exit 1\)`, and on any slow or silent build
read `sudo dmesg -T | grep -iE 'out of memory|killed process'` before you read
the error list at all. A file that was killed and a file that was never
scheduled look identical in an error list.

## How to build this branch

On a machine with the acceptance image, under a memory cap, never on
`sami-rocqperf`:

```
docker run --rm -u 0:0 --memory=48g --memory-swap=48g -v <work>:/work -w /work/lps \
  rc2-checker:1b59b23d bash -lc '
    export PATH=/home/opam/.opam/4.14/bin:$PATH OPAMROOT=/home/opam/.opam HOME=/work/lps/.home
    mkdir -p "$HOME"; rm -rf $(opam var lib)/*/user-contrib/LinuxProcessSemantics
    dune build --display short -j 16'
```

Remove the installed `LinuxProcessSemantics` **in the same container and as
root**, or the removal is discarded with the container, and print the control:
how many copies remain and how many other libraries do.

The five CI commands are `dune build --display short`,
`python3 tools/gen_checker.py --check`, `--verify`,
`python3 .github/check_assumptions.py`, `python3 tools/test_elf_snapshot.py`.

## Two rules this branch earned

**After resolving a merge, diff the result against the head on exactly the
conflicted files and account for every line of the head's own change that is
missing.** `Common/CatSim.v` had four conflicts and all four were taken from
the donor, which silently reverted the head's exit-ready repair: two lemmas
lost a `wexit_launch` premise and one assertion went back to a stale form. A
merge that reverts a landed fix **can still compile**; this one happened not
to.

**And look for what is MISSING, not only for what is broken.** Three
`cat_kill_*` lemmas landed on the head after the donor branched, so the donor
never saw them and they were still stated over the image's own segments. No
conflict marked them.
