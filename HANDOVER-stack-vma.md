# Handover: the stack VMA change (`revision/stack-vma`)

Written 2026-11-02 by session StackVma3 (Omp-Session
01a18fe5-2088-7566-a8eb-ea299455799e), for LeanLead (session
01a175f1-a3bf-71f2-a9b8-4f18af2e8f51). Delete this file before the
pull request leaves draft.

- Pull request: theorem-labs/rocq-linux-process-semantics#76, draft, base
  `revision/all-fixes`. It merges in the update AFTER the current revision.
  Do not retarget it at #38.
- Phase 1 report and lists: `/mnt/nvme/sami/scratch/lpsrev/stackvma/`
  (`lemmas-detail.txt`, `main-idents.txt`).
- Scratch for this phase, including the farm scripts:
  `/mnt/nvme/sami/scratch/lpsrev/stackvma3/`.

## The approved design

- The stack is one more entry of `vm_reserved`: `State.stack_reserved`,
  `[Run.stack_window_lo, ed_top)`, the bytes `Run.init_machine_state` maps.
  `State.init_reserved` adds it between the image's reservations and the
  vDSO pair. No record field changes.
- `State.stack_guard_band`: `stack_guard_gap_bytes kb` below that entry. It
  is in the lists the hint, both search windows (so the `mremap` move
  target) and `brk` read. It is NOT in `vm_reserved`, because MAP_FIXED and
  `vma_expandable` (in-place `mremap`) keep no gap. The band finds the
  stack as the reserved entry that holds `vm_init_sp`, and stops at the
  mmap base.
- The hint and the bottom-up fallback reach `TASK_SIZE`. The top-down
  window is `Z.min (mmap_top h) TASK_SIZE`.
- `linux_place`, `linux_place_b`, `topdown_search` take
  `kb : KernelBuild` instead of `thp : bool`.

## The owner's four decisions

1. Full-size stack approved. D3's original hinted `mmap` is pinned as the
   new disclosed residual R-e, in the same commit as the SCOPE row.
2. NARROWED (Main, after the corpus measurement): the MAP_FIXED and
   MAP_FIXED_NOREPLACE gates KEEP `alloc_top`. SCOPE discloses it as a
   refusal, not a wrong answer. The `brk`, `munmap` and three `mremap`
   gates use `TASK_SIZE`. `mmap_top` keeps `alloc_top` (R-a unchanged).
3. `init_model` takes a new positional argument `top` (the stack VMA's
   end, `ed_top`), after `sp`. `init_reserved` takes it after `sp` too.
4. This is its own update, after the revision merges.

## The guard gap

- `State.stack_guard_gap_bytes_bounds` is UNCHANGED (the 0x4aba6a2ab000
  bound, about 82 TiB). Tightening it was tried and reverted on Main's
  instruction: it would narrow the kernels the published statements cover.
- The ASan plan layer needs the band above `AsanCeil.alloc_ceiling`. That
  is the new `cs_ok` field `co_band` (`AsanCeil.stack_band_ok`),
  established once in `AsanInit.stack_band_ok_init`, where the kernel is
  `default_kernel` (256 pages), so the guard fact is discharged by
  computation (`stk_facts`). No ASan statement gets a hypothesis.
- `co_res` lists the stack entry as its own clause
  (`image ++ stack ++ rx`), so no per-image atable changes.
- `co_totsz` sums the ledger WITHOUT the entries holding `vm_init_sp`.
  `AsanPlacement.free_gap_of_totals` takes `stack_band_ok` as a premise and
  USES it to show the certified gap misses the stack and its band.
- Every node rebuild carries `co_band` with `stack_band_ok_same` from the
  `*_res`, `*_isp`, `*_mbase` and `*_kernel` fields of the step records.
  Every site was a carry; none needed a re-derivation.

## What is built

- Commit e740e7a (the change on top of 8e81ddb, before the merge): full
  `dune build` (`@default`) on the farm, Rocq 9.2: exit 0. On the same commit:
  `Print Assumptions linux_place_unique` and `linux_place_exists`: "Closed
  under the global context", the same as on 8e81ddb.
  `.github/check_assumptions.py`: exit 0.
- Commit 9931cc4 (WIP merge of `revision/all-fixes` d8f30e8, #61 vDSO
  pages): NOT built yet. The farm build of the merge before its last fixes
  (farm/20261102t055735z-b98806) failed in four files:
  `Checks/Cases/Kernel/Vdso.v` (a fixture `init_model` without `top`; fixed
  with `fx_ed_top`), `Common/MmapSim.v` and
  `Examples/patchclassify_demo/Verdicts.v` (named-argument applications of
  lemmas whose arity grew; fixed), `Checks/Cases/Mm/StackVma.v` (the new
  `seg_kind` field; fixed). The farm build of 9931cc4 itself is the job
  farm/20261102t062736z-6964d5 (tag w13; log via
  `farm-log.sh 20261102t062736z-6964d5 w13`). Expect more errors downstream of those four
  files, which did not compile in the earlier run.
- Merge notes: #61 added `co_vdso` to `cs_ok`; the order is
  `... co_mres; co_vdso; co_band`, and destruct patterns end
  `Xmres Xvdso Xband`. #61's `gp_kernel`, `sp_kernel`, `dp_kernel` are kept.
  The merge was made by hand-resolving conflicts
  (`resolve_conflicts.py`, `codemod_init2.py` in the scratch folder).

## How to build (never locally)

`/mnt/nvme/sami/scratch/lpsrev/stackvma3/farm-build-v.sh TAG @default`
bundles the worktree as `farm-TAG` and runs a timestamped `dune build` on
the farm. `farm-log.sh RUN-ID TAG` fetches the log. `pa-after.sh TAG REF`
runs the full build, `Print Assumptions` on the two lemmas and
`check_assumptions.py`. Rule from the earlier hang: no bare `lia` with
`_ mod _ = 0` hypotheses in context (`Checks.Placement.plia`,
`AsanInit.nlia`).

## The five cases (`Checks/Cases/Mm/StackVma.v`, built at e740e7a)

All on launches `Run.valid_entry` accepts (D3's start state, Qed).

| Case | Verdict |
|---|---|
| D3: MAP_FIXED_NOREPLACE map at 0x7fffff7fd000, then in-place `mremap` grow to the stack's floor | `OOk` (was `OReject`) |
| D3 control: the same two pages lower | `OOk` |
| R-e residual: D3's original hinted `mmap` at 0x7fffff7fd000 | `OReject`, with the note that it flips if fault-driven stack growth is added |
| R-b closed: hint in the page below STACK_TOP, on a launch whose stack ends at STACK_TOP - 4096 | honoured |
| R-c closed: hint at the band's lowest page | refused; one page lower honoured |

## Re-proof count so far (e740e7a against 8e81ddb)

Phase 1 estimated 149 statement changes, 42 proof-only and 203 mechanical.
Counted by script over the changed `.v` files
(`/mnt/nvme/sami/scratch/lpsrev/stackvma3/reproof-count.txt`):

- 101 lemmas with a changed statement beyond the new argument,
- 231 whose only change is the new `init_model` argument,
- 44 with a changed proof only,
- 38 new, 7 removed.

The merge adds #61's new lemmas that name `init_model` or the changed
symbols; not yet counted.

## Still to do

1. Get 9931cc4 (and fixes) green on the farm, then all six CI checks on
   #76 (Route, Build on Rocq 9.2/9.3/dev, opam install, CI).
2. #75 (SIGPIPE repair: `in_sigpipe_terminal` as the 20th `ProcInput`
   field) lands before this branch: MERGE it in, do not rebase.
3. The curl-decide top-down window lemma (`topdown_place_above_cover`,
   `family_place_in_window` and a single-size corollary) is coming to
   `revision/all-fixes`. When it lands, merge, re-prove it against the new
   `linux_place` (takes `kb`), `topdown_search` (window top
   `Z.min (mmap_top h) TASK_SIZE`, the band in front of the ledger), and
   show — do not assume — that the band falls outside its window through
   its `fst p < mmap_top h` premise (`State.stack_guard_band_above_base`
   gives band entries at or above the mmap base, and `mmap_top h` is at
   most the base). Count it in the re-proof list.
4. Re-run `Print Assumptions` on the two lemmas on the final head.
5. Delete this file; take #76 out of draft only when the owner says.

## The port (next update, not this branch)

49 targets in 19 projects of `theorem-labs/oss-verify-proofs-internal`
(`origin/main` 03b046de) vendor their own `AsanInit.v` / `AsanPlanSound.v`
at the old model pin; they publish 258 statements, 169 of them `asan_*`.
Each vendored copy gets the `co_res` / `co_totsz` / `co_band` change at port
time: mechanical, and no statement changes. The list is in the pull request
body and in `/mnt/nvme/sami/scratch/lpsrev/stackvma3/port-targets.md`.
