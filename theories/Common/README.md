# Common: the proof library

This directory is the Rocq theory `LinuxProcessSemantics.Common` (opam
package `rocq-linux-process-semantics-core`, the package that also installs
the model). It helps you prove the statements of
`theories/EquivalenceDefinition/` about RISC-V binaries. No file in it
depends on a specific binary.

Read this document to find the part of the library that you need. For the
steps to write a full proof, read
[`../Examples/README.md`](../Examples/README.md).

Import a file as `From LinuxProcessSemantics.Common Require Import <Name>.`
A typical proof starts with:

```coq
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import
  ExitSim PropExec CatExec CatSim SeqExec StepTac.
```

Most files were written by the OSS-Fuzz proof collaborators. Each file
header says so. Every proof in the library ends with `Qed`. The library
adds no axioms. Some theorems have section hypotheses; this document names
the ones that matter.

Files marked *prototype* work and have proofs, but fewer examples use them.

## Choose a behavior file

A proof shows that the binary has one *shape* of observable behavior. Find
the shape of each input case:

| Behavior | File |
| --- | --- |
| exit only, no output | `ExitSim` |
| writes to a channel, then exit | `CatSim` |
| `put`-style write loops on a channel, then exit | `WallSim` |
| read and write loop that may not stop | `StreamSim` (with `StreamExec`) |
| read all of standard input, then write once | `DrainSim` |
| `brk` allocation | `AllocSim` |
| one anonymous `mmap` | `MmapSim` |
| file operations; the result is the exit code and the final files | `FileSim` |
| every source execution crashes | `ErrEscape` |
| any combination of the above | `ShapeAlg` |

Each behavior file defines a relation that describes the reachable
behavior (for example `CatSim.to_wexit`). It then gives a lemma
`*_omni_strong_equiv*`. This lemma proves `OmniEquivalence.omni_strong_equiv`
for two binaries that have the same description. The older form
`*_strong_equiv*` is also available.

Files for less common cases:

- `AllocSim2`: a source that uses `brk` and a target that uses `mmap`.
- `AllocMixSim`, `FileMixSim`: outcome sets with branches that crash.
  `FileMixSim.file_mix_equiv_only` proves `equiv` only, not `modeled`, so
  it cannot prove `strong_universal_T`.
- `ErrEscape2`: a source that crashes after some system calls.
- `DivergeSim`, `LazyFrame`, `NoReserve`, `SpinAlg`: a branch that loops
  forever without output (for example, a sanitizer runtime after an
  allocation failure), and `mmap` with `MAP_NORESERVE`.
- `SrcShape`: a shape for a source that can crash.

## The shape algebra (ShapeAlg)

`ShapeAlg` replaces the separate relations of the behavior files with one
relation.

- A *shape* is a prefix-closed set of traces, `TSet := list event -> Prop`.
  You build it with `t_nil`, `t_emit evs T` (emit `evs`, then continue
  with `T`) and `t_alt` (a choice). `t_writes`, `t_exit` and `t_alt2` are
  derived forms.
- `realizes c T` says that from configuration `c`, the trace set is
  exactly `T` and no execution gets to the error transition.
- At a system call, the proof gives a *node* (`node_ok`): the exact set of
  next configurations and their events. `ShapeNodes` has node rules for
  the common system calls.
- Between system calls, `rz_msteps` takes a chain of machine steps
  (`CatSim.msteps`), as `StepTac` or `SymTac` make them.

The main theorem is `shape_omni_strong_equiv`: if the source and the target
realize the same shape from their initial configurations, the
equivalence statement is true. `ShapeEF.shape_strong_equiv_ef` gives the
error-free statement, and `ShapeEFS` does the same when one side uses
`SpinAlg.srealizes`.

The combinators are introduction rules with the continuation as a
parameter (for example `rz_write1`, `rz_mmap`). Thus you compose blocks by
putting one derivation inside another. `rz_alloc_writes` composes an
allocation with a list of writes.

Limits:

- `realizes` is inductive. Thus it describes runs that stop. For a loop
  that may not stop, use `StreamSim` or `DrainSim`.
- `DrainAlg` gives a read loop with a fixed maximum size (`t_drain`). This
  loop stops on every input, also on infinite input. `t_drain_collapse`
  shows that the block sizes of the reads do not change the trace set.
- A `realizes` derivation has no crash branch. For a source that can
  crash, use `SrcShape` or `ErrEscape`.

## Step through instructions

| File | Contents |
| --- | --- |
| `PropExec` | The base: the state `mkst`, register access `getr`/`regupd`, value forms (`v_addi`, `v_add`, ...), about 70 `step_*` lemmas, and the initial stack. |
| `CatExec` | Memory writes (`wbytes`), the `argv` layout on the stack. |
| `SeqExec` | Calls, returns and branches of compiled C and Zig code. `getr_resolve`, `regupd_resolve`. |
| `StepTac` | The step tactics `stepi`, `stepiv`, `stepj` for all relations, and `norm_pc`, `sp_norm`, `bveq`, `vm_refl_bv`. |
| `ArgvEnv` | The facts about the initial stack that each example needs. Use it two times: once for the source, once for the target. |
| `StoreOk` | Proofs that a store goes to writable memory (`store_ok`). |
| `WxExec` | Steps in a segment that is writable and executable. |
| `FPSteps` | Steps for the F and D instructions. |
| `SimInv` | The general "no error on any path" argument that the behavior files use. |

`mkst` takes an implicit `FPState` argument: the floating-point registers
and `fcsr`. Files that use `mkst` must declare a section variable
`Context {fx : FPState}` or name an instance, for example
`#[local] Instance fx : FPState := fx0.` (`fx0` is the state at process
start).

### Reflective symbolic execution (prototype)

A reflective executor runs a block of instructions inside Rocq with
`vm_compute`, and a soundness theorem turns the result into `msteps`.

- `SymExec` with `SymTac.sym_block`: straight-line blocks with ALU
  instructions, loads, stores and branches. `SymTac.sym_block_ex` gives the
  result as hypotheses, so you can put a block in its own lemma.
  `SymBranch` and `SymSide` close the side conditions.
- `AxSymExec3` (with `AxSymExec3B`, `AxSymExec3Sound`, `AxSymRun3`,
  `SymStepR`): a stronger executor. It keeps facts about memory, handles
  all integer loads and stores, and RV64A atomics. The ASan plan checker
  below uses it.

### Summaries and Hoare logic (prototype)

- `Hoare`: triples over `msteps`, with frame, call and loop rules.
- `MuslCall`: a summary of musl's `write` wrapper, for any load address.
- `MuslStrlen`: musl's word-at-a-time `strlen`.
- `Footprint`: regions of memory, and the proof that two accesses do not
  overlap.

## ASan plan checker

Use this part when you prove that a build with AddressSanitizer (ASan) is
equivalent to the plain build. The ASan runtime runs about 150,000
instructions before `main`, with many `mmap` calls. Do not step through it
by hand.

The method:

1. Write a *plan* (`AP.plan`, in `AsanPlan.v`). A plan says what to do at
   each point: run the executor to the next stop (`PRun`), take a system
   call node with one child for each result (`PMmap`, `PBrk2`, `PMunmap2`,
   `PSys`, ...), apply a routine summary (`PX`), change the known facts
   (`PFact`, `PSplit`, ...), or stop (`PExit`, `PSpin`, `PHandoff`).
   `munmap` of exactly one tracked entry is `PMunmap2`: its first child is
   the refusal (`-ENOMEM`, nothing else changes), its second child the cut.
2. Run the checker to get the result:
   `Eval vm_compute in AP.check SEGS IT A nx0 LIMIT HS bfuel fuel cs plan.`
   A good result is `COk shape`. `CErr` names the node and the state that
   failed.
3. State the lemma `AP.check ... = COk shape`, with the shape from step 2,
   and prove it with `CertRefl.cert_refl_vm constr:(COk shape).` Put
   `From Ltac2 Require Import Ltac2.` before `Require Import CertRefl`.
4. `AsanPlanSound.APS.check_sound` turns the lemma into
   `SpinAlg.srealizes` for each configuration that the checker state
   describes.

This library has no plan generator. Write plans by hand or with your own
tool.

Use `cert_refl_vm`, not `cert_refl`. `cert_refl` uses the native compiler,
which needs `.coq-native` files for every module that the file requires,
also the memory-image modules.

One hypothesis needs attention, and one that used to be here no longer is:

- `AsanCeil.placement_policy` says that each `mmap` without an address hint
  gets an address the checker's placement gate accepts. It is no longer a
  hypothesis: `AsanCeil.placement_policy_holds` proves it from
  `Sys/Mm/Mmap.linux_place`, the one address the spec gives such a mapping,
  so a proof that uses the `mmap` nodes of `AsanNodesMmLib` and
  `AsanNodesMmA` is conditional on nothing here. Those nodes used to take it
  as a named `PLACEMENT` hypothesis and do not any more.
- `AsanCeil.zero_random_draw` says that the `AT_RANDOM` bytes are zero.
  This is false for every real run. Only the old initial state
  `init_kn_zero` uses it. Use `init_kn` (the default), which needs no
  hypothesis.

Files: `AsanPlanCore`, `AsanPlan` (the checker), `AsanPlanSound`,
`AsanPlanSound2`, `AsanPlanSoundSums` (soundness), `AsanNodesIface` (the
obligation of each node), `AsanNodesMm*`, `AsanNodesLibE`, `AsanNodesAux`
(nodes for the memory system calls), `AsanAcct`, `AsanAcctShape`,
`BackingAlgebra` (memory accounting), `AsanPlacement`, `AsanCeil`,
`AsanInit`, `AsanStartLoops`, `AsanNodesStartX*`, `AsanPopFree`, `RefNodes`,
`Nodes`, `AgentNodes`, `RefLayout`, `RefMemcpyLib`, `MemsetLib`, `SumsLib`,
`MemSplit`, `ZStores`, `WalkTac`, `StartupAux`, `StartupTac`, `SpecConsts`,
`AsanHexScan`, `AgentLib`, `CertRefl`.

The `XSniff` routine (in `AsanPlan`) and the two address tables `ASAN` and
`BOTH` (at the end of `AsanPlanCore`) are for one specific binary. To add a node for your binary, add a checker
function and one section hypothesis in `AsanPlanSound`.

## Other libraries

| File | Contents |
| --- | --- |
| `LibWritev` | `writev` to a channel as a shape node, with short writes. Use it for musl's `__stdio_write`. |
| `AllocIface` | An abstract interface for an allocator (`malloc` and `free` rules). `AllocIfaceToy` shows that the interface can be instantiated. |
| `MallocDefs`, `LibMaskBits`, `RefEnframeArith` | Arithmetic of musl's mallocng allocator. These files set `zify_convert_to_euclidean_division_equations_flag` to `true`. |
| `NumPrint`, `Decimal` | Decimal output of numbers (`"%u"`, `"%d"`). |
| `StringsSpec` | The result of `memcmp` and the fill byte of `memset`. |
| `LiaFast` | Faster forms of `lia` and `nia`. You must opt in, file by file: put `Local Ltac lia ::= flia2.` after the last `Require`. Do not rebind `lia` globally. |
| `ShapeLaws` | Equalities of shapes (`t_eq`). |
| `TargetCover` | Prove a range of lengths from proofs for intervals that cover it. |
| `PlacementSearch` | A search for a free gap in the mapping ledger, proved sound and complete. |
| `ListFacts` | General list lemmas. |

## Import the system call checker with care

Some lemmas compute with the executable checker of one system call (for
example `check_write`). Import that checker
(`LinuxProcessSem.Checks.Sys.Fs.ReadWrite`), not
`Checks.ExecutableSpecs`. `ExecutableSpecs` imports the checkers of all
system calls, so `coqchk` must check all of them for each proof that
imports it. `FileSim`, `FileMixSim`, `ErrEscape2`, `ShapeNodes`, `LibWritev`
and the ASan node files use the full dispatch table, so they have this cost.

## Number representation

- A machine word is `word = bv 64`, a byte is `byte = bv 8`, and a
  register index is `reg = bv 5` (stdpp bit vectors).
- If arithmetic must not wrap (page rounding, bounds, overlap of
  intervals), compute in `Z` on `bv_unsigned x` and compare with `Z.ltb`
  or `Z.leb`. Use `Z_to_bv` only for values that go back into a register
  or memory.
- Immediates in the instruction syntax are bit vectors of their encoded
  width. For example, `addi sp, sp, -64` is `OpImm ALU_ADD 2 2 4032`.
- A `bv` value carries a proof, so `vm_compute; reflexivity` can fail on a
  `bv` equation. Use `StepTac.vm_refl_bv`, which goes through
  `bool_decide`.
- With stdpp, `cbn [skipn]` does not reduce `skipn 0`. Use
  `rewrite skipn_O`.
