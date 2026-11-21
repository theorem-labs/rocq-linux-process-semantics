# A compositional behavior-shape algebra (exploration)

Status: **prototype**, `theories/Common/ShapeAlg.v`. Everything in it is
`Qed`, axiom-clean (only the `PrimInt63`/`PrimString` primitives — it does
not even need `functional_extensionality`). It sits *beside* the existing
shape files; nothing is deleted or changed.

## The problem it attacks

Every shape file in `Common/` — `CatSim`, `StreamSim`, `DrainSim`,
`AllocSim`, `MmapSim`, `FileSim`, and the `*Mix`/`Escape` variants —
repeats the same four-part structure:

1. an inductive `to_X : machine_state -> ... -> Prop` characterizing
   reachable behavior, whose constructors are (silent machine step),
   (syscall node), (leaf);
2. `X_star_admits` — every expected trace is realized;
3. `X_star_only` — every realized trace is expected;
4. `~ reaches_error` — historically from a `won_path`/`mm_path`-style
   configuration invariant, now, for the files ported to the omni layer,
   a corollary of the one `OmniRun.exec` (or `coexec`) judgment that
   also gives parts 2 and 3 — then a `*_strong_equiv` packaging lemma.

Parts 2–4 are near-identical boilerplate, and — worse — the *relations*
are incompatible. `CatSim.to_wexit` cannot appear under an
`AllocSim.to_outcomes` node; putting an allocator in front of a write list
needs a new file (`AllocSim2` is exactly that, for one combination).

## The design

Two layers and one theorem.

### Layer 1 — shapes are prefix-closed trace sets

```coq
Definition TSet := list event -> Prop.

Definition t_nil  : TSet := fun tr => tr = [].
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.
```

Everything else is derived: `t_alt2 A B`, `t_exit code fs :=
t_emit [ExitEv code fs] t_nil`, `t_writes bufs T := fold_right (t_emit ∘ map (WriteEv 1)) T bufs`.

The key choice is that a shape denotes the **prefix-closed** set directly,
not a set of maximal traces plus a closure operator. Two consequences:

* it is *definitionally* the object `Run.obs_trace` is and the object
  `Equivalence.trace_equiv` compares, so `realizes_obs_iff` below is a
  bare `iff` with no closure on either side;
* a behavior with **no maximal trace** — a program looping forever on an
  infinite `stdin` colist, which `StreamSim` must express — is still an
  ordinary inhabitant of `TSet`. A prefix-closed set of *finite* traces is
  an ordinary inductive predicate even when unbounded. (Whether the
  *realization* relation can witness such a run is a separate question;
  see "What this does not cover yet".)

### Layer 2 — one realization relation

The syscall boundary is a single interface:

```coq
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))                         (* complete *)
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)). (* sound *)
```

"The admissible transitions out of `c` are *exactly* the `I`-indexed
family." The soundness half also rules out `SError` at this node for
free, which is where the whole `~ reaches_error` argument comes from.

```coq
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c I (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c, m_halted (cfg_model c) <> None -> realizes c t_nil
| rz_conseq : forall c T T', realizes c T -> t_eq T T' -> realizes c T'.
```

Three constructors, and they subsume every node in every existing shape
file:

| node | index `I` | events |
| --- | --- | --- |
| instruction step | `unit` | `[]` |
| `write(1, buf, n)` | `unit` | `map (WriteEv 1) buf` |
| `exit(code)` | `unit` | `[ExitEv code fs]`, successor halted (`rz_halt`) |
| `munmap` | `unit` | `[]` (model changes) |
| `mmap` | `{e ∈ errnos} + {a | grant_ok a}` | `[]` |
| `brk` | resolution set | `[]` |
| `read(0, …)` | chunkings of the stream | `[]` (model changes) |
| `openat` | outcome set | `[]` |

### The master theorem

Proved once, by induction on `realizes` — never on a shape:

```coq
Theorem realizes_obs_iff : realizes c T -> forall tr, obs_trace segs c tr <-> T tr.
Theorem realizes_no_error : realizes c T -> ~ reaches_error segs c.

Theorem shape_strong_equiv :
  realizes source_segs (init_config source_segs …) T ->
  realizes target_segs (init_config target_segs …) T ->
  Equivalence.modeled (run source_segs …)
  /\ Equivalence.equiv (run source_segs …) (run target_segs …).
```

Supporting structural facts, also proved once: `realizes_nonempty`
(`T []`) and `realizes_pclosed` (`T` is prefix-closed). Those two are
what make `t_emit [] T ≡ T`, i.e. what lets silent nodes disappear from
the denotation.

`realizes` is an exact omni judgment (the `node_ok` clause says the
transitions are *exactly* the family), so `OmniRun`'s two coinductive
judgments are corollaries: `realizes_cosafe : realizes c T -> cosafe segs c T`
and `realizes_coexec : realizes c T -> coexec segs c (fun tr o => T tr /\ ~ is_error o)`.
`realizes_no_error` and `shape_strong_equiv` are re-derived from them
through the compat `iff`s, and `shape_omni_strong_equiv` states the master
theorem as `OmniEquivalence.omni_strong_equiv` directly (two realisations
of one shape give the refinement pair `omni_trace_equiv_refinement`
needs). `realizes_admits` — the existential half — stays, and the bites
`realizes_not_errors` / `realizes_refutes_excluding` pin that a realised
shape never takes the escape and never hides one of its own traces.

### Composition

There is no "compose" lemma, and that is the point. Every combinator is a
**continuation-polymorphic introduction rule**:

```coq
Lemma rz_write1 : … -> realizes (mkCfg ms' model) T
                     -> realizes (mkCfg ms model) (t_emit (map (WriteEv 1) buf) T).
Lemma rz_mmap   : … -> (forall e, In e mmap_errnos -> realizes (fail e) A)
                     -> (forall a, grant_ok … -> realizes (succ a) B)
                     -> realizes (mkCfg ms model) (t_alt2 A B).
```

Blocks compose by plugging derivations into each other, exactly like the
sequencing rule of a Hoare logic. The #1 corpus unlock — "silent
nondeterministic allocation prologue, then a deterministic
write-list-then-exit tail" — is `rz_alloc_writes` at the bottom of the
file, four tactic lines, no new master theorem and no glue file.

### The existing shapes are instances

`ShapeAlg.v` proves the translation both ways for the two shapes it was
asked to cover, so the sanity check is machine-checked rather than on
paper:

* `cat_realizes : to_wexit segs ms bufs code -> realizes segs (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model)))`
* `twm_realizes`, `tmw_realizes` — the same for `MmapSim`'s `twm`/`tmw`,
  landing on `t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs))`
* `t_writes_exit_iff : t_writes bufs (t_exit code fs) tr <-> is_prefix tr (wevents bufs ++ [ExitEv code fs])`
* `t_writes_pick_exit_iff` — the same for the per-delivery shape a
  return-oblivious write node realizes once a channel write may fall
  short: `t_writes_pick bufs (t_exit code fs) tr <-> exists full, wpick (Z_to_bv 64 1) bufs full /\ is_prefix tr (full ++ [ExitEv code fs])`,
  over the channel-parametric `t_writes_ch_pick_exit_iff`. Every buffer
  must be nonempty, which every realized shape is
  (`CatSim.to_wexit_bufs_nonempty`)
* `two_traces_t_alt2 : t_alt2 … tr <-> MmapSim.two_traces bf cf bs cs fs tr`
* `cat_strong_equiv_alg` and `mmap_strong_equiv_alg` re-derive
  `CatSim.cat_strong_equiv_te` and `MmapSim.mmap_strong_equiv_te`
  statement-for-statement from `shape_strong_equiv` alone.

## How the five needed corpus compositions map on

1. **Alloc prologue + write-list tail** (~50% coverage) — `rz_alloc_writes`,
   already derived. For the brk chain: an `AllocSim`-style `brk` node is
   another `rz_node`; its resolutions become an indexed `t_alt`. A
   *data-dependent-length* brk chain (composition 5) is the same
   combinator applied recursively, with the outcome set built by the
   caller's own recursion instead of being enumerated — `t_alt` takes an
   arbitrary index `Type`, so `AllocSim`'s enumerated `U` stops being a
   constraint.
2. **Read-only openat/read/close + stdout writes** (composition 4) — this
   is the one the current design fixes most cleanly. `FileSim` swallows
   the trace and `CatSim` owns it, which is why they cannot combine; here
   an `openat` node and a `write(1)` node are both just `rz_node`s and sit
   in the same derivation. The `ExitEv code fs` leaf already carries the
   final file system, so file-system outcomes and stdout events live in
   one `TSet`.
3. **DrainSim with a multi-write tail** (composition 3) — the drain loop is
   a sequence of `read` nodes; the tail is `t_writes bufs (t_exit …)`
   instead of `t_emit (map (WriteEv 1) out) (t_exit 0 fs)`. Since the
   tail is the continuation parameter, no change to the loop reasoning.
4. **REPL/transaction loop** (composition 2, ~48 files) — expressible
   **for finite stdin**: the derivation recurses on the remaining input,
   exactly as `DrainSim` does today, and per-transaction output is an
   arbitrary `t_writes` block, which generalizes `StreamSim`'s
   echo-only tail. Line-oriented framing is a property of the *shape term
   the caller builds* (the `t_alt` over chunkings), not of the algebra.
   **Infinite stdin is not expressible** — see below.

### Update: the bounded drain loop is expressible after all

`Common/DrainAlg.v` closes composition 3/4 for the *bounded* form of the
read loop, which is the form the corpus actually uses:

```c
for (;;) { if (len >= CAP) break;
           r = read(0, buf + len, CAP - len);
           if (r <= 0) break;  len += r; }
```

Every admissible read delivers at least one byte, so this runs at most
`CAP` times **whatever the stream is, including an infinite one**. It
therefore needs no coinduction: `t_drain_ch` is a `Fixpoint` on a `nat`
fuel, `t_drain` is its instance at channel 0, and `rz_drain` is ordinary
induction on the fuel.  (Because `t_drain` wraps the fixpoint rather than
being one, `cbn [t_drain]` does not reduce it — unfolding one iteration
takes `cbn [t_drain t_drain_ch]`.) What is *not* expressible remains
`DrainSim`'s unbounded drain-to-EOF and `StreamSim`'s echo loop, where an
infinite stream really does mean a run with no maximal trace.

`DrainAlg` also proves the fact that makes the pattern usable at all:
`t_drain_collapse`. A `read` emits one `ReadEv` **per byte**, so the
chunking is invisible in the trace, and the entire nondeterministic loop
denotes the single deterministic shape

```coq
t_emit (map (ReadEv 0) (firstn cap stdin)) (Tfin (firstn cap stdin))
```

Two binaries that chunk stdin completely differently realize the *same*
`TSet`, which is exactly what `shape_strong_equiv` needs.

## What this does not cover yet

* **Non-terminating runs.** `realizes` is inductive, so every derivation
  witnesses a run that reaches a halted config in finitely many nodes.
  `StreamSim`'s infinite-input case (a run that never emits `ExitEv`)
  therefore cannot be derived. Two routes, in order of preference:
  1. make `realizes` **coinductive**. `realizes_star_only` and
     `realizes_no_error` survive unchanged (they induct on the *finite*
     `star` derivation and use `realizes` only by inversion).
     `realizes_admits` does *not* — it inducts on the derivation — and
     would have to be re-proved per shape family by induction on the
     (inductive, hence finite) derivation of `T tr`. That is one lemma per
     loop combinator, not per binary.
  2. keep it inductive and add a **step-indexed** approximation
     `realizes_n`, taking the union. Cheaper to prove, uglier to use.
  Either way the master theorem's *statement* does not change.
* **The `bh_all_errors` escape.** `ErrEscape`/`*Mix` shapes deliberately
  admit erroring branches; `node_ok` forbids `SError` by construction. The
  extension is a fourth constructor `rz_error` carrying the
  `bh_all_errors`/`AllocMixSim`-style side condition, at which point
  `realizes_no_error` becomes conditional. The corpus survey says no
  mined program needs it, so it is deliberately out of scope here.
* **`ErrEscape2`-style may-error sources.** Same reason.

## The per-binary interface

A per-binary proof (hand-written `step_*` chain, reflective symbolic
executor, or a Hoare logic over basic blocks) has to produce exactly one
thing: a `realizes` derivation. Its obligations are

* **straight-line code**: `rz_msteps` — supply a `CatSim.msteps` chain.
  This is precisely what `StepTac`'s `stepi`/`stepj`/`stepiv` already
  build, and precisely what a reflective executor would emit. Nothing
  about the shape leaks into it.
* **syscalls**: one `node_ok` per syscall, which is the `*_ok` +
  `sstep_*_inv` lemma pair the library already has for `write`, `exit`,
  `mmap`, `munmap`, `brk`, `openat`, `read`, `close`. These are proved
  once in `Common/`, not per binary.
* **loops / calls**: a Hoare-style block rule slots in as
  `realizes c' T -> realizes c T` for the block's entry/exit configs, i.e.
  a *shape-transformer*, which is the same shape as a Hoare triple with
  the continuation as postcondition. A loop rule is an induction on the
  loop's decreasing measure producing that transformer.

The boundary is deliberately narrow: the machine-step layer never
mentions `TSet`, and the shape layer never mentions instructions.

### What a LOOP needs from the per-binary layer that a straight line does not

Onboarding a loop-bearing binary (an mmap arena, a drain loop and a
recursive-descent parser, nine loops in all) surfaced one concrete gap
in the per-binary tooling, worth recording because it is the difference
between the straight-line examples and everything else in the corpus.

**`sym_block`'s result cannot be factored into a reusable lemma.** The
tactic ends by `destruct`ing `sym_exec_sound`'s conclusion, binding the
exit register file to a *local* variable `R` and its `regs_ok` fact to
`H`. Both are goal-local, so a statement of the form

```coq
Lemma prologue : exists regsE, getr regsE 11 = … /\ msteps segs init (mkst regsE …).
```

cannot be closed with `sym_block`: proving the `msteps` conjunct would
have to instantiate `regsE := R`, and `R` does not exist outside that
goal. The pre-`sym_block` `stepiv` style *can* be factored this way
(see `mmap_upper_ns_source.v`'s `source_to_mmap`) precisely because
there the exit register file is a concrete `regupd` chain rather than an
opaque variable.

For a single straight line this costs nothing — `modprint_ns_source.v`
keeps its whole derivation in one goal. For a program with several
loops it is a real obstacle, because per-iteration loop-body lemmas
(`LH acc c -> … -> LH (acc ++ bs) c'`, the shape `DrainAlg.rz_drain`
asks for) are exactly the statements one wants to prove once and reuse.
The fix is a `sym_block` variant that concludes

```coq
exists R, regs_ok E sr_exit R /\ msteps segs ms (mkst R pc mem rom)
```

with `sr_exit` a `vm_compute`d literal, so the caller can `destruct` it
themselves at the top of the enclosing lemma and keep `R` in scope for
the whole proof — i.e. move the `destruct` from inside the tactic to
outside it. Nothing about `sym_exec_sound` has to change.

### Update: the three gaps are closed

**1. Factorable blocks.** `SymExec.sym_exec_ex` is `sym_exec_sound`
with `st_ok`'s inner existential unfolded:

```coq
Theorem sym_exec_ex : … -> st_ok E base rom ss ms ->
  exists R, regs_ok E (s_regs ss') R
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss'))
                                 (mem_denot E base (s_log ss')) rom).
```

`SymTac.sym_block_ex segs ms fuel dirs rds pins pvals rvals R H Hms`
runs the same executor over the same block and leaves `R`, `H :
regs_ok …`, `Hms : msteps …` in the CONTEXT instead of spending them
on the goal; the entry state is passed explicitly rather than found in
the goal, because a factored statement's *exit* state also matches the
`mkst` pattern. The caller-side half is `sym_chain Hms` — the
`chain_mst; [exact Hms|]; norm_pc` that `sym_block` used to do
internally — and the exit registers are read out of the factored
lemma's own facts, or with the same `sym_regs H` as before when it
exported the whole `regs_ok`.

`modprint_ns_source.source_main_epilogue` is the demonstration: the
six instructions from 0x11034 to the `exit` ecall, which used to be a
`sym_block` inside `source_wexit`'s single goal, are now a standalone
lemma over an abstract register file, memory and frame base, with the
block's `SCFlat`/`SCReadBase`/pin obligations as its three hypotheses.
`source_wexit` calls it and its `ecall` tail is unchanged.

**2. `chain_mst` on `realizes`.** `chain_mst` gained
`eapply ShapeAlg.rz_msteps; [sym_halted | | ]` — the `m_halted`
premise pre-discharged (through `mmap_model`/`munmap_model`, which
touch `vm_maps` only), so the alternative leaves the same two goals as
every other one and existing `chain_mst; [exact Hms|]` call sites are
unaffected. `SymTac.chain_mst_realizes{,_mmap}` pin that.

**3. Read buffers in a grant.** `StreamSim.wseg_ok` decides buffer
writability over the STATIC segment image only, which says nothing
about an `mmap` arena. It turns out no new theory is needed: the
`read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w`
obligation and `RiscvSemantics.store_ok` are the same predicate on
`wview`, recursing on `a + 1` in lockstep, so `StoreOk.store_ok_wbuf`
bridges them in an eight-line induction and hands the buffer
obligation the whole store-side toolbox. The grant spellings are
`store_grant_wbuf` (against the `store_grant_ok` invariant a loop
carries), `heap_rg_wbuf` (against `Footprint`'s region vocabulary) and
`zmem_wbuf` (straight off the `mmap` step, through `mem_grows`).

## `Equivalence.v`

**No change needed.** `shape_strong_equiv` proves exactly
`Equivalence.modeled … /\ Equivalence.equiv … …` against the file as it
stands. The prefix-closed-`TSet` choice was made specifically so that
`trace_equiv (bh_traces source) (bh_traces target)` falls out of shape
equality with no bridging lemma.
