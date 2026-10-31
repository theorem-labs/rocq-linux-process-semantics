# Pilot review record

The execution-judgment reference for this port is Rocq commit
`9a070af9e60b69831eee66067be0dd42e5ec244e`; the entry layout and public input
domain were subsequently updated against
`7f386a77d4d3877f162c91f06b7e4fcc1d998e61`. The review treats the proof
statement, the translation and the build machinery as separate obligations.
Kernel acceptance settles the Lean theorem; it cannot settle whether the
translated definitions faithfully describe Rocq or Linux.

## Methodology checks

| Question raised | Evidence required and review result |
| --- | --- |
| Could equivalence pass because every source execution errors? | The original escape remains in `equiv`. Separate total-execution theorems require the sole exit-5 event and unchanged filesystem. `Checks/OmniPilot.lean` also demonstrates the escape on an undecodable image and rejects strong equivalence because coverage is missing. |
| Could coinduction silently replace termination? | `loop_coexec_false` accepts safety of a real decoded self-loop; `loop_has_no_total_execution` rejects total execution of that same loop. The binary guarantees use inductive `exec`, with progress and every successor quantified. |
| Could the universal domain be empty or narrower than the reference? | `Domain.lean` constructs entries for every valid input and a concrete valid input, excluding vacuity. These witnesses and candidate-relative type pins do not establish that the domain was not narrowed. The later assurance procedure compares against an independently selected reference and tests rejection of a nonempty narrowed domain. |
| Could static fetch facts ignore writes to executable memory? | The source proof maintains a bytewise frame across both actual stores. `PilotMemory.lean` accepts disjoint writes and rejects a stale instruction after an overlapping write. A wrapped-store counterexample establishes why the non-wrapping premise is necessary; a store ending exactly at the address-space boundary remains accepted. |
| Could the exit proof discard filesystem state? | Review found that empty-filesystem fixtures alone would not detect this. `exit0_preserves_nonempty_filesystem` and its matching trace are paired with `exit0_changed_filesystem_trace_rejected`. |
| Could register-map equality become accidentally extensional? | The port uses the raw radix tree, including noncanonical empty nodes and phantom width. Lookup/update laws and a concrete unequal-tree witness pin that distinction. |
| Could the stream representation be overclaimed? | Decomposition, prefix, remainder and infinite-observation laws are proved. A raw equality-preserving correspondence with Rocq colists is explicitly not claimed; a future port relying on it must prove it. |
| Could an optimization change image bytes or memory behavior? | ASCII indexing is connected to the original string reader by a general equality theorem. Literal, nibble-order, chunk-boundary and Unicode counterexamples test that boundary. The image records and production memory functions remain the ones used by execution. |
| Could the nightly entry update be accommodated by fixing randomness or capabilities? | The proofs quantify each binary's entropy and page-tail draw independently and retain both shared capability masks. `PilotMemory` checks arbitrary-draw argc reads and rejects fixed entropy, zeroed/truncated tail bytes and an extra mapped page. `PilotEntry` checks initialized HWCAP bytes and rejects a fixed scalar mask and a missing entry. `Domain` pins both capability choices and the reference's explicit abort-declaration boundary. |
| Could the added abort declaration imply signal semantics were ported? | The ordinary contract requires false, as in the newer reference; signal calls still fail closed. The README and `Run` state that killed/pending-signal state, abort-enabled contracts and their terminal rules remain unported. The old general `exits_with` interface is not asserted equivalent on arbitrary new-reference configurations. The pilot's exact trace proof uses only exit dispatch. |
| Could a capability test compare an incorrect constant with itself? | Review found that the initial tests inspected only the distinguishing vector bit and used the symbolic tag. `PilotEntry` now checks both complete initialized pairs against literal bytes, including tag 16 and the shared low bits, and rejects tag 17 and a missing shared capability bit. |

Independent review compared `OmniRun`, `Equivalence`, `OmniEquivalence`,
`ExitSim`, the tree/stream changes and the memory-frame argument with the
reference definitions. It found no semantic mismatch in those ported
interfaces. This is a source review, not a cross-prover translation theorem.

## Build and generator findings

- **A second parser could read declarations hidden inside comments.** The
  strict image reader ignored them, while instruction proposal generation
  reparsed the raw file through a less strict helper. Proposals now consume
  the validated image data. `test_commented_dependency_is_never_read`
  requires the complete generated output to remain unchanged even when the
  commented path does not exist. Wrong exported bindings and unrecognized
  commands have separate refusal tests.
- **A fixed dependency list could miss a newly added chunk.** Lake now
  discovers the supported chunk filenames on each invocation. The integration
  test splits a chunk, builds, changes only the added chunk and requires
  regeneration. It also changes each existing source/target chunk and both
  metadata files, checks helper/generator changes, and exercises missing
  inputs and deleted outputs. These are actual Lake queries, not mocks of
  its dependency logic.
- **The library glob excluded the root module.** A clean build exposed this
  once the audit imported the umbrella: Lake tried the audit before building
  its missing dependency. The glob now includes the root and its submodules.
  A small Lake fixture builds that import graph; an otherwise identical
  fresh fixture using the old glob fails for the missing root object file.
  The two cases cannot share compiled artifacts.
- **An environment walk cannot see discarded anonymous proofs.** The policy
  retains a conservative source guard for admissions and native decision
  syntax, alongside checks of actual declaration axioms and runtime
  attributes. Fixtures cover anonymous proofs, unused axioms, disconnected
  modules, later-added runtime attributes and weakened theorem statements.
- **Axiom inspection alone does not establish kernel checking.** An
  adversarial fixture disabled kernel type checking and constructed a false
  theorem without adding an axiom. The trust gate now replays compiled
  declarations through the pinned toolchain's kernel and rejects that
  fixture. This replay is separate from the original compilation, but uses
  the same kernel; it is not an independently implemented verifier.
- **Source inventory must include misplaced modules.** A prefix-only scan
  could omit a new top-level file that Lake would also skip. Inventory now
  examines the source tree and generated sources, rejects unexpected module
  paths, and requires every project module in both the declaration audit
  and kernel replay. Disposable build scratch files remain outside the
  source inventory. Positive and negative fixtures pin these distinctions.
- **A compiler crash is not a successful negative test.** On the pinned
  toolchain, reporting a false large-list decision can overflow while
  formatting the error. Large-image negatives therefore prove explicit
  inequalities for wrong fetches, bytes and literal identities. A small
  false decoder claim still exercises normal compiler rejection. The test
  driver requires exit status 1 and the expected diagnostic for rejection.
  Subprocess regressions reject a signal termination even after the expected
  diagnostic was printed, as well as success, another error status and an
  unrelated diagnostic. Timeouts also fail the run.

## Reproducing validation

The results below record the original pilot run. The later finding that its
compiler and replayer shared a known kernel defect qualifies that evidence;
see [ASSURANCE.md](ASSURANCE.md) for the patched verification procedure.

The final pilot validation on 2026-09-12 passed:

| Check | Result |
| --- | --- |
| Clean `lake build`, followed by the final review-test refresh | 50 jobs, no warnings or errors |
| Fresh trust audit and kernel replay | 47 source modules covered; 4,061 declarations and 1,895 theorems audited; all 47 compiled modules replayed |
| Proof-policy regressions | 23 tests passed |
| Generator and test-driver regressions | 16 tests passed |
| Lake dependency and image-certificate integration | 21 cases passed, including the expected rejections |

Run the commands in [README.md](README.md), from a clean Lean build.
`tools/check_lean_policy.py` freshly evaluates the audit and compares the
imported module set against both source and generated files. Generator
mutations run in disposable fixtures and do not edit the reference images.

No Rocq specification, reference program or snapshot is changed by this
pilot. The Rocq/QEMU/Sail differential suites are not replaced by these
checks and were not run for this Lean-only change. Linux conformance and
mechanized correspondence between the two developments remain separate
obligations.

## Assurance review on 2026-09-14

Local review covered the assurance implementation at
`a1fba593183e93d9cdd31ef0ac3b63d861b8b1a7`. An earlier read-only review by
Claude Code using Fable 5.1 informed the fixes; local review agents also
examined the contract boundary, verifier sources, proof adaptations and
regression methodology.
Review suggestions were checked against the actual tools. In particular,
the proposed Lake job flag was unsupported, and controlled measurements
identified virtual-address limits as the compilation failure's cause.

The compiler migration changes proof elaboration and the development policy
check, without changing the model's definition bodies or public theorem
types. The acceptance procedure compares a separately selected contract and
requires both kernel implementations. An inhabited-domain witness alone
remains insufficient protection against narrowing.

The projection investigation distinguished two claims that an undirected
negative test would conflate: a structure-name annotation disagreement and
a nested parameter with the wrong actual type. The former produces different
kernel verdicts; the latter must be rejected by both. The source argument
and regression names are recorded in
[the divergence record](../bugs/lean-assurance-projection-annotation.md).

An additional axiom regression uses an unchanged permitted name with a
different, well-formed type. Nanoda accepts that axiomatic environment;
the comparator rejects the changed type against the reference. This pins
the distinction between a name allowlist and an approved assumption.

The final driver/export regressions passed 19 and 15 tests respectively.
The patched toolchain also passed 10 upstream-kernel regressions, 24 policy
tests, 16 generator tests and 21 image-integration cases. These are local
results. Actions/check-run access is unavailable to the configured token,
so this record does not assert GitHub CI results.

The full acceptance driver then passed on the commit above in 1,115.5 seconds:
two fresh isolated builds completed all 50 jobs, comparator accepted the
eight theorem roots and their definition dependencies, and nanoda checked
5,617 exported declarations with no errors. The reference and candidate were
both that commit. This is bootstrap validation of the reviewed baseline,
not evidence that its meaning equals an earlier revision; the export suite's
separate proof-refactor and contract-mutation cases test that distinction.
The two independently built exports have SHA-256
`443d83bab84c493281584b296b69b2afa19230242200bf681fbb322239ca150b`.
The final documentation and regression-only edits do not change any of the
76 inputs materialized by that run.

The local tests exercised real namespace isolation and inherited resource
limits. Aggregate memory/process/scratch containment of a production worker
was not validated. That worker setup and administrator-controlled GitHub
enforcement remain separate obligations in [ASSURANCE.md](ASSURANCE.md).
