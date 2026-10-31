# Checking a fixed, reviewed proof contract

The operator must control the checker checkout and choose the approved
reference commit independently of the candidate. Run the checker before
executing candidate code on that machine. Selecting the candidate itself as
the reference verifies consistency with that candidate; it does not establish
preservation of an earlier contract.

Changes to the three program-proof modules can be submitted for checking. The driver
freezes all other Lean sources, entry/domain and execution definitions,
reference images and programs, generator inputs, and the acceptance machinery
against the approved Git tree. Updating these inputs requires a new reference
review, on the schedule in
[Updating the approved reference](#updating-the-approved-reference). This is
an acceptance rule for a fixed theorem, not a restriction on the semantics of
Linux or on future port work.

The shared exit artifact is also frozen: changing its bytes would change what
the two prover-local bridges claim to interpret. Its Lean normalization proofs
pass through the independent verifiers, with the remaining cross-prover
obligations described in [CORRESPONDENCE.md](CORRESPONDENCE.md).

## Why the earlier checks were insufficient

The original theorem pins elaborated their expected types in the candidate's
environment. A coordinated change to the domain or execution definitions
could therefore preserve the pins. An inhabited-domain witness only excludes
an empty domain; it does not show that the domain was not narrowed.

On 2026-09-14, the previously pinned compiler and its separate kernel replayer
both accepted the invalid nested-parameter declaration from upstream issue
[#14576](https://github.com/leanprover/lean4/pull/14577). This does not show that
the pilot used the defect. It does invalidate any claim that those two tools
provided independent protection against that kernel defect. The patched pin
is Lean `4.34.0`, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
It includes the subsequent nested-parameter correction as backport
`a068033d324c6eec8e5d4ace6ac137986160b3e9`. Regression fixtures cite their
upstream files and require the intended kernel diagnostic, with valid controls.

## Running an acceptance check

Use an unprivileged account on a disposable Linux worker with bubblewrap,
permission to create user, network and PID namespaces, and a user systemd
manager with delegated cgroup v2 memory, process and CPU controllers. The
worker wrapper reads the installed controls before starting; an unavailable
controller refuses the run. Build the verification tools from the approved
checker checkout before admitting candidate code:

```sh
elan toolchain install leanprover/lean4:v4.34.0
rustup toolchain install 1.98.1 --profile minimal
python3 tools/build_lean_assurance_tools.py \
  --cargo "$(rustup which --toolchain 1.98.1 cargo)"
python3 tools/test_lean_assurance.py
python3 tools/test_lean_assurance_exports.py
python3 tools/test_lean_assurance_worker.py
```

The bootstrap verifies the pinned comparator, exporter and nanoda commits,
uses the committed Lake and Cargo dependency locks, and records executable
hashes. The acceptance driver checks that record before using the tools.

Supply full commit IDs, not branches, and a new evidence directory:

```sh
python3 tools/run_lean_assurance_worker.py \
  --repository /path/to/repository \
  --reference "$APPROVED_COMMIT" --candidate "$CANDIDATE_COMMIT" \
  --output /path/to/new-evidence-directory \
  --toolchain-dir "$(elan run leanprover/lean4:v4.34.0 lean --print-prefix)" \
  --exporter tools/lean_assurance/.lake/packages/lean4export/.lake/build/bin/lean4export \
  --nanoda tools/lean_assurance/.lake/nanoda/target/release/nanoda_bin \
  --memory-max 6442450944 --tasks-max 512 --scratch-max 8589934592 \
  --cpu-quota 400 --runtime-max 5400
```

Both source trees are materialized from Git objects. Dirty working files and
prebuilt objects are not accepted as inputs. Each build gets a separate empty
cache and a read-only source tree. Its sandbox exposes the pinned compiler,
system programs, and its own inputs and scratch space. It has no host home,
credentials, control sockets, network access, or access to the other build.
The object-file exporter runs in the same isolation with a read-only cache.

Outside the candidate namespaces, within the bounded worker, the trusted frontend calls upstream comparator's
complete comparison and Lean replay routine. It compares the target statements
and their transitive definitions, including kernel primitives and quotient
checks. There are no definition holes. The driver then requires nanoda, an
independently implemented Rust checker, to validate exactly the same serialized
solution. No candidate `.olean` file is loaded by either trusted verifier.
This follows the separation described in the
[Lean validation manual](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

Only the driver writes `assurance/verdict.json`, after both verifiers succeed. It binds
the verdict to the reference and candidate commits/trees, theorem roots,
allowed assumptions, verifier provenance, and both exported artifacts. Logs
or an acceptance message from a candidate build never authorize acceptance.
Missing tools, isolation failures, malformed exports, failed stages and timeouts
refuse acceptance; there is no fallback to a weaker verifier.

The outer launcher writes `worker-verdict.json` only after the transient
service has completed successfully. That receipt binds the proof verdict to
the requested resource policy and the supervisor's actual cgroup readings.
A proof verdict left behind by a subsequently failed service is insufficient.
The worker tests exercise that distinction with real quota exhaustion and
failed commands carrying success text.

Build caches and each stage's private temporary directory share a size-limited
tmpfs. Separate temporary mounts would escape that filesystem limit; nested
user namespaces and writes to the sandbox root and device directory are
therefore refused. Memory accounting covers the entire service, including
temporary filesystem pages and descendants that start new sessions. The
scratch cap is an availability policy, not a new bound in the semantics.
Fixed driver logs and exports leave through the existing per-file limits.

SIGTERM and SIGHUP initiate service cleanup; systemd owns the whole process
tree and the final runtime deadline. A launcher killed with SIGKILL cannot
run cleanup, so its service can survive until that deadline. Use disposable
workers to bound the lifetime of the surrounding trusted tooling too.

## Updating the approved reference

The reference is the operator's choice and nobody else's: not a ticket, not
the candidate, not this file. What was missing was a rule for when it moves,
so any candidate the Lean port produces is refused against the pilot
reference with a message that names no way forward.

The rule is that a candidate changing the contract stays refused until the
operator has reviewed and approved a new reference containing that change.
The port changes the contract almost daily, so the reference is re-approved at
the port plan's milestones. They are `REFERENCE_REVIEWS` in
[the driver](../tools/check_lean_assurance.py), which records them in
`verdict.json`, and the tests hold each one to a node of
`docs/lean-port/data/plan.json` so the schedule cannot name a milestone nobody
planned:

- `M-table`, when the checked table (`K6b`) is merged. This is the earliest
  the names described below can be listed at all: the twin that states them
  is `K3`, which `K6b` needs through `K6a`, so it is inside `M-table`'s
  dependency set; and it is where the rows those theorems quantify over start
  existing;
- `M0`, when wave 0 is complete (`tools/lean_port_graph.py` defines the
  wave). Its dependency set contains `M-table`'s;
- `M-all`, when every arm's checker is registered: the soundness and
  completeness theorems then range over the complete table, and every
  registration before it edits a frozen file, which is a contract change this
  rule holds to a review;
- `R3`, the promotion pass, whose acceptance moves `lean` and `lean-replay`
  into `nightly_checks_green.sh --required`; the ruleset edit that makes them
  required contexts is `R3h`, the human step after it.

These are review points, not a chain. By the plan's dependencies `M-table`
is below `M0` and `M-all`, and `M-all` is below `R3`; `M0` and `M-all` are
unordered, each needing tickets the other does not, and `R3` does not need
`M0`. The middle two were one entry, `M2`, until the plan renamed its
milestones: `M1`, `M2` and `M3` became `M-spec`, `M-table` and `M-all`
(`tools/lean_port_graph.py` states the mapping, dated 2026-09-17 by the
plan's own clock, and `tools/test_lean_port_graph.py` pins that the old three
are gone), so a schedule still naming `M2` names nothing. `M-table` is the
rename the plan declares for `M2`; the old `M2`'s content, every checker
registered, is `M-all`'s, which is why both are here. What caught the stale
id was the plan-node test, not a reader: a schedule entry that is not a node
of the plan is a refusal nobody can act on.

At each of those points the reference is reviewed; between them the refusal
stands, and reviewing the change before choosing the reference is the whole
content of the rule. Selecting a candidate
as its own reference establishes no preservation, and neither does selecting
the newest commit whose run happened to go green. The schedule lives in the
driver and not in `docs/lean-port/data/progress.json`, which the ticket had
named: that file is a derived cache of ticket and pull-request state,
recomputed and rewritten by `tools/lean_port_state.py` on every refresh,
whereas the driver is a gate file, so moving the schedule is itself a
contract change and is reviewed as one.

### Why a new twin file is refused rather than admitted

A candidate carrying one new `Checks/Cases` twin is refused as `contract
inventory changed`, with the instruction above. The alternative considered was
to narrow the frozen set to the pilot's import closure computed from the
reference tree, leaving other files under `lean/` carried into the build but
uncompared. It was not taken, for two reasons.

It would not admit a spec port, which is the case that matters, and it would
not even move the refusal. A new dispatcher arm is a line in that twin's
`Sys/Registry/<Mirror>.lean`, and that file is inside the closure: the
pilot's proof reaches it through `Domain`, which imports `Run`, which imports
`Specs`, which imports the syscall table, which imports `Sys.Registry.All`,
the generated import list of every registry file. (Until T31 the arm was a
line in a committed `Sys/SyscallTable.lean` instead, one step earlier in the
same chain; the table is rendered into `lean/.lake/generated` on every build
now, and the registry file that feeds it took its place in the closure.) The
narrowed rule would freeze exactly that file too, and refuse the same
candidate at the same stage for the same reason. Where spec ports are
concerned the closure is not a smaller set, only the same one reached by a
computation that can go wrong.

It would also weaken the freeze for the candidates it did admit. The closure
is Lean's import graph, and the three mutable proof files help determine it: a
proof file may import a carried module, so the set of files participating in
an accepted proof would stop being the set the operator approved. Both kernels
still check the result, so what this costs is review surface rather than
soundness. That is why it is recorded here as a judgement and not as a defect
in either direction.

Behind both reasons sits a third refusal, which is the one worth knowing
about, because it would survive any inventory rule at all.
`Specs.syscall_spec` is `dispatch spec_table`, and `Run.sstep` names
`syscall_spec` in the premises of its syscall steps, so the table is among the
transitive definitions of every theorem about a run. The trusted frontend asks
for the target statements and their definitions with no holes, so a changed
table is a changed contract however the frozen set is drawn. The load-bearing
half of that is whether the comparison descends into an inductive's
constructor types and not only through `def` bodies, since that is how the
table is reached. Nothing in this tree settles it: the upstream comparator is
pinned but not vendored here, and
[the export tests](../tools/test_lean_assurance_exports.py) exercise the
refusal on a `def` a theorem's type names directly. It rests on the routine's
own completeness claim, recorded above.

None of this blocks a port PR. The port's merge gate is to be the `lean` and
`lean-replay` workflows, which `R3` prepares and `R3h` promotes to required
contexts; neither is required today, and `lean-replay` does not exist yet,
being a deliverable of ticket `H4`. This driver is not that gate. Its workflow
does run on every pull request, but only to test the machinery: the acceptance
step is guarded by `workflow_dispatch`, so no port PR is ever judged against a
reference unless
someone dispatches that run and chooses one.

### What the acceptance build needs that the contract does not carry

Since T31 the syscall table and its lookup pins are not files in the tree:
`lean/lakefile.lean`'s `generatedInput` facet renders them on every build by
shelling out to `tools/gen_lean_registry.py`, which reads the registry files
under `lean/` and the Rocq table and spec files under
`theories/LinuxProcessSem/`. A materialized contract tree carries neither the
generator nor those Rocq files -- `managed()` takes `lean/` without its
Markdown, `theories/Examples/rwx_flag_ns/`, `tools/lean_assurance/`, the
`lean*` workflows and the files it names by hand -- so an
acceptance run dispatched today fails at that facet rather than at a
comparison. What it costs, what it hides and what closes it are recorded in
[../bugs/lean-assurance-contract-lacks-the-table-generator.md](../bugs/lean-assurance-contract-lacks-the-table-generator.md);
the short of it is that the reference has to be re-approved in any case,
because T31 removed two files the inventory named, and the operator who
re-approves is the one who decides how far outside `lean/` the trusted base
reaches.

### What the contract names, and what the checker rung adds

The names both kernels replay (`contract_theorems()` in the driver) are the
pilot's own theorems today. As the checker rung lands the list gains the port
checker's soundness and completeness theorems, so that both kernels replay the
claim that the checker answers exactly what the specification admits, rather
than only the pilot's proofs. Listing a name in `PORT_THEOREMS` does two things,
and a test watches each: the name joins the list the comparator and nanoda are
asked for, and the module stating it must be in the contract, since
`port_theorem_files()` maps the name's module prefix to that module's file,
by the tree's convention that a declaration's namespace is its module, and
the inventory demands the file, so a contract naming the theorem cannot be
built from a tree that lacks it. The file's immutability is not new and is
not this rule's doing; every non-Markdown file under `lean/` is frozen
already. The list cannot be filled before the Lean twin of
`theories/LinuxProcessSem/Checks/ExecutableSpecs.v` exists, because a name no
build defines fails at the exporter, on the reference build, before the
candidate is built or exported. "Defines" is
read where the exporter looks, which is the import closure of the root
module `LinuxProcessSemantics` and not every file the library glob builds;
since #729 a twin adds a file and edits no import, so filling the list also
puts the twin on the root module's import chain, a frozen file, and that edit
is part of the same reference review.

## Authority and remaining obligations

The `lean-assurance` workflow's pull-request runs test the machinery. Its manual
acceptance mode must be dispatched from an approved workflow revision with an
independently selected reference. A candidate-editable job with a familiar
check name is not a trusted acceptance gate.

The [deployment procedure](../tools/lean_assurance/DEPLOYMENT.md) renders an
organization-required workflow pinned to an independently reviewed commit,
with a separately pinned checker checkout and no bypass actors. Its live
audit distinguishes that configuration from an ordinary named status check.
Deployment requires organization ruleset administration. A generated payload
or a passing offline configuration test does not establish live enforcement.
Whether it has been deployed is a question about GitHub rather than about this
tree, and the live rules answer it:

```sh
gh api repos/{owner}/{repo}/rules/branches/main \
  --jq '.[] | "\(.type) from \(.ruleset_source_type) \(.ruleset_source)"'
```

Read on 2026-09-16, that returned three rules, every one of them `from
Repository theorem-labs/linux-process-semantics`, which
`gh api repos/{owner}/{repo}/rulesets` names as the single active ruleset
`protect-main`: `deletion`, `pull_request`, and
`required_status_checks` carrying the seven contexts
`tools/nightly_checks_green.sh --required` prints. There was no rule of type
`workflow` and no organization-sourced rule at all. So the required assurance
workflow is not deployed, and nothing on `main` requires this driver. The
endpoint reports the rules from every source that applies to the branch, which
is why an organization ruleset would have appeared in that same answer. The
checking form of the same question, against an operator policy rather than by
eye, is `enforcement.py audit`, in the deployment procedure linked above.
Before approving a
reference update, review the semantic/domain/image changes separately from the
proof that consumes them; do not select a new reference merely because its
candidate run became green.

The trusted computing base still includes the chosen contract, tool build and
dependency sources, verifier plumbing, operating system and sandbox. Two
checkers can share a defect. Namespace isolation, stage timeouts and file/core
limits complement the worker's aggregate resource controls. The driver
inherits memory/process policy without imposing an address-space ceiling:
measured pilot compilations reserve tens of GiB virtually with roughly
0.5–1.3 GiB resident. Both a 16 GiB and a 64 GiB virtual-address cap aborted
valid compilation during thread creation. Increasing an empirical ceiling
for each larger import graph would not provide a RAM quota. Resource
exhaustion refuses acceptance and never changes the theorem or produces a
successful verdict.

The result is proof validity against the approved Lean contract. It does not
establish that this contract matches Rocq or Linux. Those correspondence
obligations and the repository's implementation-source authority remain in
force. Separate grading images must adopt the patched toolchain before being
used as verification evidence.
