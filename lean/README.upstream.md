# Lean port and first equivalence pilot

Rocq remains the reference specification. The pilot's execution judgments
were ported from `9a070af9e60b69831eee66067be0dd42e5ec244e`; entry initialization
and the public input domain follow `7f386a77d4d3877f162c91f06b7e4fcc1d998e61`.
The existing `theories/Examples/rwx_flag_ns/` snapshots are unchanged between
those references. A disagreement is a
port defect to investigate against that reference and, for implementation
behavior, the source authority required by `AGENTS.md`.
The [review record](PILOT_REVIEW.md) records the adversarial findings and
the tests that address them.
The [assurance procedure](ASSURANCE.md) separates the approved contract from
candidate proof code and requires an independently implemented verifier.
The [exit correspondence boundary](CORRESPONDENCE.md) describes the first
paired semantic normalization and the obligations that remain between provers.

## Pilot contract

`Examples/rwx_flag_ns/Proof.lean` retains the reference example's
`omni_strong_universal` and `strong_universal` statements: both images are
quantified over all valid process inputs and their own valid entries.
`modeled` remains part of the conclusion. Neither the images nor the
reference C and Zig programs are changed for Lean.

Source and target entry randomness and page-tail bytes are independent,
unconstrained draws. The capability word remains a shared process input
ranging over both reference masks. The `valid_input` contract retains the
reference's explicit false abort declaration. No additional restriction
is introduced to recover the program proof after these entry changes.

The equivalence relation permits an all-source-executions-error escape.
The pilot therefore also supplies `source_terminates` and
`target_terminates`: each proves total execution to exactly the exit-5
event with the input filesystem unchanged. Coinductive safety alone
would also admit divergence. `Domain.lean` separately constructs valid
entries for every valid input and exhibits a valid input, ruling out an
empty domain as a way to satisfy the universal statement.

The source startup reads the argument count from the stack and stores
its computed environment pointer before executing the program body.
Its code shares a writable executable segment with its globals.
`SourceExec.lean` proves that each store preserves the absence of overlay
bytes in the code interval before using a snapshot fetch fact. The byte
load after the flag store reads the actual memory overlay.

These are proofs about the Lean model. They are not a mechanized theorem
relating the Lean and Rocq developments, nor a new Linux conformance run.
The translation itself still requires source review. A checker/spec
agreement proof cannot establish that either matches Linux.

## Build and trust boundary

From the repository root, with elan and Python 3 installed:

```sh
(cd lean && lake build)
python3 tools/check_lean_policy.py
python3 tools/test_lean_policy.py
python3 tools/test_lean_axioms_glob.py
python3 tools/test_gen_lean_image.py
python3 tools/test_lean_image_integration.py
python3 tools/test_lean_kernel_regressions.py
```

Elan reads `lean/lean-toolchain`. The patched pin and its provenance are
recorded in [ASSURANCE.md](ASSURANCE.md).
The package uses only Lean's core and standard library. Generated image
sources live under `lean/.lake/generated/` and are build products, like
the Rocq example's generated instruction facts. Do not commit copies
into the source tree.

Lake tracks the snapshot `.v` files, their `.hex` chunks and the generator
dependencies. `tools/gen_lean_image.py` accepts the
pilot's snapshot grammar, including exported module bindings, and
rejects unrecognized forms. It proposes instructions; Lean checks every
proposed fetch and decode against the real image and decoder.

`Common/ImageBytes.lean` addresses a proof-checking cost: repeatedly
expanding a large string's UTF-8 representation. It proves a general
ASCII indexing equation and checks the original literals against it.
Chunk boundaries, permissions, metadata and byte semantics are preserved.
No faster replacement is installed in the model.

`Checks/Axioms.lean` enforces the allowed assumptions `propext`,
`Quot.sound`, and `Classical.choice`. Its import list is a generated
module under `lean/.lake/generated`, which `lakefile.lean` writes from the
library's module glob on every build, so a new module is audited by
`lake build` itself and no shared
import list has to be edited for it to be walked; a hand-maintained list
is exactly what a new module can be left out of. The syscall table works
the same way one level down: `Sys/SyscallTable.lean` and its pins
`Checks/Cases/SyscallTable.lean` are rendered under `lean/.lake/generated`
on every build by `tools/gen_lean_registry.py`, which `lakefile.lean` runs
from one registry file per twin under `Sys/Registry/`, and the module
`Sys.Registry.All` that the table imports to reach every twin is the second
generated import list `lakefile.lean` writes, beside `Checks.All`, from the
same directory.
A port adds its registry file and nothing else; the `generated-docs` job
runs `--check`, which refuses a copy of either rendered file in the source
tree, without needing a toolchain to have rendered one. A hand-written
module UNDER either name -- `Sys/SyscallTable/Extra`, say -- is not a copy
but cannot build either: the generated library claims every submodule of
its roots and reads it from `.lake/generated`, where it is not (the
lakefile's `SysTable` comment), and `lean_mutate.py`'s shadowed-sources
check refuses it by name. The tool's docstring says what a registry file may hold
and why the table copies each arm's text rather than naming it. The policy gate checks
source and generated module coverage, declaration assumptions, theorem
types and runtime attributes. It also replays every compiled project
module with the pinned toolchain's `leanchecker`, catching malformed
proofs even if their
original compilation bypassed kernel checking. This uses the same Lean
kernel, not an independently implemented verifier. Standard-library
imports remain trusted. `tools/lean_check_env.sh` (the `lean-trust` job)
runs that replay as a gate of its own and adds what the walk cannot
see: under this toolchain `collectAxioms` answers for an imported
declaration from a table the compiler wrote into the olean, so the gate
computes every theorem's axiom closure from the constant bodies the
replay verified (`tools/lean_trust/TrustReport.lean`), names a partial
definition or unsafe declaration a theorem under `Checks/` or
`Examples/` reaches, and refuses a toolchain other than the one
`leanchecker.pin` beside `lean-toolchain` names. Its negative tests must fail for the intended reason,
not merely obtain a nonzero compiler exit. Compiled evaluation is not
proof evidence. Any future foreign or alternate runtime implementation
needs its own justified correspondence argument and conformance tests.
These are development checks. They do not protect an expected statement from
coordinated edits to its definitions; use the separately controlled assurance
procedure for that threat model.

The Lean CI job is separate from the Rocq jobs. The repository's main
merge gate currently does not require that context; changing that gate
is separate work. A successful Lean build does not imply that the Rocq
or QEMU-based suites ran.

## Translation decisions

Lean modules retain reference paths, namespaces and semantic names.
Rocq section parameters become explicit arguments. Definitions use
`BitVec`, `Int`, and `Nat` for bitvectors and integer arithmetic; range
conditions remain integer conditions over `bv_unsigned`.

The task's address-space declaration is mirrored as in Rocq:
`State.VaSize` with its per-depth constants, `ProcInput.in_va_size`, the
`_va` entry predicates with their Sv48 instances, `Run.valid_entry` reading
the declaration, `Run.valid_input` pinning `Sv48`, and the
`valid_input_sv39` / `valid_input_sv57` / `valid_input_va_any` stances with
the split lemma.

The task's AT_HWCAP declaration is mirrored the same way and is a separate
axis: `Run.valid_input_hwcap_rv64gc`, `Run.valid_input_hwcap_rv64gcv`, the two
narrowing lemmas and `Run.valid_input_hwcap_splits` are in `Run.lean`, and
so is the pair declared over the ABORT stance. The sealed statements over
the two declared words are in `EquivalenceDefinition/Equivalence/ErrorFree.lean`:
`strong_universal_T_hwcap_rv64gc`, `strong_universal_T_hwcap_rv64gcv`, their
error-free twins, both `_splits` lemmas and the four `SPEC_*HWCAP*`
structures. The budgeted and scfg families, the abort AT_HWCAP combinations
among them, are not ported: `Equivalence/Budgets.lean` lists them as
`unported:`. Of
`theories/LinuxProcessSem/Checks/Cases/Hwcap.v`, parts (i), (ii) and (v),
which fire both declared pairs on the demo launch, and part (iv), which
pins why the declaration exists, stand in `Checks/Cases/Run.lean` beside
the pins on `Run.lean`'s input predicates; the section there says why
the other two parts are not there. The other Lean
statements quantify over `valid_input`, whose `valid_hwcap` clause admits
both words, so only the `*_hwcap_*` statements rest on a declaration.

The break's ASLR band is mirrored as a constant and a predicate, not as a
case file: `State.brk_aslr_max` is `State/Geometry.lean`'s
`brk_aslr_max` and `Run.valid_brk` is `Run.lean`'s, and
`tools/check_lean_spec_parity.py` holds both to the Rocq text, so the
band cannot move on one side alone. `theories/LinuxProcessSem/Checks/Cases/Brk.v`
pins the edges of that band — the kernel's reach admitted, the page above
it refused — against the Rocq constant, and is not ported: a Lean twin of
those pins would recompute the same two sums over a constant the parity
check already forces to equal the Rocq one, so it would go red only in
cases where the parity check goes red first. What a Lean twin would add
instead is a pin of the Lean `valid_brk`'s own decision procedure, which
belongs with the whole-program entry checks (roadmap item 4), where the
Lean side first has to read an image.

The register map is the literal radix tree, including noncanonical empty
nodes and its phantom width parameter. Extensional lookup equality does
not imply raw tree equality. This matters because later interfaces can
observe more than lookup results.

Lean supports coinductive predicates in `Prop`, used by `OmniRun`.
The existing stream data representation remains an indexed unfolding
with sticky terminal observations. `StreamLaws.lean` proves decomposition,
prefix, remainder and extensional observation laws, including infinite
streams and distinct network terminals. This is not a proof of a raw
equality-preserving bijection with Rocq colists. A later port depending
on raw colist equality must settle that obligation explicitly.

The program proof uses symbolic `ExitSim.to_exit` derivations rather than
the reference's general write-and-exit proof interface. Both feed the
baseline execution judgments. This avoids importing unused I/O proof
machinery; it does not skip startup, stores, fetches or exit dispatch.

What `Run.v` and `OmniRun.v` define and Lean does not yet is registered,
one `unported:` line with its reason per definition, in the
`rocq-baseline` header blocks of `Run.lean` and `OmniRun.lean`, which
`tools/check_lean_spec_parity.py` holds to the Rocq files (ticket A14);
this page does not list them, so there is one place to read and one to
correct. The budget-parameterised statement families of `Equivalence.v`
have no such register and are not ported; this sentence is stale once
`EquivalenceDefinition/Equivalence.lean` states them.
A ported definition can register `partial: <name> -- <reason>` for shapes it declines.
The header rules in [BRIEF.md section 3](../docs/lean-port/BRIEF.md#3-mirroring-rules) define validation, drift, and waiver requirements.

The killed/pending-signal state and the terminal rules ARE ported (ticket
A12): `State.ProcState` carries the kill flag, the pending SIGABRT, the
alternate-stack bit, the abort declaration and the stat pins; `Run.sstep`
has the `sstep_killed` rule and `sstep_exit` requires the flag clear;
`MustExit.must_exit_at` and `OmniRun.exits_with` carry the kill conjunct,
so a death by signal is not an exit; and `Run.decl_off_frame` with
`star_off_no_kill` is the named hypothesis under which the declaration-off
stance the pilot uses is the old semantics.  Unsupported signal calls
still fail closed in Lean.  The pilot's runs are under that stance and use
only exit dispatch because the pilot program issues only `exit`, so they
prove their entire trace without `decl_off_frame`; that hypothesis is what
`star_off_no_kill` takes for a run that issues other syscalls.

## Adversarial checks

The regression modules contain accepting and rejecting witnesses for
claims that could otherwise make the pilot misleading:

- `Checks/OmniPilot.lean`: an actual decoded infinite loop, refusal to
  prove its total termination, exact and incorrect exit traces, coverage
  and image guards.
- `Checks/PilotMemory.lean`: stack reads and zero-fill boundaries,
  disjoint stores, a code-overwriting store, and address wraparound that
  invalidates the frame argument when its bound is removed; nonzero entropy
  and address-dependent page tails reject fixed or truncated entry bytes.
- `Checks/PilotEntry.lean`: initialized capability bytes for both masks,
  rejection of a fixed mask or missing entry, and layout size consistency.
- `Checks/Cases/StreamLaws.lean` and `Riscv/Prelude.lean`: incorrect stream
  remainders, invented bytes, terminal confusion, noncanonical trees and
  update keys.
- `Examples/rwx_flag_ns/Domain.lean`: valid witnesses plus invalid stack
  and empty-argv rejection, both capability masks, independent entry draws,
  and the explicit abort-declaration boundary.
- `Examples/rwx_flag_ns/Checks.lean`: real-image exit-5 acceptance,
  exit-6 rejection and exclusion of source and target errors.

Generator and trust-policy selftests additionally exercise failures of
the proof pipeline. The universal program proofs do not replace these
checks of the statement, input domain and build machinery.

## Porting table

One row per arm of the Rocq `spec_table`, with the five boxes a port has to
turn green (`docs/lean-port/data/plan.json`, guard G10). The table is
generated from this checkout by `tools/lean_port_status.py --write` and
compared by its `--verify` in the required `generated-docs` job, so a hand
edit to it fails CI: what the tree says is the only thing it can say.

`●` the obligation holds, on a file in this checkout. `✗` a file in this
checkout says it does not. `○` nothing holds it yet -- the arm is not ported
that far. `…` this checkout cannot answer: the obligation needs a run and no
report of one is committed, or a file the reader needs -- the Rocq spec, the
kernel pin, the Lean table -- is missing or unreadable here, and the box's
reason says which. The last two are different answers: `○` is missing work,
`…` is a missing instrument or a broken checkout.

The first two boxes are questions about a FILE, and the arms of one spec file
share their answer: `pwrite64` is parity-green as soon as `Fs/ReadWrite.v` has
a twin that accounts for every definition, whether or not the Lean syscall
table carries `pwrite64` itself. The last three are per arm.

What each box reads, and what a `●` does not say:

- **parity** (G3) is the name half of `tools/check_lean_spec_parity.py`:
  every top-level Rocq definition of the spec file is a definition of the
  Lean twin, or an `unported:` entry of its `rocq-baseline` header. It is
  not the baseline half -- whether that commit resolves, is an ancestor, and
  whether the Rocq has moved since -- because those are questions about git
  history, and this block has to render to the same bytes from every checkout
  of one commit: a clone without history would answer them differently, and
  `--verify` would then call the table stale on a tree nobody edited. The
  guard runs that half itself, in the same required `generated-docs` job,
  which checks out with full history for it; a twin whose baseline is
  fabricated or whose Rocq has moved is red there beside a `●` here.
- **citations** (G4) is `tools/check_lean_pin_evidence.py`'s verdict on the
  arm's `Checks/Cases` twin with no kernel tree: every pin carries exactly
  one evidence annotation, and each `probe:`, `trace:`, `model:` and
  `rocq-twin:` resolves in this tree. Whether a `kernel:` annotation's
  symbol is really defined in the file it names at the pinned commit is
  resolved by the same checker in `lean.yml`, against a fetched kernel; a `●`
  here does not say it was.
- **checker** (G5) is membership of the arm's number in the Lean
  `checked_table`. `CheckedArm` cannot be built without its five proof
  fields, so a table that COMPILES has them -- but this box reads the text,
  not a build, and no required context builds `lean/`: `lake build` runs in
  the `lean` and `lean-trust` jobs, neither of them one of the seven the
  `protect-main` ruleset gates on. So a `●` here says the arm
  is named in the table, and the `lean`
  job says the table elaborates. An absent table is `…`, never five
  obligations vacuously met, and two members claiming one syscall number are
  reported as neither's.
- **replay** (G6) is a committed report of a replay of the recorded corpus
  through the Lean checker, which is a run and not a checkout: `replay.json`
  under `docs/lean-port/data/`, to be written by ticket H4's replay tool in
  the schema `tools/lean_port_status.py`'s own THE FIVE BOXES comment defines
  (nothing writes it yet, so the column is `…` today).
  Why the column is what it is, this checkout says: the board's legend prints
  the reason and so does every box in the column. A report cannot make an arm
  green without a Lean checker registered for it, without a recorded run that
  issues it, over no judged occurrence, or over another recording than the one
  `testing/syscall-check/traces/manifest.json` records; and a report that
  judged fewer occurrences of the arm than those traces hold leaves it `○`,
  because a replay stops at the first arm the Lean table lacks and what it
  did not reach is work, not evidence.
- **docs** (G8) is `tools/check_syscall_docs.py`'s header reader: some file
  under `docs/syscalls/` claims the syscall in its `<!-- syscall: -->`
  header. The decline half of G8, which compares the registers against the
  table rather than per arm, is that guard's own run.

The counts, the per-box reasons for every state and the rest of the port's
state are on the board, which is not committed here: the day branch's
publisher renders it from the day tip onto the `lean-port-pages` branch. This
block carries no total, because a total changes on every port and would make
two ports that touch different arms conflict on one line.

Every box is read from this checkout, so a change under `theories/` or
`lean/` can move one -- parity, citations and the checker box directly, and
the other two through the recorded corpus and the docs. `--write` rewrites
this block, the kept data files under `docs/lean-port/data/` and the pages in
one pass and has no README-only mode. The pages are ignored by git and
published by `tools/lean-port-ops/jobs/pages-publish.sh`, whose pathspec is
`docs/lean-port` alone, so a port that moves a box commits this file and the
kept data files `--write` changed -- `data/inventory.json` carries the same
boxes these rows are rendered from -- and nothing else. `--verify` in
`generated-docs` compares those committed copies with a fresh rendering and
holds the pages to reproducing from the committed sources, so nothing about
the pages goes red on such a pull request. The consequence to know rather
than rediscover: a stale block here is not repaired centrally, because the
publisher never commits this file. It is red in `generated-docs` on whatever
pull request carries it next, and the fix is to run `--write` and commit
`lean/README.md` together with any kept data file it changed.

<!-- BEGIN GENERATED PORTING TABLE: tools/lean_port_status.py --write -->

| # | syscall | spec file | parity | citations | checker | replay | docs |
| --: | --- | --- | :-: | :-: | :-: | :-: | :-: |
| 17 | `getcwd` | `Fs/DPath.v` | ● | ● | ● | … | ● |
| 19 | `eventfd2` | `Fs/EventFd.v` | ● | ● | ● | … | ● |
| 20 | `epoll_create1` | `Fs/EventPoll.v` | ● | ● | ● | … | ● |
| 21 | `epoll_ctl` | `Fs/EventPoll.v` | ● | ● | ● | … | ● |
| 22 | `epoll_pwait` | `Fs/EventPoll.v` | ● | ● | ● | … | ● |
| 23 | `dup` | `Fs/File.v` | ● | ● | ● | … | ● |
| 24 | `dup3` | `Fs/File.v` | ● | ● | ● | … | ● |
| 25 | `fcntl` | `Fs/Fcntl.v` | ● | ● | ● | … | ● |
| 29 | `ioctl` | `Fs/Ioctl.v` | ● | ● | ● | … | ● |
| 32 | `flock` | `Fs/Locks.v` | ● | ● | ● | … | ● |
| 35 | `unlinkat` | `Fs/Namei.v` | ● | ● | ● | … | ● |
| 46 | `ftruncate` | `Fs/Open.v` | ● | ● | ● | … | ● |
| 48 | `faccessat` | `Fs/Open.v` | ● | ● | ● | … | ● |
| 56 | `openat` | `Fs/Open.v` | ● | ● | ● | … | ● |
| 57 | `close` | `Fs/Open.v` | ● | ● | ● | … | ● |
| 59 | `pipe2` | `Fs/Pipe.v` | ● | ● | ● | … | ● |
| 61 | `getdents64` | `Fs/Readdir.v` | ● | ● | ● | … | ● |
| 62 | `lseek` | `Fs/ReadWrite.v` | ● | ● | ● | … | ● |
| 63 | `read` | `Fs/ReadWrite.v` | ● | ● | ● | … | ● |
| 64 | `write` | `Fs/ReadWrite.v` | ● | ● | ● | … | ● |
| 65 | `readv` | `Fs/ReadWrite.v` | ● | ● | ● | … | ● |
| 66 | `writev` | `Fs/ReadWrite.v` | ● | ● | ● | … | ● |
| 67 | `pread64` | `Fs/ReadWrite.v` | ● | ● | ● | … | ● |
| 68 | `pwrite64` | `Fs/ReadWrite.v` | ● | ● | ● | … | ● |
| 72 | `pselect6` | `Fs/Select.v` | ● | ● | ● | … | ● |
| 73 | `ppoll` | `Fs/Select.v` | ● | ● | ● | … | ● |
| 78 | `readlinkat` | `Fs/Stat.v` | ● | ● | ● | … | ● |
| 79 | `newfstatat` | `Fs/Stat.v` | ● | ● | ● | … | ● |
| 80 | `fstat` | `Fs/Stat.v` | ● | ● | ● | … | ● |
| 82 | `fsync` | `Fs/Sync.v` | ● | ● | ● | … | ● |
| 83 | `fdatasync` | `Fs/Sync.v` | ● | ● | ● | … | ● |
| 85 | `timerfd_create` | `Fs/Timerfd.v` | ● | ● | ● | … | ● |
| 93 | `exit` | `Kernel/Exit.v` | ● | ● | ● | … | ● |
| 94 | `exit_group` | `Kernel/Exit.v` | ● | ● | ● | … | ● |
| 96 | `set_tid_address` | `Kernel/Fork.v` | ● | ● | ● | … | ● |
| 98 | `futex` | `Kernel/Futex/Syscalls.v` | ● | ● | ● | … | ● |
| 101 | `nanosleep` | `Kernel/Time/Hrtimer.v` | ● | ● | ● | … | ● |
| 113 | `clock_gettime` | `Kernel/Time/PosixTimers.v` | ● | ● | ● | … | ● |
| 119 | `sched_setscheduler` | `Kernel/Sched/Syscalls.v` | ● | ● | ● | … | ● |
| 123 | `sched_getaffinity` | `Kernel/Sched/Syscalls.v` | ● | ● | ● | … | ● |
| 124 | `sched_yield` | `Kernel/Sched/Syscalls.v` | ● | ● | ● | … | ● |
| 130 | `tkill` | `Kernel/Signal.v` | ● | ● | ● | … | ● |
| 131 | `tgkill` | `Kernel/Signal.v` | ● | ● | ● | … | ● |
| 132 | `sigaltstack` | `Kernel/Signal.v` | ● | ● | ● | … | ● |
| 134 | `rt_sigaction` | `Kernel/Signal.v` | ● | ● | ● | … | ● |
| 135 | `rt_sigprocmask` | `Kernel/Signal.v` | ● | ● | ● | … | ● |
| 144 | `setgid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 146 | `setuid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 147 | `setresuid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 149 | `setresgid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 157 | `setsid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 158 | `getgroups` | `Kernel/Groups.v` | ● | ● | ● | … | ● |
| 159 | `setgroups` | `Kernel/Groups.v` | ● | ● | ● | … | ● |
| 160 | `uname` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 167 | `prctl` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 169 | `gettimeofday` | `Kernel/Time/Time.v` | ● | ● | ● | … | ● |
| 172 | `getpid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 174 | `getuid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 175 | `geteuid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 176 | `getgid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 177 | `getegid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 178 | `gettid` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 198 | `socket` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 199 | `socketpair` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 200 | `bind` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 201 | `listen` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 202 | `accept` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 203 | `connect` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 204 | `getsockname` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 205 | `getpeername` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 206 | `sendto` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 207 | `recvfrom` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 208 | `setsockopt` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 209 | `getsockopt` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 210 | `shutdown` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 211 | `sendmsg` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 212 | `recvmsg` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 214 | `brk` | `Mm/Mmap.v` | ● | ● | ● | … | ● |
| 215 | `munmap` | `Mm/Mmap.v` | ● | ● | ● | … | ● |
| 216 | `mremap` | `Mm/Mremap.v` | ● | ● | ● | … | ● |
| 220 | `clone` | `Kernel/Fork.v` | ● | ● | ● | … | ● |
| 222 | `mmap` | `Mm/Mmap.v` | ● | ● | ● | … | ● |
| 226 | `mprotect` | `Mm/Mprotect.v` | ● | ● | ● | … | ● |
| 233 | `madvise` | `Mm/Madvise.v` | ● | ● | ● | … | ● |
| 242 | `accept4` | `Net/Socket.v` | ● | ● | ● | … | ● |
| 260 | `wait4` | `Kernel/Exit.v` | ● | ● | ● | … | ● |
| 261 | `prlimit64` | `Kernel/Sys.v` | ● | ● | ● | … | ● |
| 278 | `getrandom` | `Drivers/Char/Random.v` | ● | ● | ● | … | ● |
| 435 | `clone3` | `Kernel/Fork.v` | ● | ● | ● | … | ● |
| 439 | `faccessat2` | `Fs/Open.v` | ● | ● | ● | … | ● |

<!-- END GENERATED PORTING TABLE -->

## Roadmap after the pilot

Each stage needs source correspondence review, a positive test and a
test rejecting the concrete mistake under discussion. Passing an earlier
stage is evidence for its own obligations, not a shortcut around later ones.

1. **Complete shared proof interfaces.** Port the remaining simulation,
   stream, signal-terminal and spurious-failure interfaces needed by the next example.
   Separate raw representation obligations from observational laws;
   preserve the original theorem domains and error distinctions.
2. **Build a differential ISA backend.** Preserve ISA effect tags,
   including illegal versus defined-illegal instructions, before the
   process layer collapses them. Reuse the existing decoder, instruction
   and access-report corpora. Compiled runner agreement and kernel-checked
   facts are separate gates. Resolve disagreements against the ISA or
   named implementation source.
3. **Port a syscall dependency slice.** Bring state operations, user-memory
   helpers, the relational specification, executable checker and
   soundness/completeness proofs together. Then run existing Linux probes
   and effective mutations. Preserve check order, errno precedence and
   explicit unmodeled boundaries. Harness limitations cannot become new
   semantic bounds.
4. **Expand whole-program proofs by dependency.** Keep every existing
   example. Include error-sensitive examples and genuine I/O before
   treating the port as general-purpose. Each completed example needs
   its original universal theorem, image validation and an inhabited
   domain; success-only examples also need a termination guarantee.
5. **Establish maintenance parity.** Make reference changes trigger paired
   Lean work or an explicit tracked gap. Promote the Lean CI gate only
   after it covers the promised surface. Independently validate any
   export or runtime toolchain used to consume the proofs.

The pilot does not supply a syscall or ISA runner, compressed/floating-point
coverage, general I/O proofs, or proofs for the other reference examples.
Those remain follow-up obligations; they must not be disguised by narrowing
a public equivalence theorem.
