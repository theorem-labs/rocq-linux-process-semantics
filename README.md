# rocq-linux-process-semantics

[![CI](https://github.com/theorem-labs/rocq-linux-process-semantics/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/theorem-labs/rocq-linux-process-semantics/actions/workflows/ci.yml?query=branch%3Amain)

This repository contains a model, in the Rocq Prover, of a Linux process
that runs a 64-bit RISC-V (RV64GC) binary. It also contains:

- the statements that a proof about such binaries must prove (for example,
  "these two binaries have the same observable behavior"),
- a proof library for these statements,
- an example proof about a small binary, and worked instances of two of
  the statements.

The model is not complete. It models part of Linux, and it uses
assumptions that it does not check. A proof is only as good as the model.
Read [SCOPE.md](SCOPE.md) before you use a proof as evidence about a real
program.

## Design priorities

The model describes the *supported systems*: stable Linux v6.18.46 and QEMU
user mode, on riscv64, with the RISC-V specification for instructions. Bugs
in Linux or QEMU do not count. The model does not choose one system: it
describes the behaviors that the supported systems can give, taken
together.

The model has three design priorities, in order of importance. Comments in
the code refer to them by number.

1. **Sound (required).** A statement that you prove with this model is true
   of the supported systems, under the assumptions in
   [SCOPE.md](SCOPE.md). Where the model cannot be sound, it says
   `unmodeled`.
2. **Precise (goal).** The model includes no behavior that no supported
   system gives.
3. **Covered (goal).** The model has no `unmodeled` cases.

Priorities 2 and 3 together make the model complete: a statement that is
true of the supported systems is provable with this model. The exception is
a statement that depends on a detail that the documented interface (man
pages, POSIX) leaves open, or that differs between the supported systems.
An example is the address that `mmap` chooses.

A failure of priority 2 can also break priority 1. If the model includes a
behavior that no supported system gives, a statement that compares sets of
behaviors, such as equivalence, can be false of the supported systems.
[SCOPE.md](SCOPE.md) lists the known gaps.

Comments that state kernel behavior name the file and the function in Linux
v6.18.46 (commit `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`).

## Packages

The repository has four opam packages. One dune project builds all of them.

| opam package | Rocq theory | Directory | Contents |
| --- | --- | --- | --- |
| `rocq-linux-process-semantics-core` | `LinuxProcessSemantics` | `theories/` (except `Common/` and `Examples/`) | The model and the statements. Also the tools `elf-snapshot` and `gen-fd-lemmas`. |
| `rocq-linux-process-semantics-common` | `LinuxProcessSemantics.Common` | `theories/Common/` | The proof library. |
| `rocq-linux-process-semantics-examples` | `LinuxProcessSemantics.Examples` | `theories/Examples/` | The example proofs. |
| `rocq-linux-process-semantics` | none | none | Installs the three packages above. |

`tests/` holds tests that are not in a package.

## Install

You need opam 2 and Python 3. opam installs Rocq (9.2 or later) and the
other dependencies. CI tests Rocq 9.2, 9.3 and the development version.

1. Add the Rocq opam repository:

   ```sh
   opam repo add rocq-released https://rocq-prover.org/opam/released
   ```

2. Pin and install all packages:

   ```sh
   opam pin add https://github.com/theorem-labs/rocq-linux-process-semantics.git
   ```

   opam finds the four `.opam` files at the top of the repository and pins
   all of them.

To install only one package, pin with `--no-action`, then install that
package:

```sh
opam pin add --no-action https://github.com/theorem-labs/rocq-linux-process-semantics.git
opam install rocq-linux-process-semantics-core
```

From a clone, use `.` in place of the URL.

A full build uses about 45 CPU-minutes. Each compile job can use up to
3 GB of memory.

## Build from a clone

```sh
opam install --deps-only .
dune build
```

`dune build` builds all theories, the examples and the tests. To build one
file, give its target, for example `dune build theories/Riscv/Decode.vo`.

`dune build -p <package>` builds one package only. It uses the installed
versions of the packages that it depends on, so install them first.

To run the tests of the ELF snapshot tool:

```sh
python3 tools/test_elf_snapshot.py
```

### Check one new file in a second

A full build takes about 45 CPU-minutes, so a typo in a new file is an
expensive thing to find. If the file is new — it is not yet part of any
installed package — you can type-check it on its own against the model
that opam installed, which takes about a second:

```sh
python3 tools/check_one.py theories/LinuxProcessSem/Procs.v
```

It compiles each file you name with `rocq compile`, with the warning flags
from the top-level `dune`, and prints the compiler's message. It writes
nothing beside your source, and it exits nonzero if any file failed.

Which model answers is the whole answer. The installed library is one
revision of the model; if it is not the revision your file will be read
against, you do not get an error, you get a wrong answer. So the script
has no default image: `--image IMAGE` (or `CHECK_ONE_IMAGE`) runs the
check inside a container, and before it compiles anything it works out
which revision that image carries — from the image's
`org.theorem.lps.commit` label, and failing that by hashing the model
sources the image installed and matching them against this repository,
which no missing label can defeat. It prints that commit and says
whether it is an ancestor of your HEAD, ahead of it, or on a different
line of development altogether. An image whose model it cannot identify
is refused; `--model-commit SHA` asserts a commit you established some
other way, and the output records that you asserted it.

The difference between two models is not always a missing lemma that
fails loudly: `State.mkProcState` takes twelve fields on `main` and
fifteen on the revision line. An arity error on a constructor such as
`mkProcState` usually means the image's model is not the line you wrote
against, not that your file is wrong. Read the printed model commit
against the commit your file is based on before you read the error.

Beside a failure it adds a hint for a mistake this repository produces
again and again: a numeral read in `bv_scope` where `Z`, `positive` or
`nat` was wanted, which is the most repeated of all and is fixed by
writing the scope (`0x1101c%Z`); a name that is stdpp's rather than
Stdlib's, `filter` above all; a `bv_eqb` lemma that does not exist; a
`Proof.` with no goal; and an inversion pattern short of branches, where
the fact wanted is that every constructor needs one, including the arms
the conclusion rules out. A hint is keyed to what the compiler said, not
to what the source looks like — `0x1101c` as a bit-vector literal and
`0x1101c` where a `Z` was wanted are the same characters — so a correct
file never gets one.

If a script calls it, test the last line, not the exit status:

```sh
python3 tools/check_one.py FILE.v | tee /dev/stderr | \
    grep -qx 'CHECK-ONE-RESULT: pass'
```

The exit status cannot tell you that the program ran. A truncated or
empty copy of it — a redirect that created the file before the command
that was to fill it failed — is a valid Python program that does nothing
and exits 0. `CHECK-ONE-RESULT: pass` or `CHECK-ONE-RESULT: fail` is
printed on every path out, including a refusal and a crash, so the
absence of that line means the check did not run.

This is a spell checker, not the build. It reaches what the compiler
decides by reading the file: a tactic that names a constant defined sixty
lines below it, a numeral in the wrong scope, a shadowed name, a lemma
that does not exist. It does not reach a file that runs for seven minutes
and then dies on a signal, or exhausts memory. It checks your file against
the **installed** library, so it cannot see a change you made to a file
that the library already contains — on a revision whose changes are mostly
such edits, its audience is the new self-contained witness files under
`theories/LinuxProcessSem/Checks/Cases/`. A switch or image can also
carry one package and not the others — the checker images carry
`rocq-linux-process-semantics-core` alone, so a file importing
`LinuxProcessSemantics.Common` or `.Examples` is reported `NOT CHECKED`
and counted as a failure rather than compiled. It does not check one new
file against another new file of the same branch, and it does not compile
anything that depends on your file. `dune build` still decides whether the
repository is sound. `python3 tools/check_one.py --help` lists the limits.

## What a proof shows

### The main statement

The main statement is `strong_universal_T` in
[`theories/EquivalenceDefinition/Equivalence.v`](theories/EquivalenceDefinition/Equivalence.v).
It is about two binaries, the *source* and the *target*. It says:

> For every valid process input, and for every valid launch of the source
> and of the target, the model covers every execution of the source, and
> the behaviors of the two binaries are equivalent.

- **Process input.** The input contains the arguments, the environment
  variables, the initial files, standard input, the user and group IDs, and
  the network peers. [`State.ProcInput`](theories/LinuxProcessSem/State.v)
  defines it. [`Run.valid_input`](theories/LinuxProcessSem/Run.v) gives its
  restrictions. The two binaries get the same input.
- **Launch.** The launch contains the stack address, the initial program
  break, the mmap base and the `AT_RANDOM` bytes. The statement quantifies
  the two launches independently. Thus a proof cannot use the same
  addresses or random bytes for both binaries.
- **Behavior.** A behavior is a set of finite observable trace prefixes,
  plus facts about errors. The set includes prefixes of executions that do
  not stop.

### What the model observes

The events are in [`State.event`](theories/LinuxProcessSem/State.v):

- input and output on a channel, one byte at a time,
- normal exit, with the final state of the modeled files,
- termination by a modeled fatal signal.

Thus these are different behaviors: different output bytes, a different
order of output, a different exit status, or different final file contents.

These are not observable: the number of instructions, the time, how a
program divides its output into `write` calls, and the file system calls
themselves. For example, `write("a"); write("b")` has the same observations
as `write("ab")`.

### The two conditions

For each input and each pair of launches, the statement requires:

1. **Coverage.** No execution of the source gets to a configuration that
   the model does not interpret (`unmodeled`).
2. **Equivalence.** One of these is true:
   - every execution of the source gets to the error transition (for
     example, a crash), or
   - the source and the target have the same set of trace prefixes, and no
     execution of the target can get to the error transition.

The first alternative of condition 2 accepts any target if the source always
crashes. One crash on one path is not sufficient: all executions must
crash. A system call that returns an error number is not a crash. A system
call that the model does not interpret does not give this alternative: it
makes condition 1 false.

Each example also checks `IMAGE_WF` for both images. These checks make sure
that the statement is not true only because an image cannot run.

### Other statements

| Statement | File | Use it when |
| --- | --- | --- |
| `strong_universal_error_free_T` | `Equivalence.v` | Neither binary may crash. The statement has no "source always crashes" alternative. |
| `*_budgets` variants, `SPEC_*BUDGETS*` | `Equivalence.v` | The source is a plain build and the target is a sanitizer build of the same program. The statement excludes inputs on which the source exceeds its memory budget. |
| `*_scfg` variants, `SPURIOUS_CFG` | `Equivalence.v` | The task removes some families of environment failures that the model's state does not force. |
| `*_abort` variants | `Equivalence.v` | The task declares that `abort()` is a terminal outcome. |
| `*_either` variants | `Equivalence.v` | The task does not choose: the statement must be true with and without the `abort()` declaration. |
| `*_hwcap_*`, `*_sv39`, `*_sv57` variants | `Equivalence.v` | The task fixes the `AT_HWCAP` value or the address-space size. |
| `omni_strong_universal_T` | `OmniEquivalence.v` | You prefer proofs over execution trees. It is proved equivalent to `strong_universal_T`. |
| `must_exit_with` | `MustExit.v` | Every execution must stop with a given exit code. Equal trace prefixes do not show this. |
| `halts_allowed_T` | `HaltsAllowed.v` | One binary must stop with an exit code from a given set. |
| `SPEC_PATCH_CLASSIFY*` | `PatchClassifySpec.v` | A patch and two classifier programs. See `theories/Examples/patchclassify_demo/`. |
| `weight_bound_T` | `Measure.v`, `MeasureLib.v` | A bound on the weight of the inputs that a classifier rejects. See `theories/Examples/measure_lib_demo/`. |

A result must name the statement that it proves.

## How the model works

### System calls

A system call specification gives a set of permitted outcomes. It does not
choose one outcome. [`Monad.v`](theories/LinuxProcessSem/Monad.v) defines
the specification language: `choose P` permits each value that satisfies
`P`, and `alt` combines alternatives. An outcome gives a return value, the
changes to memory and state, and the events. The `Unmodeled` outcome says
that the model does not interpret the case.

For example, the input fixes which bytes are available to `read`. The model
lets `read` return any nonempty prefix of them. Thus two programs can read
the same input in different block sizes.

By default, the environment can make some system calls fail (for example,
`mmap` can return `ENOMEM`). Thus a program that does not handle an error
can have a different behavior from a program that handles it.

| File | Contents |
| --- | --- |
| [`Specs.v`](theories/LinuxProcessSem/Specs.v) | The interface of the system call specifications, and the map from kernel source files to specification files. |
| [`Sys/`](theories/LinuxProcessSem/Sys/) | One specification per system call, in directories like the kernel source. For example, `Sys/Fs/ReadWrite.v` is for `fs/read_write.c`. |
| [`Checks/`](theories/LinuxProcessSem/Checks/) | An executable checker for each system call, and the proof that it agrees with the specification. |
| [`State.v`](theories/LinuxProcessSem/State.v), [`Fs.v`](theories/LinuxProcessSem/Fs.v), [`Run.v`](theories/LinuxProcessSem/Run.v) | The process state, the file contents, and how instructions and system calls make an execution. |
| [`Riscv/`](theories/Riscv/) | The decoder and the semantics of RV64GC instructions. |
| [`MemImageType.v`](theories/LinuxProcessSem/MemImageType.v), `tools/elf_snapshot.py` | How a binary becomes a memory image. |

## Known limits

[SCOPE.md](SCOPE.md) lists where the model is narrower than the supported
systems, the assumptions that it does not check, and the known gaps in
precision. Read it before you use a proof as evidence about a real program.

## Write a proof

- [`theories/Examples/README.md`](theories/Examples/README.md) tells you how
  to add an example and how to write its proof.
- [`theories/Common/README.md`](theories/Common/README.md) tells you which
  part of the proof library to use.

## License

MIT. See [LICENSE](LICENSE).
