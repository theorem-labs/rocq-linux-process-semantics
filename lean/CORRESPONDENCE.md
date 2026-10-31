# Exit correspondence boundary

The exit bridge proves a bounded semantic normalization in each prover. It
does not yet prove a theorem connecting the two prover environments, and it
does not establish Linux conformance. Neither production specification is
defined in terms of the bridge.

`LinuxProcessSem/Bridge/Exit.v` and
`LinuxProcessSemantics/LinuxProcessSem/Bridge/Exit.lean` consume the same
`theories/LinuxProcessSem/Bridge/exit.hex` file directly, through
`ReadFileString` and `include_str`. No generator proposes either term. The
file contains lowercase hexadecimal bytes without whitespace. `serialize`
and `deserialize` define the protocol; `deserialize_serialize` and
`serialize_injective` rule out ambiguous constructor encodings. Literal
fields are bytes because this first syntax needs only byte literals. Raw
syscall inputs remain unrestricted words in the original models.

The public `exit_dispatch_artifact` theorem quantifies over every input,
pre-model and outcome at either exit dispatch number. It proves an
iff between the existing syscall relation and the denotation of the
checked file. The file's successful decoding is a theorem, not a hypothesis
that could silently empty the domain. `denote_normal_form` retains the full
post-model, all effect ledgers and the event list, including the distinction
between a successful outcome and `Unmodeled`.
`status_mod256` additionally reduces each bitvector masking operation to the
unsigned remainder modulo 256 for every raw word, and `exit_dispatch_status`
derives that arithmetic observation from the existing syscall relation.

The common bytes settle which constructor and literals each side uses. The
following identifications still require a mechanized bridge:

| Boundary | Rocq representation | Lean representation |
| --- | --- | --- |
| Words and literals | stdpp `bv`, `Z_to_bv`, `bv_unsigned` | `BitVec`, `BitVec.ofInt`, unsigned `toNat` |
| Argument selection | `in_arg` with `Z.to_nat` | `in_arg` with `BitVec.toNat` |
| Masking to unsigned arithmetic | `status_mod256` over `Z` | `status_mod256` over `Int` |
| State update | Rocq `with_halted` | Lean `with_halted` |
| Outcomes and effects | Rocq records, lists and relation | Lean records, lists and relation |
| File decoding | Rocq primitive strings and hex reader | Lean strings and hex reader |

The state row is consequential. Current Rocq carries killed and pending
signal state that the Lean pilot does not carry. The theorems use each
side's actual setter, so they expose that obligation instead of asserting a
false equality between the records. They do not justify translating arbitrary
process steps or reusing a newer Rocq terminal theorem in Lean.

A complete formal correspondence needs the two semantic objects represented
in one kernel-checked setting, or a verified translation between settings,
with explicit input, model and outcome relations. It must prove both
directions and an inhabited relation on the claimed domain. Paired local
proofs and a common serialization are a useful decomposition of that work;
they do not discharge it. Before a process-step theorem, the signal and
terminal differences documented in `README.md` must be resolved.

The tests deliberately keep semantic and build evidence separate:

- `Checks/ExitBridge` in each prover accepts the intended outcome and rejects
  wrong argument selection, masking, return value and an invented unmodeled
  result. Wide-argument controls distinguish masking from passing the raw
  status through. These witnesses quantify over every pre-model.
- The decoder tests accept the decline constructor and reject unknown tags,
  wrong arity, odd length, trailing tokens and malformed hexadecimal input.
- `tools/test_exit_bridge.py` builds an isolated source fixture, changes only
  the shared file, requires a warm rebuild to fail at `artifact_checked`, and
  requires the restored file to build again. It runs separately under each
  prover so CI cannot hide a missing tool behind a skip.

Run both build systems and both dependency tests from the repository root:

```sh
(cd lean && lake build)
dune build --root . -j 2
python3 tools/test_exit_bridge.py --prover lean
python3 tools/test_exit_bridge.py --prover rocq
python3 tools/check_lean_policy.py
```

Changing both original specs and both denotations to the same wrong behavior
would preserve these local proofs. Source review and Linux probes remain
independent obligations, as does an externally approved assurance reference.
The shared file is consequently a frozen assurance input, not candidate proof
material.
