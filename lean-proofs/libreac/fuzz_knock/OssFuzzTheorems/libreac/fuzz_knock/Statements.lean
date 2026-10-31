-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/Statements.v
-- over rocq-linux-process-semantics f1006fe8's Lean twin.
import OssFuzzTheorems.Core.Shapes
import OssFuzzTheorems.libreac.fuzz_knock.Images

/-! # libreac / fuzz_knock: theorem statements

The Lean twin of `projects/libreac/fuzz_knock/Statements.v` of
theorem-labs/oss-verify-proofs-internal (`origin/ossv/recipes`
`9b0ac6f0e6780f75e0353041e71b055f15384ff0`), over the Lean twin of the Rocq
model those statements pin (rocq-linux-process-semantics `f1006fe8`). The
docstrings below are that file's, word for word, with two changes the port
forces: "Proving a statement" names `Proof.lean` and `theorem` where the Rocq
file names `Proof.v` and `Theorem`, and drops its two pointers to
`docs/proving.md`, which this repository does not carry. `ubsan_agrees`'s
docstring still opens "As `asan_agrees`", the released wording;
`asan_agrees` is one of the four statements this file does not carry (below).

SUBJECT. Four builds of libreac's own fuzz target `fuzz_knock`, which OSS-Fuzz
does not run, for libreac 1.9.0 (FreeREAC/libreac at `d16f3f4e`), static riscv64
Linux programs run as `<file> FILE`:

    plain       no sanitizer
    ubsan       UndefinedBehaviorSanitizer; a failed check executes a trap
    asan        AddressSanitizer; a report aborts
    asan_ubsan  both

`Images` names their memory images. A driver linked into every build reads FILE
as `[u16 config word][config bytes][u32 allocation mask][payload]`
(little-endian; the low 15 bits of the config word are the config length, and
this harness binary ignores the mask), calls `LLVMFuzzerTestOneInput(payload,
length)` one to four times (`(config[0] & 3) + 1`; once when there is no
config), and prints each return value. With a wrong argument count, a missing or
unreadable FILE, a FILE shorter than its header, or one of 64 MiB or more, it
exits with status 2 without calling the harness. Every statement quantifies over
all of these cases and over every other process input (see Vocabulary in
`OssFuzzTheorems.Core.Shapes`).

WHAT THE HARNESS CHECKS. Drives the knock, `reac_knock`, the check that a wire
carries no master before libreac drives it: from the payload, a start time and
up to 4096 events, each advancing a monotonic clock and saying whether a frame
was heard and whether the caller steps the knock. Neither the target nor the
library code it runs allocates memory. The harness checks:
(a) init starts a knock that listens, has no licence, and opened at the start
time. [abort(); not confirmed in the binary]
(b) A step answers NONE or DRIVE; DRIVE comes at most once and with the licence
set, and only at least REAC_KNOCK_LISTEN_NS after the wire came up and after the
last frame heard. [abort(); not confirmed in the binary]
(c) The licence is not withheld: a step at or after that time, with nothing
heard since and no licence yet granted, drives. [abort(); not confirmed in the
binary]
(d) granted is set exactly when DRIVE has come, and a later frame does not
revoke it; the state is PROVEN after DRIVE, else CANCELLED after a frame, else
LISTENING. [abort(); not confirmed in the binary]
Only the checks marked "confirmed in the binary" had their assertion text or
message found in the binary's bytes; for the others no usable text was found,
which does not mean that they are compiled out, and no statement below relies on
them.

Whether each statement is open, proved or known false is recorded in the harness
README, not here: this file changes only when a statement does.

## The four statements of this file that are NOT here

`asan_halts`, `asan_ubsan_halts`, `asan_agrees` and `asan_ubsan_agrees` name
`Images.asan` and `Images.asan_ubsan`, which `Images.lean` does not carry
(OSSV-265 gaps row K1-3). The five below are the released text of their five,
word for word. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.Statements

open OssFuzzTheorems.Core.Shapes
open OssFuzzTheorems.libreac.fuzz_knock

/-! ## Halting -/

/-- On every input on which the plain build is never refused memory for
exceeding 16 GiB, and when the environment refuses nothing it is not forced to,
every execution of the plain build exits with status 0 or 2. It never crashes,
fails an assertion, hangs, or leaves the model.

Not claimed: anything about what the program writes; anything about other
compilers, architectures or libreac commits. -/
def plain_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain

/-- As `plain_halts`, for the UBSan build. A failed UBSan check traps, so a
proof also shows that no check UBSan makes in this build fails on any such
input. -/
def ubsan_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.ubsan

/-- Every execution of the plain build exits, with any status, on every input
and whatever the environment refuses (any allocation, open or read may fail at
any time). It covers every input and any refusal, unlike `plain_halts`, but
allows any exit status. There is no ASan statement of this form: the ASan
runtime deliberately waits forever when its start-up reservation is refused, so
such a statement would be false for a reason that has nothing to do with this
harness.

Not claimed: anything about what the program writes. -/
def plain_halts_may_fail : Prop :=
  halts_may_fail Exits.any Images.plain

/-- As `plain_halts_may_fail`, for the UBSan build. It covers every input and
any refusal, unlike `ubsan_halts`, but allows any exit status. A failed UBSan
check traps, so a proof also shows that no check UBSan makes in this build fails
on any such input. -/
def ubsan_halts_may_fail : Prop :=
  halts_may_fail Exits.any Images.ubsan

/-! ## Agreement of each sanitizer build with the plain build -/

/-- As `asan_agrees`, for the UBSan build, with 16 GiB for the plain build. A
failed UBSan check traps, so a proof shows that no UBSan check in this build
fails on any such input. -/
def ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan

/-! ## Proving a statement

A proof is a directory named after the statement, in this fuzz target's proofs
folder, whose `Proof.lean` ends, for example, in

    theorem plain_halts_holds : Statements.plain_halts
-/

end OssFuzzTheorems.libreac.fuzz_knock.Statements
