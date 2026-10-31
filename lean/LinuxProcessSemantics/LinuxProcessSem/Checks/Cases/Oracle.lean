import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Oracle — the recorded answers pins state their values through

GENERATED.  `tools/gen_lean_oracle.py --root . --write` writes this file from the
recorded corpus and the rows the pins cite; `--verify` refuses a stale copy
in the `generated-docs` job.  Edit the generator, never this file.

Not part of the trusted specification, and no Rocq twin: there is nothing to
claim a `rocq-baseline` against, because nothing here is ported.  Every value
below was PRODUCED -- by the pinned kernel under
`testing/syscall-check/run-tests.sh`, with any `--mutate` of the case
applied -- and recorded in the corpus manifest's own words:

  corpus lps-trace-corpus/1, Linux 6.18.46 at 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5

A row is one `syscall` record, addressed `<probe>/<NNN>#<seq>`
(`testing/syscall-check/TRACE.md` is the format) and named here with the two
separators a Lean name cannot carry spelled out: `mmap_shapes/001#1` is
`row_mmap_shapes_001_s1`, and six definitions stand over it --

    row_…_call     the number, the six registers and the memory read
    row_…_state    the MODEL the answer was given in, or `none`
    row_…_effect   what the kernel did, the case's `--mutate` applied
    row_…_conform  whether the run was graded `conform`
    row_…_holds    that call, in that state, put to the dispatcher
    row_…_answer   the recorded effect as an outcome in that state

-- and a pin states its value over them:

    theorem … : row_probe_000_s0_holds o ↔ o = row_probe_000_s0_answer

so the number, the registers, the state and the answer all come from the
recording and the only free choice left is the SHAPE of the outcome: an
admitted answer, a refused one, or a decline. `tools/check_lean_oracle_pins.py`
refuses a hand-written errno where a row holds the same answer, and
`docs/lean-port/TESTING.md`'s L7 says what the layer cannot see -- above all
that a row is ONE implementation's answer, so a pin over it proves the spec
ADMITS that answer and never that another supported implementation would
give it too.

Six definitions and no `structure`, and the id is not the name: both are
PIN-7's (`tools/check_lean_pins.py`), which refuses a guillemet-quoted name
and a type declaration under `Checks/Cases/` because a name bound either way
is one its readers do not follow. The generator's MODULE-SHAPE rule refuses
its own rendering if that syntax comes back.

The generator's own rules -- what makes a record renderable, and the bounds
on the memory and the prefix it will render -- are its docstring's, and
`tools/test_gen_lean_oracle.py` shows each of them refusing a case. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Oracle

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## What a row is -/

/-- The `ProcInput` `LpsRunner.Replay.procInputOf` builds from a header whose
`stdin`, `peers`, `seed_files` and `initial_fs` are empty -- the only headers
the generator renders, since each of those is a stream or an image the model
reads through a function. -/
def oracle_input (uid gid : word) (groups : List word) (nofile sigmask hwcap : word)
    (abort : Bool) (va : VaSize) : ProcInput :=
  { in_argv := [], in_envp := [], in_image_fs := [], in_tmp := []
    in_stdin := IEof, in_urandom := IEof
    in_uid := uid, in_gid := gid, in_groups := groups
    in_net := net_silent
    in_nofile := nofile, in_sigmask := sigmask, in_hwcap := hwcap
    in_abort_terminal := abort, in_va_size := va }

/-! ## The model the answer was given in

`oracle_fold` is the replay's own fold, one definition for the whole tree:
`Checks.ExecutableSpecs.check_syscall_for_run` over the records before the
row's, the model threaded through, and `none` as soon as the checker refuses a
record -- which is what makes a pin over such a row fail to close
instead of closing on a model nobody computed.

A pin over a row whose state is folded over a non-empty prefix resolves
that fold BEFORE it normalizes: `sys_norm`'s ground pass does not evaluate
it at any recursion depth (measured to 1000000), because the fold is a run
of the checker itself, while kernel reduction does it in milliseconds.  The
shape is

    simp only [row_probe_000_s1_holds, row_probe_000_s1_answer, spec_at,
      answer_at, show row_probe_000_s1_state = some _ from rfl]
    sys_norm

and the `rfl` is the fail-closed half: a row whose prefix the checker
refuses has no such equation, so the pin does not elaborate rather than
closing on the `False` arm of `spec_at`. -/
@[sys_simp] def oracle_fold (m : Model) (pre : List (SyscallInput × SyscallEffect)) :
    Option Model :=
  match pre with
  | [] => some m
  | (i, eff) :: rest =>
      match check_syscall_for_run i eff m with
      | some (CheckOk m' _) => oracle_fold m' rest
      | _ => none

/-- A row's own call, put to the dispatcher: the number and the registers
decide which arm answers, and the folded state is the model it answers in.
`False` where the fold has no model, so a pin over a row whose prefix the
checker refuses cannot close. -/
@[sys_simp] def spec_at (call : SyscallInput) (state : Option Model)
    (o : outcome SyscallEffect) : Prop :=
  match state with
  | some m => syscall_spec call m o
  | none => False

/-- The outcome the record IS: the recorded effect, in the state the answer
was given in, with no events (a pure decision emits none).  `Unmodeled`
where the fold has no model, for the reason `spec_at` gives. -/
@[sys_simp] def answer_at (state : Option Model) (eff : SyscallEffect) :
    outcome SyscallEffect :=
  match state with
  | some m => Ok eff m []
  | none => Unmodeled

/-! ## The rows the pins cite -/

/-- `clone_fork/001#0`: clone(17, 0, 0, 0, 0, 0) -- the kernel answered `39`,
and the checker's verdict on the pair was `ok`.

Recorded 2026-09-16 in `testing/syscall-check/traces/clone_fork/001.jsonl`
under case `conform -- fork # the kernel hands the parent a pid; the model
admits it`. -/
def row_clone_fork_001_s0_call : SyscallInput := SyscallInput.mkInput 220 [17, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_clone_fork_001_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 8192), (73728, 4096)] 64581632 140735745130496 140737022161696 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_clone_fork_001_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 39 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_clone_fork_001_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_clone_fork_001_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_clone_fork_001_s0_call row_clone_fork_001_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_clone_fork_001_s0_answer : outcome SyscallEffect :=
  answer_at row_clone_fork_001_s0_state row_clone_fork_001_s0_effect

/-- The recorded answer as a value: `39`, off a `conform` case.
trace: clone_fork/001 -/
example :
    row_clone_fork_001_s0_effect.eff_ret = 39
      ∧ row_clone_fork_001_s0_conform = true := by decide

/-- The fold has a model, so `row_clone_fork_001_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_clone_fork_001_s0_state.isSome = true := by rfl

/-- `clone_fork/002#0`: clone(17, 0, 0, 0, 0, 0) -- the kernel answered `41`,
and the checker's verdict on the pair was `ok`.

Recorded 2026-09-16 in `testing/syscall-check/traces/clone_fork/002.jsonl`
under case `conform -- twice # two real forks, two pids`. -/
def row_clone_fork_002_s0_call : SyscallInput := SyscallInput.mkInput 220 [17, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_clone_fork_002_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 8192), (73728, 4096)] 848842752 140735944937472 140737448498256 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_clone_fork_002_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 41 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_clone_fork_002_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_clone_fork_002_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_clone_fork_002_s0_call row_clone_fork_002_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_clone_fork_002_s0_answer : outcome SyscallEffect :=
  answer_at row_clone_fork_002_s0_state row_clone_fork_002_s0_effect

/-- The recorded answer as a value: `41`, off a `conform` case.
trace: clone_fork/002 -/
example :
    row_clone_fork_002_s0_effect.eff_ret = 41
      ∧ row_clone_fork_002_s0_conform = true := by decide

/-- The fold has a model, so `row_clone_fork_002_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_clone_fork_002_s0_state.isSome = true := by rfl

/-- `clone_fork/002#1`: clone(17, 0, 0, 0, 0, 0) -- the kernel answered `42`,
and the checker's verdict on the pair was `ok`.

Recorded 2026-09-16 in `testing/syscall-check/traces/clone_fork/002.jsonl`
under case `conform -- twice # two real forks, two pids`. -/
def row_clone_fork_002_s1_call : SyscallInput := SyscallInput.mkInput 220 [17, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_clone_fork_002_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 8192), (73728, 4096)] 848842752 140735944937472 140737448498256 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 220 [17, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 41 [] [] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_clone_fork_002_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 42 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_clone_fork_002_s1_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_clone_fork_002_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_clone_fork_002_s1_call row_clone_fork_002_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_clone_fork_002_s1_answer : outcome SyscallEffect :=
  answer_at row_clone_fork_002_s1_state row_clone_fork_002_s1_effect

/-- The recorded answer as a value: `42`, off a `conform` case.
trace: clone_fork/002 -/
example :
    row_clone_fork_002_s1_effect.eff_ret = 42
      ∧ row_clone_fork_002_s1_conform = true := by decide

/-- The fold has a model, so `row_clone_fork_002_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_clone_fork_002_s1_state.isSome = true := by rfl

/-- `clone_fork/003#0`: clone(17, 0, 0, 0, 0, 0) -- the record carries `0`,
and the checker's verdict on the pair was `reject`.

Recorded 2026-09-16 in `testing/syscall-check/traces/clone_fork/003.jsonl`
under case `reject --mutate clone:ret=0 -- fork # the CHILD's answer,
forged over the real pid`. The case staged `--mutate clone:ret=0`, so the
answer is the one the checker was shown and not the kernel's own; the case
expects it to be REFUSED. -/
def row_clone_fork_003_s0_call : SyscallInput := SyscallInput.mkInput 220 [17, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_clone_fork_003_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 8192), (73728, 4096)] 812244992 140736121925632 140737055767920 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_clone_fork_003_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 0 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_clone_fork_003_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_clone_fork_003_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_clone_fork_003_s0_call row_clone_fork_003_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_clone_fork_003_s0_answer : outcome SyscallEffect :=
  answer_at row_clone_fork_003_s0_state row_clone_fork_003_s0_effect

/-- The recorded answer as a value: `0`, off a `reject` case.
trace: clone_fork/003 -/
example :
    row_clone_fork_003_s0_effect.eff_ret = 0
      ∧ row_clone_fork_003_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_clone_fork_003_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_clone_fork_003_s0_state.isSome = true := by rfl

/-- `clone_fork/008#0`: clone(16401, 0, 0, 0, 0, 0) -- the kernel answered
`56`, and the checker's verdict on the pair was `unmodeled`.

Recorded 2026-09-16 in `testing/syscall-check/traces/clone_fork/008.jsonl`
under case `fail-closed --expect-unmodeled clone -- vfork # a clone the
kernel accepts and the model declines`. -/
def row_clone_fork_008_s0_call : SyscallInput := SyscallInput.mkInput 220 [16401, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_clone_fork_008_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 8192), (73728, 4096)] 693047296 140735915057152 140737416133568 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_clone_fork_008_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 56 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_clone_fork_008_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_clone_fork_008_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_clone_fork_008_s0_call row_clone_fork_008_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_clone_fork_008_s0_answer : outcome SyscallEffect :=
  answer_at row_clone_fork_008_s0_state row_clone_fork_008_s0_effect

/-- The recorded answer as a value: `56`, off a `fail-closed` case.
trace: clone_fork/008 -/
example :
    row_clone_fork_008_s0_effect.eff_ret = 56
      ∧ row_clone_fork_008_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_clone_fork_008_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_clone_fork_008_s0_state.isSome = true := by rfl

/-- `clone_fork/012#0`: clone(17, 0, 0, 0, 0, 0) -- the record carries
`errno_ret EAGAIN`, and the checker's verdict on the pair was `ok`.

Recorded 2026-09-16 in `testing/syscall-check/traces/clone_fork/012.jsonl`
under case `conform --mutate clone:ret=-EAGAIN -- fork # an errno forged
over a real fork is admissible on its own`. The case staged `--mutate
clone:ret=-EAGAIN`, so the answer is the one the checker was shown and not
the kernel's own; the case expects it to be ADMITTED, as an answer some
real run could give. -/
def row_clone_fork_012_s0_call : SyscallInput := SyscallInput.mkInput 220 [17, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_clone_fork_012_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 8192), (73728, 4096)] 220065792 140735775002624 140737105124880 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_clone_fork_012_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551605 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_clone_fork_012_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_clone_fork_012_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_clone_fork_012_s0_call row_clone_fork_012_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_clone_fork_012_s0_answer : outcome SyscallEffect :=
  answer_at row_clone_fork_012_s0_state row_clone_fork_012_s0_effect

/-- The recorded answer as a value: `errno_ret EAGAIN`, off a `conform` case.
trace: clone_fork/012 -/
example :
    row_clone_fork_012_s0_effect.eff_ret = errno_ret EAGAIN
      ∧ row_clone_fork_012_s0_conform = true := by decide

/-- The fold has a model, so `row_clone_fork_012_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_clone_fork_012_s0_state.isSome = true := by rfl

/-- `errno_mmap/001#0`: mmap(0, 4096, 3, 34, 18446744073709551615, 0) -- the
record carries `errno_ret ENOMEM`, and the checker's verdict on the pair
was `ok`.

Recorded 2026-09-16 in `testing/syscall-check/traces/errno_mmap/001.jsonl`
under case `conform --mutate mmap:ret=-ENOMEM,drop-zeros -- mmap # mmap:
-ENOMEM`. The case staged `--mutate mmap:ret=-ENOMEM,drop-zeros`, so the
answer is the one the checker was shown and not the kernel's own; the case
expects it to be ADMITTED, as an answer some real run could give. -/
def row_errno_mmap_001_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_errno_mmap_001_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 581439488 140736200962048 140737118684352 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_errno_mmap_001_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551604 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_errno_mmap_001_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_errno_mmap_001_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_errno_mmap_001_s0_call row_errno_mmap_001_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_errno_mmap_001_s0_answer : outcome SyscallEffect :=
  answer_at row_errno_mmap_001_s0_state row_errno_mmap_001_s0_effect

/-- The recorded answer as a value: `errno_ret ENOMEM`, off a `conform` case.
trace: errno_mmap/001 -/
example :
    row_errno_mmap_001_s0_effect.eff_ret = errno_ret ENOMEM
      ∧ row_errno_mmap_001_s0_conform = true := by decide

/-- The fold has a model, so `row_errno_mmap_001_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_errno_mmap_001_s0_state.isSome = true := by rfl

/-- `errno_mmap/002#0`: mmap(0, 4096, 3, 34, 18446744073709551615, 0) -- the
record carries `errno_ret EBADF`, and the checker's verdict on the pair
was `reject`.

Recorded 2026-09-16 in `testing/syscall-check/traces/errno_mmap/002.jsonl`
under case `reject --mutate mmap:ret=-EBADF,drop-zeros -- mmap # mmap:
-EBADF (no fd is involved)`. The case staged `--mutate
mmap:ret=-EBADF,drop-zeros`, so the answer is the one the checker was
shown and not the kernel's own; the case expects it to be REFUSED. -/
def row_errno_mmap_002_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_errno_mmap_002_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 15839232 140735954702336 140736755132000 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_errno_mmap_002_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551607 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_errno_mmap_002_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_errno_mmap_002_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_errno_mmap_002_s0_call row_errno_mmap_002_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_errno_mmap_002_s0_answer : outcome SyscallEffect :=
  answer_at row_errno_mmap_002_s0_state row_errno_mmap_002_s0_effect

/-- The recorded answer as a value: `errno_ret EBADF`, off a `reject` case.
trace: errno_mmap/002 -/
example :
    row_errno_mmap_002_s0_effect.eff_ret = errno_ret EBADF
      ∧ row_errno_mmap_002_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_errno_mmap_002_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_errno_mmap_002_s0_state.isSome = true := by rfl

/-- `errno_mmap/003#0`: mmap(0, 4096, 3, 34, 18446744073709551615, 0) -- the
record carries `errno_ret EACCES`, and the checker's verdict on the pair
was `reject`.

Recorded 2026-09-16 in `testing/syscall-check/traces/errno_mmap/003.jsonl`
under case `reject --mutate mmap:ret=-EACCES,drop-zeros -- mmap # mmap:
-EACCES (real for openat, not mmap)`. The case staged `--mutate
mmap:ret=-EACCES,drop-zeros`, so the answer is the one the checker was
shown and not the kernel's own; the case expects it to be REFUSED. -/
def row_errno_mmap_003_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_errno_mmap_003_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 1005731840 140735617892352 140737416192896 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_errno_mmap_003_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551603 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_errno_mmap_003_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_errno_mmap_003_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_errno_mmap_003_s0_call row_errno_mmap_003_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_errno_mmap_003_s0_answer : outcome SyscallEffect :=
  answer_at row_errno_mmap_003_s0_state row_errno_mmap_003_s0_effect

/-- The recorded answer as a value: `errno_ret EACCES`, off a `reject` case.
trace: errno_mmap/003 -/
example :
    row_errno_mmap_003_s0_effect.eff_ret = errno_ret EACCES
      ∧ row_errno_mmap_003_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_errno_mmap_003_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_errno_mmap_003_s0_state.isSome = true := by rfl

/-- `mmap_budget/009#3`: mmap(0, 35184372088832, 3, 16418,
18446744073709551615, 0) -- the kernel answered `errno_ret ENOMEM`, and
the checker's verdict on the pair was `ok`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_budget/009.jsonl` under case `conform
--alloc-limit 0x10000 -- exhaust # real -ENOMEM at TASK_SIZE: three 32 TiB
NORESERVE grants fit below a top-down mmap_base under 2^47, the fourth has
no gap (mm/mmap.c get_unmapped_area, v6.18.46). NULL-hint grants are
placed under the run's stack, State.alloc_top`. -/
def row_mmap_budget_009_s3_call : SyscallInput := SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 3 record(s) before `seq 3`. -/
def row_mmap_budget_009_s3_state : Option Model :=
  oracle_fold (init_model [(65536, 8192)] 550641664 140735770521600 140736507602496 65536
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 105551398432768 [] [(105551398432768, 35184372088832)] [] [] []),
     (SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 70367026343936 [] [(70367026343936, 35184372088832)] [] [] []),
     (SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 35182654255104 [] [(35182654255104, 35184372088832)] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_budget_009_s3_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551604 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_budget_009_s3_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_budget_009_s3_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_budget_009_s3_call row_mmap_budget_009_s3_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_budget_009_s3_answer : outcome SyscallEffect :=
  answer_at row_mmap_budget_009_s3_state row_mmap_budget_009_s3_effect

/-- The recorded answer as a value: `errno_ret ENOMEM`, off a `conform` case.
trace: mmap_budget/009 -/
example :
    row_mmap_budget_009_s3_effect.eff_ret = errno_ret ENOMEM
      ∧ row_mmap_budget_009_s3_conform = true := by decide

/-- The fold has a model, so `row_mmap_budget_009_s3_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 3 record(s) before seq 3 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_budget_009_s3_state.isSome = true := by rfl

/-- `mmap_budget/010#3`: mmap(0, 35184372088832, 3, 16418,
18446744073709551615, 0) -- the record carries `17592186044416`, and the
checker's verdict on the pair was `reject`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_budget/010.jsonl` under case `reject
--alloc-limit 0x10000 --mutate mmap#4:ret=0x100000000000 -- exhaust # a
kernel that found a fourth 32 TiB gap where none exists`. The case staged
`--mutate mmap#4:ret=0x100000000000`, so the answer is the one the checker
was shown and not the kernel's own; the case expects it to be REFUSED. -/
def row_mmap_budget_010_s3_call : SyscallInput := SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 3 record(s) before `seq 3`. -/
def row_mmap_budget_010_s3_state : Option Model :=
  oracle_fold (init_model [(65536, 8192)] 45895680 140735940165632 140737434026736 65536
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 105551568076800 [] [(105551568076800, 35184372088832)] [] [] []),
     (SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 70367195987968 [] [(70367195987968, 35184372088832)] [] [] []),
     (SyscallInput.mkInput 222 [0, 35184372088832, 3, 16418, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 35182823899136 [] [(35182823899136, 35184372088832)] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_budget_010_s3_effect : SyscallEffect := SyscallEffect.mkEffectU 17592186044416 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_budget_010_s3_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_budget_010_s3_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_budget_010_s3_call row_mmap_budget_010_s3_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_budget_010_s3_answer : outcome SyscallEffect :=
  answer_at row_mmap_budget_010_s3_state row_mmap_budget_010_s3_effect

/-- The recorded answer as a value: `17592186044416`, off a `reject` case.
trace: mmap_budget/010 -/
example :
    row_mmap_budget_010_s3_effect.eff_ret = 17592186044416
      ∧ row_mmap_budget_010_s3_conform ≠ true := by decide

/-- The fold has a model, so `row_mmap_budget_010_s3_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 3 record(s) before seq 3 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_budget_010_s3_state.isSome = true := by rfl

/-- `mmap_file_backed/002#0`: mmap(0, 4096, 1, 2, 999, 1) -- the kernel
answered `errno_ret EINVAL`, and the checker's verdict on the pair was
`ok`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_file_backed/002.jsonl` under case
`conform -- misaligned # a misaligned offset is -EINVAL, decided before
the fd`. -/
def row_mmap_file_backed_002_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 1, 2, 999, 1] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_mmap_file_backed_002_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 747712512 140736219512832 140736605979968 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_file_backed_002_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551594 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_file_backed_002_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_file_backed_002_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_file_backed_002_s0_call row_mmap_file_backed_002_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_file_backed_002_s0_answer : outcome SyscallEffect :=
  answer_at row_mmap_file_backed_002_s0_state row_mmap_file_backed_002_s0_effect

/-- The recorded answer as a value: `errno_ret EINVAL`, off a `conform` case.
trace: mmap_file_backed/002 -/
example :
    row_mmap_file_backed_002_s0_effect.eff_ret = errno_ret EINVAL
      ∧ row_mmap_file_backed_002_s0_conform = true := by decide

/-- The fold has a model, so `row_mmap_file_backed_002_s0_holds` is the
dispatcher applied to it and not the `False` `spec_at`'s `none` arm
answers -- which is what a NEGATIVE pin over this row needs, since `¬
False` closes having said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_file_backed_002_s0_state.isSome = true := by rfl

/-- `mmap_file_backed/003#0`: mmap(0, 4096, 1, 2, 999, 1) -- the record
carries `errno_ret EBADF`, and the checker's verdict on the pair was
`reject`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_file_backed/003.jsonl` under case
`reject --mutate mmap:ret=-EBADF -- misaligned # ...so the closed fd's
-EBADF does not get to answer`. The case staged `--mutate
mmap:ret=-EBADF`, so the answer is the one the checker was shown and not
the kernel's own; the case expects it to be REFUSED. -/
def row_mmap_file_backed_003_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 1, 2, 999, 1] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_mmap_file_backed_003_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 378531840 140736161026048 140736700708336 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_file_backed_003_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551607 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_file_backed_003_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_file_backed_003_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_file_backed_003_s0_call row_mmap_file_backed_003_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_file_backed_003_s0_answer : outcome SyscallEffect :=
  answer_at row_mmap_file_backed_003_s0_state row_mmap_file_backed_003_s0_effect

/-- The recorded answer as a value: `errno_ret EBADF`, off a `reject` case.
trace: mmap_file_backed/003 -/
example :
    row_mmap_file_backed_003_s0_effect.eff_ret = errno_ret EBADF
      ∧ row_mmap_file_backed_003_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_mmap_file_backed_003_s0_holds` is the
dispatcher applied to it and not the `False` `spec_at`'s `none` arm
answers -- which is what a NEGATIVE pin over this row needs, since `¬
False` closes having said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_file_backed_003_s0_state.isSome = true := by rfl

/-- `mmap_file_backed/004#0`: mmap(0, 4096, 1, 2, 999, 1) -- the record
carries `errno_ret ENOMEM`, and the checker's verdict on the pair was
`reject`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_file_backed/004.jsonl` under case
`reject --mutate mmap:ret=-ENOMEM -- misaligned # ...and neither does the
environment errno the anonymous shapes [a word the Lean policy gate
refuses in source, elided; read the case in the trace file named above]`.
The case staged `--mutate mmap:ret=-ENOMEM`, so the answer is the one the
checker was shown and not the kernel's own; the case expects it to be
REFUSED. -/
def row_mmap_file_backed_004_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 1, 2, 999, 1] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_mmap_file_backed_004_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 289976320 140736004005888 140736952825152 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_file_backed_004_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551604 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_file_backed_004_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_file_backed_004_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_file_backed_004_s0_call row_mmap_file_backed_004_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_file_backed_004_s0_answer : outcome SyscallEffect :=
  answer_at row_mmap_file_backed_004_s0_state row_mmap_file_backed_004_s0_effect

/-- The recorded answer as a value: `errno_ret ENOMEM`, off a `reject` case.
trace: mmap_file_backed/004 -/
example :
    row_mmap_file_backed_004_s0_effect.eff_ret = errno_ret ENOMEM
      ∧ row_mmap_file_backed_004_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_mmap_file_backed_004_s0_holds` is the
dispatcher applied to it and not the `False` `spec_at`'s `none` arm
answers -- which is what a NEGATIVE pin over this row needs, since `¬
False` closes having said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_file_backed_004_s0_state.isSome = true := by rfl

/-- `mmap_file_backed/005#0`: mmap(0, 4096, 3, 34, 18446744073709551615, 1) --
the kernel answered `errno_ret EINVAL`, and the checker's verdict on the
pair was `ok`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_file_backed/005.jsonl` under case
`conform -- anon-misaligned # and the same gate applies to the plain
anonymous rw shape`. -/
def row_mmap_file_backed_005_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 1] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_mmap_file_backed_005_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 613683200 140735423815680 140737284398144 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_file_backed_005_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551594 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_file_backed_005_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_file_backed_005_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_file_backed_005_s0_call row_mmap_file_backed_005_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_file_backed_005_s0_answer : outcome SyscallEffect :=
  answer_at row_mmap_file_backed_005_s0_state row_mmap_file_backed_005_s0_effect

/-- The recorded answer as a value: `errno_ret EINVAL`, off a `conform` case.
trace: mmap_file_backed/005 -/
example :
    row_mmap_file_backed_005_s0_effect.eff_ret = errno_ret EINVAL
      ∧ row_mmap_file_backed_005_s0_conform = true := by decide

/-- The fold has a model, so `row_mmap_file_backed_005_s0_holds` is the
dispatcher applied to it and not the `False` `spec_at`'s `none` arm
answers -- which is what a NEGATIVE pin over this row needs, since `¬
False` closes having said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_file_backed_005_s0_state.isSome = true := by rfl

/-- `mmap_file_backed/006#0`: mmap(0, 4096, 3, 34, 18446744073709551615, 1) --
the record carries `1073741824`, and the checker's verdict on the pair was
`reject`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_file_backed/006.jsonl` under case
`reject --mutate mmap:ret=0x40000000 -- anon-misaligned # ...which
therefore places nothing`. The case staged `--mutate mmap:ret=0x40000000`,
so the answer is the one the checker was shown and not the kernel's own;
the case expects it to be REFUSED. -/
def row_mmap_file_backed_006_s0_call : SyscallInput := SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 1] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_mmap_file_backed_006_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096)] 926633984 140736232914944 140737353784800 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_file_backed_006_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 1073741824 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_file_backed_006_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_file_backed_006_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_file_backed_006_s0_call row_mmap_file_backed_006_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_file_backed_006_s0_answer : outcome SyscallEffect :=
  answer_at row_mmap_file_backed_006_s0_state row_mmap_file_backed_006_s0_effect

/-- The recorded answer as a value: `1073741824`, off a `reject` case.
trace: mmap_file_backed/006 -/
example :
    row_mmap_file_backed_006_s0_effect.eff_ret = 1073741824
      ∧ row_mmap_file_backed_006_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_mmap_file_backed_006_s0_holds` is the
dispatcher applied to it and not the `False` `spec_at`'s `none` arm
answers -- which is what a NEGATIVE pin over this row needs, since `¬
False` closes having said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_file_backed_006_s0_state.isSome = true := by rfl

/-- `mmap_shapes/001#1`: mmap(0, 0, 3, 34, 18446744073709551615, 0) -- the
kernel answered `errno_ret EINVAL`, and the checker's verdict on the pair
was `ok`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_shapes/001.jsonl` under case `conform
-- ok # the modeled shape, plus len=0 answering -EINVAL`. -/
def row_mmap_shapes_001_s1_call : SyscallInput := SyscallInput.mkInput 222 [0, 0, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_mmap_shapes_001_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 8192)] 866889728 140736325091328 140736593256416 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 140736325087232 [] [(140736325087232, 4096)] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_shapes_001_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551594 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_shapes_001_s1_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_shapes_001_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_shapes_001_s1_call row_mmap_shapes_001_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_shapes_001_s1_answer : outcome SyscallEffect :=
  answer_at row_mmap_shapes_001_s1_state row_mmap_shapes_001_s1_effect

/-- The recorded answer as a value: `errno_ret EINVAL`, off a `conform` case.
trace: mmap_shapes/001 -/
example :
    row_mmap_shapes_001_s1_effect.eff_ret = errno_ret EINVAL
      ∧ row_mmap_shapes_001_s1_conform = true := by decide

/-- The fold has a model, so `row_mmap_shapes_001_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_shapes_001_s1_state.isSome = true := by rfl

/-- `mmap_shapes/002#1`: mmap(0, 0, 3, 34, 18446744073709551615, 0) -- the
record carries `0`, and the checker's verdict on the pair was `reject`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_shapes/002.jsonl` under case `reject
--mutate mmap#2:ret=0 -- ok # mmap's zero length admits only -EINVAL`. The
case staged `--mutate mmap#2:ret=0`, so the answer is the one the checker
was shown and not the kernel's own; the case expects it to be REFUSED. -/
def row_mmap_shapes_002_s1_call : SyscallInput := SyscallInput.mkInput 222 [0, 0, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_mmap_shapes_002_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 8192)] 72105984 140736166440960 140737256458864 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 140736166436864 [] [(140736166436864, 4096)] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_shapes_002_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 0 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_shapes_002_s1_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_shapes_002_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_shapes_002_s1_call row_mmap_shapes_002_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_shapes_002_s1_answer : outcome SyscallEffect :=
  answer_at row_mmap_shapes_002_s1_state row_mmap_shapes_002_s1_effect

/-- The recorded answer as a value: `0`, off a `reject` case.
trace: mmap_shapes/002 -/
example :
    row_mmap_shapes_002_s1_effect.eff_ret = 0
      ∧ row_mmap_shapes_002_s1_conform ≠ true := by decide

/-- The fold has a model, so `row_mmap_shapes_002_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_shapes_002_s1_state.isSome = true := by rfl

/-- `mmap_shapes/003#1`: mmap(0, 0, 3, 34, 18446744073709551615, 0) -- the
record carries `errno_ret ENOMEM`, and the checker's verdict on the pair
was `reject`.

Recorded 2026-09-16 in
`testing/syscall-check/traces/mmap_shapes/003.jsonl` under case `reject
--mutate mmap#2:ret=-ENOMEM -- ok # ...and no other errno: the length gate
precedes errno_from`. The case staged `--mutate mmap#2:ret=-ENOMEM`, so
the answer is the one the checker was shown and not the kernel's own; the
case expects it to be REFUSED. -/
def row_mmap_shapes_003_s1_call : SyscallInput := SyscallInput.mkInput 222 [0, 0, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_mmap_shapes_003_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 8192)] 774344704 140736326832128 140737478232640 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 222 [0, 4096, 3, 34, 18446744073709551615, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 140736326828032 [] [(140736326828032, 4096)] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_mmap_shapes_003_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551604 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_mmap_shapes_003_s1_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_mmap_shapes_003_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_mmap_shapes_003_s1_call row_mmap_shapes_003_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_mmap_shapes_003_s1_answer : outcome SyscallEffect :=
  answer_at row_mmap_shapes_003_s1_state row_mmap_shapes_003_s1_effect

/-- The recorded answer as a value: `errno_ret ENOMEM`, off a `reject` case.
trace: mmap_shapes/003 -/
example :
    row_mmap_shapes_003_s1_effect.eff_ret = errno_ret ENOMEM
      ∧ row_mmap_shapes_003_s1_conform ≠ true := by decide

/-- The fold has a model, so `row_mmap_shapes_003_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_mmap_shapes_003_s1_state.isSome = true := by rfl

/-- `set_tid/001#0`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the kernel
answered `33`, and the checker's verdict on the pair was `ok`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/001.jsonl`
under case `conform -- one # first call pins the kernel's real tid`. -/
def row_set_tid_001_s0_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_set_tid_001_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 985985024 140735379660800 140737395861520 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_001_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 33 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_001_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_001_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_001_s0_call row_set_tid_001_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_001_s0_answer : outcome SyscallEffect :=
  answer_at row_set_tid_001_s0_state row_set_tid_001_s0_effect

/-- The recorded answer as a value: `33`, off a `conform` case.
trace: set_tid/001 -/
example :
    row_set_tid_001_s0_effect.eff_ret = 33
      ∧ row_set_tid_001_s0_conform = true := by decide

/-- The fold has a model, so `row_set_tid_001_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_001_s0_state.isSome = true := by rfl

/-- `set_tid/004#0`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the record
carries `0`, and the checker's verdict on the pair was `reject`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/004.jsonl`
under case `reject --mutate set_tid_address:ret=0 -- one # tids are
positive`. The case staged `--mutate set_tid_address:ret=0`, so the answer
is the one the checker was shown and not the kernel's own; the case
expects it to be REFUSED. -/
def row_set_tid_004_s0_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_set_tid_004_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 316350464 140735783878656 140736747315616 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_004_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 0 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_004_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_004_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_004_s0_call row_set_tid_004_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_004_s0_answer : outcome SyscallEffect :=
  answer_at row_set_tid_004_s0_state row_set_tid_004_s0_effect

/-- The recorded answer as a value: `0`, off a `reject` case.
trace: set_tid/004 -/
example :
    row_set_tid_004_s0_effect.eff_ret = 0
      ∧ row_set_tid_004_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_set_tid_004_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_004_s0_state.isSome = true := by rfl

/-- `set_tid/005#0`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the record
carries `4194304`, and the checker's verdict on the pair was `reject`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/005.jsonl`
under case `reject --mutate set_tid_address:ret=4194304 -- one # the
modeled envelope is exclusive`. The case staged `--mutate
set_tid_address:ret=4194304`, so the answer is the one the checker was
shown and not the kernel's own; the case expects it to be REFUSED. -/
def row_set_tid_005_s0_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_set_tid_005_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 685473792 140736260898816 140737048112848 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_005_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 4194304 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_005_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_005_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_005_s0_call row_set_tid_005_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_005_s0_answer : outcome SyscallEffect :=
  answer_at row_set_tid_005_s0_state row_set_tid_005_s0_effect

/-- The recorded answer as a value: `4194304`, off a `reject` case.
trace: set_tid/005 -/
example :
    row_set_tid_005_s0_effect.eff_ret = 4194304
      ∧ row_set_tid_005_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_set_tid_005_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_005_s0_state.isSome = true := by rfl

/-- `set_tid/009#0`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the record
carries `errno_ret EINVAL`, and the checker's verdict on the pair was
`reject`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/009.jsonl`
under case `reject --mutate set_tid_address:ret=-EINVAL -- one # >= 2^22
as u64; set_tid_address has no error path`. The case staged `--mutate
set_tid_address:ret=-EINVAL`, so the answer is the one the checker was
shown and not the kernel's own; the case expects it to be REFUSED. -/
def row_set_tid_009_s0_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_set_tid_009_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 502829056 140735821021184 140736488547776 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_009_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 18446744073709551594 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_009_s0_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_009_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_009_s0_call row_set_tid_009_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_009_s0_answer : outcome SyscallEffect :=
  answer_at row_set_tid_009_s0_state row_set_tid_009_s0_effect

/-- The recorded answer as a value: `errno_ret EINVAL`, off a `reject` case.
trace: set_tid/009 -/
example :
    row_set_tid_009_s0_effect.eff_ret = errno_ret EINVAL
      ∧ row_set_tid_009_s0_conform ≠ true := by decide

/-- The fold has a model, so `row_set_tid_009_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_009_s0_state.isSome = true := by rfl

/-- `set_tid/010#0`: set_tid_address(0, 0, 0, 0, 0, 0) -- the kernel answered
`43`, and the checker's verdict on the pair was `ok`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/010.jsonl`
under case `conform -- null # first call with tidptr = NULL (address
ignored)`. -/
def row_set_tid_010_s0_call : SyscallInput := SyscallInput.mkInput 96 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_set_tid_010_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 597618688 140735391203328 140737326716720 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_010_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 43 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_010_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_010_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_010_s0_call row_set_tid_010_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_010_s0_answer : outcome SyscallEffect :=
  answer_at row_set_tid_010_s0_state row_set_tid_010_s0_effect

/-- The recorded answer as a value: `43`, off a `conform` case.
trace: set_tid/010 -/
example :
    row_set_tid_010_s0_effect.eff_ret = 43
      ∧ row_set_tid_010_s0_conform = true := by decide

/-- The fold has a model, so `row_set_tid_010_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_010_s0_state.isSome = true := by rfl

/-- `set_tid/017#0`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the kernel
answered `50`, and the checker's verdict on the pair was `ok`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/017.jsonl`
under case `conform -- two # second call repeats the pinned tid`. -/
def row_set_tid_017_s0_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_set_tid_017_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 68931584 140735658541056 140736970114736 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_017_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 50 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_017_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_017_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_017_s0_call row_set_tid_017_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_017_s0_answer : outcome SyscallEffect :=
  answer_at row_set_tid_017_s0_state row_set_tid_017_s0_effect

/-- The recorded answer as a value: `50`, off a `conform` case.
trace: set_tid/017 -/
example :
    row_set_tid_017_s0_effect.eff_ret = 50
      ∧ row_set_tid_017_s0_conform = true := by decide

/-- The fold has a model, so `row_set_tid_017_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_017_s0_state.isSome = true := by rfl

/-- `set_tid/017#1`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the kernel
answered `50`, and the checker's verdict on the pair was `ok`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/017.jsonl`
under case `conform -- two # second call repeats the pinned tid`. -/
def row_set_tid_017_s1_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_set_tid_017_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 68931584 140735658541056 140736970114736 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 50 [] [] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_017_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 50 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_017_s1_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_017_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_017_s1_call row_set_tid_017_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_017_s1_answer : outcome SyscallEffect :=
  answer_at row_set_tid_017_s1_state row_set_tid_017_s1_effect

/-- The recorded answer as a value: `50`, off a `conform` case.
trace: set_tid/017 -/
example :
    row_set_tid_017_s1_effect.eff_ret = 50
      ∧ row_set_tid_017_s1_conform = true := by decide

/-- The fold has a model, so `row_set_tid_017_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_017_s1_state.isSome = true := by rfl

/-- `set_tid/018#1`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the record
carries `52`, and the checker's verdict on the pair was `reject`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/018.jsonl`
under case `reject --mutate set_tid_address#2:ret+1 -- two # second call
with a DIFFERENT tid (the original bug)`. The case staged `--mutate
set_tid_address#2:ret+1`, so the answer is the one the checker was shown
and not the kernel's own; the case expects it to be REFUSED. -/
def row_set_tid_018_s1_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_set_tid_018_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 705687552 140735724478464 140736702211872 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 51 [] [] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_018_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 52 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_018_s1_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_018_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_018_s1_call row_set_tid_018_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_018_s1_answer : outcome SyscallEffect :=
  answer_at row_set_tid_018_s1_state row_set_tid_018_s1_effect

/-- The recorded answer as a value: `52`, off a `reject` case.
trace: set_tid/018 -/
example :
    row_set_tid_018_s1_effect.eff_ret = 52
      ∧ row_set_tid_018_s1_conform ≠ true := by decide

/-- The fold has a model, so `row_set_tid_018_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_018_s1_state.isSome = true := by rfl

/-- `set_tid/023#0`: set_tid_address(69640, 0, 0, 0, 0, 0) -- the kernel
answered `56`, and the checker's verdict on the pair was `ok`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/023.jsonl`
under case `conform -- two-ptr # second call with a different tidptr, same
tid`. -/
def row_set_tid_023_s0_call : SyscallInput := SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 0 record(s) before `seq 0`. -/
def row_set_tid_023_s0_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 111251456 140735854919680 140736862345056 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48)) []

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_023_s0_effect : SyscallEffect := SyscallEffect.mkEffectU 56 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_023_s0_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_023_s0_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_023_s0_call row_set_tid_023_s0_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_023_s0_answer : outcome SyscallEffect :=
  answer_at row_set_tid_023_s0_state row_set_tid_023_s0_effect

/-- The recorded answer as a value: `56`, off a `conform` case.
trace: set_tid/023 -/
example :
    row_set_tid_023_s0_effect.eff_ret = 56
      ∧ row_set_tid_023_s0_conform = true := by decide

/-- The fold has a model, so `row_set_tid_023_s0_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 0 record(s) before seq 0 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_023_s0_state.isSome = true := by rfl

/-- `set_tid/023#1`: set_tid_address(69632, 0, 0, 0, 0, 0) -- the kernel
answered `56`, and the checker's verdict on the pair was `ok`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/023.jsonl`
under case `conform -- two-ptr # second call with a different tidptr, same
tid`. -/
def row_set_tid_023_s1_call : SyscallInput := SyscallInput.mkInput 96 [69632, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_set_tid_023_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 111251456 140735854919680 140736862345056 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 56 [] [] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_023_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 56 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_023_s1_conform : Bool := true

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_023_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_023_s1_call row_set_tid_023_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_023_s1_answer : outcome SyscallEffect :=
  answer_at row_set_tid_023_s1_state row_set_tid_023_s1_effect

/-- The recorded answer as a value: `56`, off a `conform` case.
trace: set_tid/023 -/
example :
    row_set_tid_023_s1_effect.eff_ret = 56
      ∧ row_set_tid_023_s1_conform = true := by decide

/-- The fold has a model, so `row_set_tid_023_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_023_s1_state.isSome = true := by rfl

/-- `set_tid/024#1`: set_tid_address(69632, 0, 0, 0, 0, 0) -- the record
carries `2`, and the checker's verdict on the pair was `reject`.

Recorded 2026-10-25 in `testing/syscall-check/traces/set_tid/024.jsonl`
under case `reject --mutate set_tid_address#1:ret=1 --mutate
set_tid_address#2:ret=2 -- two-ptr # a different tidptr does not start a
new pin`. The case staged `--mutate set_tid_address#2:ret=2`, so the
answer is the one the checker was shown and not the kernel's own; the case
expects it to be REFUSED. -/
def row_set_tid_024_s1_call : SyscallInput := SyscallInput.mkInput 96 [69632, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The state the answer was given in: the trace's header through `init_model`,
folded over the 1 record(s) before `seq 1`. -/
def row_set_tid_024_s1_state : Option Model :=
  oracle_fold (init_model [(65536, 4096), (69632, 4096)] 498876416 140736338616320 140737457472112 549755813888
      (oracle_input 1000 1000 [] 1024 0 4397 false .Sv48))
    [(SyscallInput.mkInput 96 [69640, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none),
       SyscallEffect.mkEffectU 1 [] [] [] [] [])]

/-- What the kernel did, the case's `--mutate` applied. -/
def row_set_tid_024_s1_effect : SyscallEffect := SyscallEffect.mkEffectU 2 [] [] [] [] []

/-- Whether the run was graded `conform`: the case's answer -- the kernel's own, or the one its `--mutate` staged -- admitted.
`false` where the case stages an answer to be REFUSED (`reject`) or a
shape the model declines (`fail-closed`), which is what
`tools/check_lean_pin_evidence.py`'s POLARITY rule holds a pin citing this
trace to. -/
def row_set_tid_024_s1_conform : Bool := false

/-- The recorded call in the recorded state, put to the dispatcher. -/
@[sys_simp] def row_set_tid_024_s1_holds (o : outcome SyscallEffect) : Prop :=
  spec_at row_set_tid_024_s1_call row_set_tid_024_s1_state o

/-- The recorded answer as an outcome in that state. -/
@[sys_simp] def row_set_tid_024_s1_answer : outcome SyscallEffect :=
  answer_at row_set_tid_024_s1_state row_set_tid_024_s1_effect

/-- The recorded answer as a value: `2`, off a `reject` case.
trace: set_tid/024 -/
example :
    row_set_tid_024_s1_effect.eff_ret = 2
      ∧ row_set_tid_024_s1_conform ≠ true := by decide

/-- The fold has a model, so `row_set_tid_024_s1_holds` is the dispatcher
applied to it and not the `False` `spec_at`'s `none` arm answers -- which
is what a NEGATIVE pin over this row needs, since `¬ False` closes having
said nothing.
model: the Lean checker admits the 1 record(s) before seq 1 of this trace;
a closed computation over the model's own definitions, and no claim about
Linux -/
example : row_set_tid_024_s1_state.isSome = true := by rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Oracle
