import LinuxProcessSemantics.LinuxProcessSem.State.Geometry
import LinuxProcessSemantics.LinuxProcessSem.State.Errno
import LinuxProcessSemantics.LinuxProcessSem.State.Effects
import LinuxProcessSemantics.LinuxProcessSem.State.Readers
import LinuxProcessSemantics.LinuxProcessSem.State.Streams
import LinuxProcessSemantics.LinuxProcessSem.State.Fd
import LinuxProcessSemantics.LinuxProcessSem.State.Pipes
import LinuxProcessSemantics.LinuxProcessSem.State.Vm
import LinuxProcessSemantics.LinuxProcessSem.State.Model
import LinuxProcessSemantics.LinuxProcessSem.State.Backing

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State — the process model

Mirrors `theories/LinuxProcessSem/State.v`: the record layout of `Model`
and its seven subsystems, the syscall input/effect types, the observable
events, the process input, and `init_model`, with the helpers the specs
read.  Every field keeps the Rocq name and type, so a spec ported later
reads the same state the Rocq one does.

THE ONE ROCQ FILE IS TEN LEAN FILES, and this module is only their
re-export.  The split is by subsystem so that a base PR adds its
definitions to the file of its own subsystem and never touches a shared
model file, which is what made every merge into this file a rebase and a
rebuild for every base ticket in flight.  In dependency order:

- `State/Geometry.lean` — the address-space geometry and its constants;
- `State/Errno.lean`    — the errno values;
- `State/Effects.lean`  — syscall inputs and effects;
- `State/Readers.lean`  — reading user memory;
- `State/Streams.lean`  — standard input and the network;
- `State/Fd.lean`       — descriptors and their table;
- `State/Pipes.lean`    — the pipe helpers;
- `State/Vm.lean`       — the virtual-memory ledger;
- `State/Model.lean`    — the seven subsystems and the model;
- `State/Backing.lean`  — the atomic first-access accounting.

Each part's own header says what belongs in it; this list only fixes
the order.

Every definition keeps its Rocq name and lives in this one namespace, so
`open State` reaches all of them.  No definition is made in more than one
part, and that is not a convention but a compile error: the parts share
a namespace and this module imports them all, so a second `def` of a
name Lean already has fails the build.  Parity with `State.v` is a
property of the ten together, held to the `rocq-baseline` above: every
Rocq definition of `State.v` has a same-named Lean twin in one of them
(`tools/check_lean_spec_parity.py` reads the parts through this file's
imports), and a Rocq definition deliberately left out is registered
`unported:` in the header of the part its subsystem belongs to — today
the iovec importers, in `Readers` — never here, so that a register grows
with the part it is about.

A ticket that ports more of `State.v` edits the part of its subsystem, or
adds a part and one import line here; every part is a base file (BRIEF.md
section 4), frozen to port PRs exactly as this file is.

Only the twins of Rocq lemmas sit beside the definitions.  The pins — a
value or a shape the kernel really has, and beside it the concrete mistake
refuted — are not part of the trusted specification and live in
`Checks/Cases/State.lean`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

end LinuxProcessSemantics.LinuxProcessSem.State
