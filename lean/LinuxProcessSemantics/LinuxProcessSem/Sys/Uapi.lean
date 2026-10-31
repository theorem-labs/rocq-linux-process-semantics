import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.Fs
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.Net
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.Sched
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.Time
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.Signal
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.Mm

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uapi — the constants the userspace ABI fixes

Mirrors `theories/LinuxProcessSem/Sys/Uapi.v`, which holds what the
kernel keeps in `include/uapi/` and the specs share rather than any one
syscall's behaviour.  Every other file under `Sys/` answers to one kernel
SOURCE file; this one answers to a kernel HEADER.

THE ONE ROCQ FILE IS SIX LEAN FILES, and this module is only their
re-export.  The split is by subsystem so that a spec PR adds its
constants to the file of its own subsystem and never touches a shared
constants file, which is what G7 (base files frozen during a port wave)
otherwise makes impossible:

- `Uapi/Fs.lean`     — what a file descriptor or a pathname reaches: open,
                        fcntl, flock and lseek words, `AT_` flags, the three
                        shared paths, terminal ioctls, the eventfd and
                        timerfd create masks, getrandom flags, the
                        descriptor-table floor, NAME_MAX, and `struct stat`
                        with its predicates and lemmas;
- `Uapi/Net.lean`    — sockets;
- `Uapi/Sched.lean`  — the task itself: scheduling, clone, futex, wait4,
                        ids and limits, uname, prctl and capabilities;
- `Uapi/Time.lean`   — clock ids, the `ktime_t` bounds, the timespec
                        decoders;
- `Uapi/Signal.lean` — signal sets, `rt_sigprocmask`'s `how`,
                        sigaltstack, SIGABRT;
- `Uapi/Mm.lean`     — mmap, mprotect, mremap and madvise words.

Every definition keeps its Rocq name and lives in this one namespace, so
`open Sys.Uapi` reaches all of them.  No constant is defined in more than
one of the six, and that is not a convention but a compile error: the six
share a namespace and this module imports them all, so a second `def` of
a name Lean already has fails the build.  Parity with `Uapi.v` is a
property of the six together, held to the `rocq-baseline` above: every
Rocq definition of `Uapi.v` has a same-named Lean twin in one of them
(`tools/check_lean_spec_parity.py` reads the six through this file's
imports), and a Rocq lemma left out says why in place, beside the
definition it is about.

Only the twins of Rocq lemmas sit beside the definitions.  The pins — a
value the kernel really has, and beside it the concrete mistake the
constant exists to prevent, refuted — are not part of the trusted
specification and live under `Checks/Cases/Sys/Uapi/`, one file per part,
with the pins that need two parts at once in `Checks/Cases/Sys/Uapi.lean`.

Rocq `Require Export`s `Syscall` from here; the import above keeps that
for anything that reaches `Syscall` through `Uapi`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
