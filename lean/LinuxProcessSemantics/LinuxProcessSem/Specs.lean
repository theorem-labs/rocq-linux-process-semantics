import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable

/-! # LinuxProcessSem.Specs — the dispatcher

Mirrors `theories/LinuxProcessSem/Specs.v`.  The Rocq header carries the
modeling priority (sound, then reject impossible traces, then complete),
the representation rules, the FAIL CLOSED convention, and the map from
each `Sys/` file to the kernel source file it answers to.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Specs

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable

/-- The syscall numbers this model covers, read off the table so the two
cannot drift. -/
def modeled_sysnos : List Int := arm_numbers spec_table

/-- Dispatch on the unsigned syscall number; every number outside
`modeled_sysnos` is `unmodeled`. -/
def syscall_spec : Sys SyscallEffect := dispatch spec_table

end LinuxProcessSemantics.LinuxProcessSem.Specs
