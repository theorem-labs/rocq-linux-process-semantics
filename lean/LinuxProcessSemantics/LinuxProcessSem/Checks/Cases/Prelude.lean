import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.PreludeCore
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Prelude — `PreludeCore` plus the fixtures that need `Run`

Not part of the trusted specification.  `Checks/Cases/PreludeCore.lean`
holds the fixtures every check file shares and imports no spec; this file
re-exports it, with `Tactic`, and adds the entry-page fixture that reads
`Run.init_machine_state`.  `Run` imports `Specs`, which is why that fixture
does not live in the core: a pin file whose subject is one twin imports
`PreludeCore` and `TacticCore`, and so keeps its mutation cache key at that
twin's own `Sys/` file. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Monad

/-! ## The page the entry stack image ends in

The demo layout, spelled once: argv = ["x"], envp = [], a page-aligned `sp`
so the page boundary above the block is easy to read off.  The block is
what `build_stack_bytes` lays out; the model maps up to the next page
boundary above it (the Rocq `h_sp` note; the entry-page examples are pins
on `Run`, not ported here). -/

def h_sp : word := Z_to_bv 64 65536
def h_block : List byte :=
  build_stack_bytes demo_phdrs h_sp [[Z_to_bv 8 120]] [] demo_uid demo_hwcap demo_draw
def h_mem (draw : EntryDraw) : word → Option byte :=
  (init_machine_state [] 0x10000 demo_phdrs h_sp draw [[Z_to_bv 8 120]] [] demo_uid demo_hwcap).ms_mem

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
