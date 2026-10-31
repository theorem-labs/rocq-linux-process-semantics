-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Lib/Step.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells

/-! `lib/Lib/Step.v`: the read-and-write predicate a contract puts on a C
object.

Only `rw_cells`, the one declaration of this 824-line Rocq file that the
`lib/Prog/` contracts name. The file's reading lemmas (`rw_cells_read` and the
bridge from `rw_cells` to a 4-byte `rdn`) have no Lean twin, so a ported
contract takes the read as a hypothesis (OSSV-265 gaps row T-11). -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (wr_at)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells (cell cells_at cells_size)

/-- `lib/Lib/Step.v:25-26`. -/
def rw_cells (segs : List Segment) (m : word → Option byte) (A : Int)
    (cs : List cell) : Prop :=
  cells_at segs m A cs ∧ wr_at segs m A (cells_size cs)

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step
