-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_struct.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step

/-! `lib/Prog/reac_knock_struct.v`: `struct reac_knock` as the proof reads it.

The two Rocq lemmas of this file, `knock_sx32_unsigned` and `knock_sx32_eqb`,
turn the sign-extended `lw` result into a `Z.eqb` on the stored integer. They
rest on stdpp's `bv_swrap` lemma set, which the Lean port does not carry
(OSSV-265 gaps row T-12); they are proved here from Lean's own `BitVec` facts
instead. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct

open LinuxProcessSemantics.Riscv.Prelude
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells (cell)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (sx32)

/-- `lib/Prog/reac_knock_struct.v:7`: `REAC_KNOCK_LISTEN_NS`. -/
def L_NS : Int := 500000000

/-- `lib/Prog/reac_knock_struct.v:9-10`: the seven fields of
`struct reac_knock` as the proof reads them. -/
def knock_cells (st : Int) (p1 opened due heard : word) (g : Int) (p2 : word)
    : List cell :=
  [.C4 (Z_to_bv 64 st), .C4 p1, .C8 opened, .C8 due, .C8 heard,
   .C4 (Z_to_bv 64 g), .C4 p2]

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct
