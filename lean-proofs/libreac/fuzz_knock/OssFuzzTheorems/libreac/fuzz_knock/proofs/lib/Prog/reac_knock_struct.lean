-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_struct.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step

/-! `lib/Prog/reac_knock_struct.v`: `struct reac_knock` as the proof reads it.

This file is `L_NS` and `knock_cells`, and nothing else: it carries no theorem.

The two Rocq lemmas of `reac_knock_struct.v` — `knock_sx32_unsigned`
(`lib/Prog/reac_knock_struct.v:12-28`) and `knock_sx32_eqb`
(`lib/Prog/reac_knock_struct.v:30-36`) — turn the sign-extended `lw` result
into a `Z.eqb` on the stored integer. They rest on stdpp's `bv_swrap` lemma
set, which the Lean port does not carry (OSSV-265 gaps row T-12). The Lean
port proves both from its own `Int` arithmetic, as `private theorem`s of the
two walks that use them: `proofs/lib/Prog/reac_knock_step.lean`, under its
heading "The two lemmas of `lib/Prog/reac_knock_struct.v`", and
`proofs/lib/Prog/reac_knock_heard.lean`. They are private in both on purpose:
this file is the shared vocabulary, and the agent-hours table credits the
function proofs that paid for the two lemmas. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct

open LinuxProcessSemantics.Riscv.Prelude
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells (cell)

/-- `lib/Prog/reac_knock_struct.v:7`: `REAC_KNOCK_LISTEN_NS`. -/
def L_NS : Int := 500000000

/-- `lib/Prog/reac_knock_struct.v:9-10`: the seven fields of
`struct reac_knock` as the proof reads them. -/
def knock_cells (st : Int) (p1 opened due heard : word) (g : Int) (p2 : word)
    : List cell :=
  [.C4 (Z_to_bv 64 st), .C4 p1, .C8 opened, .C8 due, .C8 heard,
   .C4 (Z_to_bv 64 g), .C4 p2]

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct
