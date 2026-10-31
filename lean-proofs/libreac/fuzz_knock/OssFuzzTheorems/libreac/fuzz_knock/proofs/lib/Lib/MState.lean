-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Lib/MState.v
import LinuxProcessSemantics.Common.PropExec

/-! `lib/Lib/MState.v`: the machine state a function contract is stated over.

Rocq's `MS` builds a `machine_state` with `ms_fregs`, `ms_fcsr` and `ms_resv`
left free; the Lean port's step lemmas are stated over
`LinuxProcessSemantics.Common.PropExec.mkst`, which pins all three
(OSSV-265 gaps row T-6). The contracts below take `mkst`, as OSSV-265 slice T's
probe did.

Only the declarations the `lib/Prog/` contracts name; the Rocq file is 159
lines. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState

open LinuxProcessSemantics.Riscv.Prelude

/-- `lib/Lib/MState.v:140`: a `jalr` target has its low bit cleared.

The Lean library spells the same value `SeqExec.v_jalr ra 0`, and
`PropExec.b_jalr` is the equality between the two shapes (OSSV-265 gaps row
T-9). -/
def ret_pc (ra : word) : word := bv_and ra (bv_not (Z_to_bv 64 1))

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState
