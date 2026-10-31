-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Lib/Mem.v
import LinuxProcessSemantics.Common.PropExec

/-! `lib/Lib/Mem.v`: the memory vocabulary the function contracts are stated in.

Only the declarations the ported contracts of `lib/Prog/` are stated in are
here: eleven of the Rocq file's 21 definitions, and none of its 64 lemmas. The
Rocq file is 594 lines, most of them the reading and writing lemmas that join
`mrd`, `bytes_at` and `wr_at` (`bytes_at_rdn` at `lib/Lib/Mem.v:89-103`,
`bytes_at_read` at `:112-119`, `wr_at_store_ok` at `:125-135`, and so on).
Those lemmas have NO Lean twin, and neither has the vocabulary they are about:
a grep of the Lean port's `LinuxProcessSemantics/Common/` for `bytes_at`,
`wr_at`, `mrd`, `ro_addr`, `mem_inv`, `ro_bytes` and `upd_bytes` returns
nothing (OSSV-265 gaps row T-8: the symbols of our Rocq `proofs/lib/Lib/` have
no Lean name at all). The model's own reader is `Common.PropExec.rdn`, whose
lemmas are about the model's `wbytes` and overlay, not about these predicates.
That is why each ported contract takes the read it needs as a HYPOTHESIS where
the Rocq contract derives it from `rw_cells` (OSSV-265 gaps row T-11).

Each declaration names the Rocq line it is translated from. First written for
OSSV-265 slice T (`probe/ossv265-t/Probe/Defs.lean` of
theorem-labs/oss-verify-proofs-internal, branch `mcsl/lean-convert-probe`
`4054974252`), and parameterised here by the segment list, as Rocq has it. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec

/-- `lib/Lib/Mem.v:20`. -/
def wa (a : Int) : word := Z_to_bv 64 a

/-- `lib/Lib/Mem.v:52-53`: the overlay first, the image behind it. -/
def mrd (segs : List Segment) (m : word → Option byte) (a : word) : Option byte :=
  match m a with
  | some b => some b
  | none => seg_rom segs a

/-- `lib/Lib/Mem.v:389`. -/
def le8 (v : word) : List byte := word_to_le_bytes 8 v

/-- `lib/Lib/Mem.v:390`. -/
def le4 (v : word) : List byte := Z_to_le_bytes 4 (bv_unsigned v)
/-- `lib/Lib/Mem.v:391`. -/
def le2 (v : word) : List byte := Z_to_le_bytes 2 (bv_unsigned v)

/-- `lib/Lib/Mem.v:392`. -/
def le1 (v : word) : List byte := Z_to_le_bytes 1 (bv_unsigned v)

/-- `lib/Lib/Mem.v:75-79`: an address that lies in a loaded segment that is
not writable. -/
def ro_addr (segs : List Segment) (a : word) : Bool :=
  match find_segment segs (bv_unsigned a) 1 with
  | some seg => !(seg_writable seg)
  | none => false

/-- `lib/Lib/Mem.v:82-83`: the overlay never shadows a read-only byte. -/
def mem_inv (segs : List Segment) (m : word → Option byte) : Prop :=
  ∀ a b, m a = some b → ro_addr segs a = false

/-- `lib/Lib/Mem.v:65-67`. -/
def bytes_at (segs : List Segment) (m : word → Option byte) (a : Int)
    (bs : List byte) : Prop :=
  0 ≤ a ∧ a + bs.length ≤ 2 ^ 64 ∧
    ∀ i, i < bs.length → mrd segs m (wa (a + i)) = bs[i]?

/-- `lib/Lib/Mem.v:70-72`. -/
def wr_at (segs : List Segment) (m : word → Option byte) (a : Int) (n : Int) : Prop :=
  0 ≤ a ∧ a + n ≤ 2 ^ 64 ∧
    ∀ i : Int, 0 ≤ i → i < n → wview segs m (wa (a + i)) ≠ none

/-- `lib/Lib/Mem.v:497`: the sign extension an `lw` leaves in the register. -/
def sx32 (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v))

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem
