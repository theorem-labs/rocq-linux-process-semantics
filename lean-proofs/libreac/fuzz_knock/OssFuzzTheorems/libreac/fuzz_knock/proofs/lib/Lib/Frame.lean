-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Lib/Frame.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem

/-! `lib/Lib/Frame.v`: what a call may change, and what it may not.

Only the declarations the `lib/Prog/` contracts name; the Rocq file is 245
lines. `mkR`, the 31-register record of `lib/Lib/Frame.v`, has no twin: a Lean
register file is a `bvmap 5 word` read by `getr`, so "only a1 and a2 changed" is
stated as a quantified equation (OSSV-265 gaps row T-10). -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (wa mrd)

/-- `lib/Lib/Frame.v:35`. -/
abbrev ivl := Int × Int

/-- `lib/Lib/Frame.v:37-39`. -/
def outside : List ivl → Int → Prop
  | [], _ => True
  | (lo, hi) :: W, x => (x < lo ∨ hi ≤ x) ∧ outside W x

/-- `lib/Lib/Frame.v:71-72`: every byte outside the written intervals is the
byte it was. -/
def munch (W : List ivl) (m m' : word → Option byte) : Prop :=
  ∀ x : word, outside W (bv_unsigned x) → m' x = m x

/-- `lib/Lib/Frame.v:73-74`: a writable byte stays writable. -/
def wmono (segs : List Segment) (m m' : word → Option byte) : Prop :=
  ∀ x : word, wview segs m x ≠ none → wview segs m' x ≠ none

/-- `lib/Lib/Frame.v:81-83`: every byte of `[lo, hi)` is writable and readable
— the stack window a call may use. -/
def stk (segs : List Segment) (m : word → Option byte) (lo hi : Int) : Prop :=
  0 ≤ lo ∧ hi ≤ 2 ^ 64 ∧
    ∀ a : Int, lo ≤ a → a < hi →
      wview segs m (wa a) ≠ none ∧ ∃ b, mrd segs m (wa a) = some b

/-- `lib/Lib/Frame.v:85-86`. -/
theorem stk_split (segs : List Segment) (m : word → Option byte) (lo mid hi : Int)
    (h : stk segs m lo hi) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    stk segs m lo mid ∧ stk segs m mid hi := by
  obtain ⟨hlo, hhi, hall⟩ := h
  exact ⟨⟨hlo, by omega, fun a ha hb => hall a ha (by omega)⟩,
         ⟨by omega, hhi, fun a ha hb => hall a (by omega) hb⟩⟩

theorem munch_refl (W : List ivl) (m : word → Option byte) : munch W m m :=
  fun _ _ => rfl

theorem wmono_refl (segs : List Segment) (m : word → Option byte) : wmono segs m m :=
  fun _ h => h

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
