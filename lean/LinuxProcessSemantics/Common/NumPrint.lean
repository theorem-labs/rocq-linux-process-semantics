import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.NumPrint — unsigned decimal rendering spec and algebra

Ported from `theories/Common/NumPrint.v` at the baseline above, with the
Rocq names and statements: `udec_aux`, `udec` and the lemmas of the file.  The
rendering's argument (why 24 fuel steps, why the downward-walking lemmas
carry `0 ≤ v`) is the Rocq file's header, not repeated here.

Spellings that differ:
- Rocq `v =? 0` is the decidable `v = 0` on `Int`.
- Rocq's `v / 10` and `v mod 10` are Lean's `v / 10` and `v % 10`: Rocq
  divides by floor (Lean's `Int.fdiv` and `Int.fmod`) and Lean's `Int`
  operators are Euclidean, which agree for every `v` because the divisor 10
  is positive (core `Int.fdiv_eq_ediv_of_nonneg` and
  `Int.fmod_eq_emod_of_nonneg`; the examples at the end of this file pin
  it, and that the two do not agree at every divisor).
- `10^(Z.of_nat f)` is `10 ^ f` at a `Nat` exponent, and the literal powers
  `2^64` and `10^20` are `2 ^ 64` and `10 ^ 20` at one, where each agrees
  with Rocq's non-negative `Z` exponent; `(_ <= _)%nat` is `Nat`'s `≤`, and
  Rocq `S f` is `f + 1`. -/

namespace LinuxProcessSemantics.Common.NumPrint

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-- Unsigned decimal rendering, most-significant digit first. -/
def udec_aux (v : Int) (fuel : Nat) : List byte :=
  match fuel with
  | 0 => []
  | f + 1 => if v = 0 then [] else udec_aux (v / 10) f ++ [Z_to_bv 8 (48 + v % 10)]

def udec (v : Int) : List byte :=
  if v = 0 then [Z_to_bv 8 48] else udec_aux v 24

/-! ## udec decomposition (pure) -/

theorem udec_aux_S : ∀ (f : Nat) (v : Int),
    udec_aux v (f + 1) = if v = 0 then []
                         else udec_aux (v / 10) f ++ [Z_to_bv 8 (48 + v % 10)] := by
  intro f v
  rfl

theorem udec_aux_fuel : ∀ (f g : Nat) (v : Int),
    0 ≤ v → v < 10 ^ f → f ≤ g → udec_aux v g = udec_aux v f := by
  intro f
  induction f with
  | zero =>
    intro g v hv0 hv _
    have hv' : v < 1 := hv
    have h0 : v = 0 := by omega
    subst h0
    cases g with
    | zero => rfl
    | succ g => rfl
  | succ f ih =>
    intro g v hv0 hv hfg
    cases g with
    | zero => omega
    | succ g =>
      rw [udec_aux_S, udec_aux_S]
      by_cases h : v = 0
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte]
        have hv10 : v < 10 ^ f * 10 := by rw [← Int.pow_succ]; exact hv
        have hq : v / 10 < 10 ^ f := by
          generalize (10 : Int) ^ f = P at hv10 ⊢
          omega
        rw [ih g (v / 10) (by omega) hq (by omega)]

theorem pow10_20_gt : (2 : Int) ^ 64 < 10 ^ 20 := by decide

/-- Single digit. -/
theorem udec_single : ∀ v : Int, 1 ≤ v ∧ v ≤ 9 → udec v = [Z_to_bv 8 (48 + v)] := by
  intro v hv
  have h0 : ¬ v = 0 := by omega
  have hm : v % 10 = v := by omega
  have h1 : v < 10 ^ 1 := by
    show v < 10
    omega
  unfold udec
  rw [udec_aux_fuel 1 24 v (by omega) h1 (by omega), udec_aux_S]
  simp only [h0, ↓reduceIte, hm]
  rfl

/-- Peel the least significant digit. -/
theorem udec_step : ∀ v : Int, 10 ≤ v → v < 2 ^ 64 →
    udec v = udec (v / 10) ++ [Z_to_bv 8 (48 + v % 10)] := by
  intro v hv10 hv64
  have h0 : ¬ v = 0 := by omega
  have hd : ¬ v / 10 = 0 := by omega
  unfold udec
  rw [udec_aux_S 23 v]
  simp only [h0, hd, ↓reduceIte]
  have h20 : (10 : Int) ^ 20 ≤ 10 ^ 23 := by decide
  have hq : v / 10 < 10 ^ 23 := by
    have := pow10_20_gt
    generalize (2 : Int) ^ 64 = T at hv64 this
    generalize (10 : Int) ^ 20 = P at this h20
    generalize (10 : Int) ^ 23 = Q at h20 ⊢
    omega
  rw [udec_aux_fuel 23 24 (v / 10) (by omega) hq (by omega)]

theorem udec_aux_len : ∀ (f : Nat) (v : Int), (udec_aux v f).length ≤ f := by
  intro f
  induction f with
  | zero => intro v; simp only [udec_aux, List.length_nil, Nat.le_refl]
  | succ f ih =>
    intro v
    rw [udec_aux_S]
    by_cases h : v = 0
    · simp only [h, ↓reduceIte, List.length_nil]
      omega
    · simp only [h, ↓reduceIte, List.length_append, List.length_singleton]
      have := ih (v / 10)
      omega

theorem udec_len_le : ∀ v : Int, 0 ≤ v → v < 2 ^ 64 → (udec v).length ≤ 20 := by
  intro v hv0 hv
  unfold udec
  by_cases h : v = 0
  · simp only [h, ↓reduceIte, List.length_singleton]
    omega
  · simp only [h, ↓reduceIte]
    have h20 : v < 10 ^ 20 := by
      have := pow10_20_gt
      generalize (2 : Int) ^ 64 = T at hv this
      generalize (10 : Int) ^ 20 = P at this ⊢
      omega
    rw [udec_aux_fuel 20 24 v hv0 h20 (by omega)]
    exact udec_aux_len 20 v

theorem udec_len_pos : ∀ v : Int, 1 ≤ (udec v).length := by
  intro v
  unfold udec
  by_cases h : v = 0
  · simp only [h, ↓reduceIte, List.length_singleton]
    omega
  · simp only [h, ↓reduceIte]
    rw [udec_aux_S 23 v]
    simp only [h, ↓reduceIte, List.length_append, List.length_singleton]
    omega

/-- Pin the zero arm to the ASCII digit `0`. -/
example : udec 0 = [Z_to_bv 8 48] := by decide

/-- Pin the fuel and the zero guards: `-1 / 10` is `-1` under Lean's
Euclidean `/` (`Int.ediv`), as under Rocq's floor `Z.div` (the divisor is
positive), so only the fuel ends the recursion and the rendering takes
all 24 steps. -/
example : (udec (-1)).length = 24 := by decide

/-- Boundary pin for `oob_read_bug_ns_defs.udec_len_24` at `2^64 - 1`.
This has no mutant of its own: fuel 20 renders these same 20 digit bytes. -/
example : udec 18446744073709551615 =
    [Z_to_bv 8 49, Z_to_bv 8 56, Z_to_bv 8 52, Z_to_bv 8 52,
     Z_to_bv 8 54, Z_to_bv 8 55, Z_to_bv 8 52, Z_to_bv 8 52,
     Z_to_bv 8 48, Z_to_bv 8 55, Z_to_bv 8 51, Z_to_bv 8 55,
     Z_to_bv 8 48, Z_to_bv 8 57, Z_to_bv 8 53, Z_to_bv 8 53,
     Z_to_bv 8 49, Z_to_bv 8 54, Z_to_bv 8 49, Z_to_bv 8 53] := by decide

/-! ## Floor and Euclidean division at the divisor 10

The header reads Rocq's floor `v / 10` and `v mod 10` as Lean's Euclidean
`v / 10` and `v % 10`.  The first two examples pin that reading for every
`v`.  The next two show that the agreement does not hold at every divisor:
at `-2` the floor and Euclidean quotients of `7` differ, and so do its
remainders.  The last pins `udec_aux` itself at a negative value, against
Rocq's `[57; 51]`: Rocq's floor division takes `-7` to `-1` with the digit
`3`, then `-1` to itself with the digit `9`, where a truncating `/` and
`%` would take `-7` to `0` with the remainder `-7` and render the one
byte `41`. -/

example (v : Int) : Int.fdiv v 10 = v / 10 := Int.fdiv_eq_ediv_of_nonneg v (by decide)
example (v : Int) : Int.fmod v 10 = v % 10 := Int.fmod_eq_emod_of_nonneg v (by decide)
example : Int.fdiv 7 (-2) ≠ 7 / (-2) := by decide
example : Int.fmod 7 (-2) ≠ 7 % (-2) := by decide
example : udec_aux (-7) 2 = [Z_to_bv 8 57, Z_to_bv 8 51] := by decide

end LinuxProcessSemantics.Common.NumPrint
