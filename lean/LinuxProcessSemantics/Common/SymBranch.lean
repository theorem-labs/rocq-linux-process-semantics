import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.StepTac

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.SymBranch — closing `SymExec`'s `SCBr` obligations

Ported from `theories/Common/SymBranch.v` at the baseline above: its
lemmas, with the Rocq statements, and its Ltac closer `sym_br` as a Lean
macro.  The Rocq file's docstring says what a branch obligation looks like
and why the step from `bv_signed` to `bv_unsigned` is the missing piece; it
is not repeated here.

Spellings: Rocq's `Z.ltb`/`Z.eqb` are `decide` of `<`/`=` on `Int`, and
`bv_signed_lit`'s combined range `-2^63 <= z < 2^63` is one conjunction
hypothesis.  `v_addiw` is `PropExec`'s, as in Rocq.

`sym_br` calls Rocq's `StepTac.u_norm`, an Ltac definition `StepTac.lean`
leaves unported (its docstring).  It is `sym_u_norm` here, defined in this
file because `sym_br` is the first tactic to need it, under a name of its
own so that a later port of `u_norm` into `StepTac` does not clash with it.
The macro names stay usable as identifiers (the last example). -/

namespace LinuxProcessSemantics.Common.SymBranch

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Common.PropExec

/-- Below `2^63` the signed and unsigned readings agree.

`protected`: `PropExec.bv_signed_small` has the same name and statement, and
a file opening both namespaces would otherwise read the bare name as
ambiguous.  This one is proved from that one. -/
protected theorem bv_signed_small (x : word) (hx : bv_unsigned x < 2 ^ 63) :
    bv_signed x = bv_unsigned x :=
  PropExec.bv_signed_small x hx

/-- `blt`/`bge` on two operands below `2^63`, as an `Int` comparison. -/
theorem bv_lts_small (a b : word) (ha : bv_unsigned a < 2 ^ 63) (hb : bv_unsigned b < 2 ^ 63) :
    bv_lts a b = decide (bv_unsigned a < bv_unsigned b) := by
  have ha' := PropExec.bv_signed_small a ha
  have hb' := PropExec.bv_signed_small b hb
  unfold bv_lts
  unfold bv_signed at ha' hb'
  rw [BitVec.slt, ha', hb']

/-- `bltu`/`bgeu` as an `Int` comparison. -/
theorem bv_ltu_Z (a b : word) : bv_ltu a b = decide (bv_unsigned a < bv_unsigned b) := by
  unfold bv_ltu bv_unsigned
  rw [BitVec.ult]
  exact decide_eq_decide.2 Int.ofNat_lt.symm

/-- `beq`/`bne` as an `Int` comparison. -/
theorem bv_eqb_Z (a b : word) : bv_eqb a b = decide (bv_unsigned a = bv_unsigned b) := by
  unfold bv_eqb bv_unsigned
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, Int.ofNat_inj, BitVec.toNat_inj]

/-- A literal operand in the signed range reads back as itself (a `blt`
against a negative literal, whose `bv_signed` is not its `bv_unsigned`). -/
theorem bv_signed_lit (z : Int) (hz : -2 ^ 63 ≤ z ∧ z < 2 ^ 63) :
    bv_signed (Z_to_bv 64 z) = z := by
  unfold bv_signed Z_to_bv
  exact BitVec.toInt_ofInt_eq_self (by decide) hz.1 hz.2

/-- `addiw` with an immediate of either sign, when the sum stays in
`[0, 2^31)`. -/
theorem v_addiw_range (x : word) (imm : Int) (hlo : 0 ≤ bv_unsigned x + imm)
    (hhi : bv_unsigned x + imm < 2 ^ 31) :
    bv_unsigned (v_addiw x imm) = bv_unsigned x + imm := by
  unfold v_addiw
  have hs : bv_swrap 32 (bv_unsigned x + imm) = bv_unsigned x + imm := by
    unfold bv_swrap bv_wrap bv_half_modulus bv_modulus
    have h : (2 : Int) ^ 32 / 2 = 2 ^ 31 := by decide
    rw [h, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  rw [Z_to_bv_unsigned, hs, bv_wrap64_mod]
  exact Int.emod_eq_of_lt hlo (by omega)

/-- Lean-only: `bv_lts` as the `Int` comparison of the signed readings,
which is Rocq's definition of `bv_lts`.  Rocq's `sym_br` reaches that form
by `unfold bv_lts`; Lean's `bv_lts` unfolds to `BitVec.slt` instead, so the
macro rewrites with this. -/
theorem bv_lts_signed (a b : word) : bv_lts a b = decide (bv_signed a < bv_signed b) := rfl

/-- Rocq's `StepTac.u_norm` (`repeat rewrite u_Z2bv by lia`): collapse
`bv_unsigned (Z_to_bv 64 z)` to `z` while `omega` closes the instance's
`0 ≤ z` and `z < 2 ^ 64`, in the first goal alone.  `rewrite`, not `rw`,
leaves the rewritten goal open, as Rocq's does.  Matching differs: Lean
collapses a `let`-bound alias of `Z_to_bv 64 z`, which Rocq's `u_norm`
leaves alone; a width named by a definition collapses in Rocq and stays
unchanged here (the alias and named-width examples below). -/
macro "sym_u_norm" : tactic => `(tactic|
  repeat (focus (rewrite [StepTac.u_Z2bv]; rotate_left; omega; omega)))

/-- Rocq's `sym_br`: close a branch obligation `bv_lts a b = d`,
`bv_ltu a b = d` or `bv_eqb a b = d` (or its negation under `!`), for a
literal `d`, from the `Int` facts in context, on the first goal alone.

Rocq's steps, with a rewrite by `bv_lts_signed`,
`bv_ltu_Z` and `bv_eqb_Z` for Rocq's `unfold`, and each Rocq
`rewrite ?L by tac` a `repeat` of `rewrite [L]` whose side conditions `tac`
closes as goals of their own.  Lean's
`rewrite` and `omega` are not Rocq's `rewrite` and `lia`, so some goals
close on one side and not the other.

The `!` and `decide` rewrites use reducible transparency: at default
transparency, a rewrite that finds no match can run into `maxRecDepth`.
The large-operand examples below pin this for `!`; the `BitVec 32`
`+4096` and `zzB 3000` examples pin it for `decide`. -/
macro "sym_br" : tactic => `(tactic|
  (repeat with_reducible rewrite [Bool.not_eq_true']) <;>
  (repeat with_reducible rewrite [Bool.not_eq_false']) <;>
  (repeat rewrite [SymBranch.bv_lts_signed]) <;> (repeat rewrite [SymBranch.bv_ltu_Z]) <;>
  (repeat rewrite [SymBranch.bv_eqb_Z]) <;>
  (repeat (focus (rewrite [SymBranch.bv_signed_lit]; rotate_left; omega))) <;>
  (repeat (focus
    rewrite [SymBranch.bv_signed_small]
    rotate_left
    repeat (focus (rewrite [SymBranch.v_addiw_range]; rotate_left; omega; omega))
    sym_u_norm
    omega)) <;>
  (repeat (focus (rewrite [SymBranch.v_addiw_range]; rotate_left; omega; omega))) <;>
  sym_u_norm <;>
  (repeat with_reducible rewrite [decide_eq_false_iff_not]) <;>
  (repeat with_reducible rewrite [decide_eq_true_eq]) <;>
  omega)

-- `bge` taken on `1 >= argc`, and falling through on `argc >= 2`.
example (x : word) (h : bv_unsigned x ≤ 1) : (!(bv_lts (Z_to_bv 64 1) x)) = true := by
  sym_br
example (x : word) (h : 2 ≤ bv_unsigned x) (h2 : bv_unsigned x < 1000) :
    (!(bv_lts (Z_to_bv 64 1) x)) = false := by
  sym_br
example (x y : word) (h : bv_unsigned x < bv_unsigned y) : bv_ltu x y = true := by
  sym_br
example (x y : word) (h : bv_unsigned x = bv_unsigned y) : (!(bv_eqb x y)) = false := by
  sym_br
-- Two `!`s: the `= true` step runs first, as in Rocq.
example (x y : word) (h : bv_unsigned x < bv_unsigned y) : (!(!(bv_ltu x y))) = true := by
  sym_br
-- Large operands where no `!` is found: pin the reducible `!` rewrites.
example (x y : word) (hx0 : 0 ≤ bv_unsigned x) (hx : bv_unsigned x < 10)
    (hy0 : 20 ≤ bv_unsigned y) (hy1 : bv_unsigned y < 1000) :
    bv_ltu x (v_addiw y 3) = true := by
  sym_br
example (x y : word) (hx0 : 0 ≤ bv_unsigned x) (hx : bv_unsigned x < 100)
    (hy : bv_unsigned y = 200) : bv_eqb (v_addiw x 1) y = false := by
  sym_br
-- A negative literal operand.
example (x : word) (h0 : 0 ≤ bv_unsigned x) (h : bv_unsigned x < 2 ^ 63) :
    bv_lts x (Z_to_bv 64 (-9)) = false := by
  sym_br
-- An `addiw` operand with a negative immediate.
example (x y : word) (h1 : 2 ≤ bv_unsigned x) (h2 : bv_unsigned x < 100)
    (h3 : bv_unsigned y = 200) : bv_lts (v_addiw x (-2)) y = true := by
  sym_br
-- A projection inside an operand.
example (x y : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 100)
    (h3 : bv_unsigned y = 200) : bv_ltu (Z_to_bv 64 (bv_unsigned x - 16)) y = true := by
  sym_br
-- Two projection operands: `sym_u_norm` collapses both.
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    bv_ltu (Z_to_bv 64 (bv_unsigned x - 16)) (Z_to_bv 64 (bv_unsigned x - 8)) = true := by
  sym_br

example (y : word) (hy : bv_unsigned y = 10) :
    (!(bv_ltu y (Z_to_bv 64 6))) = true ∧ (!(bv_ltu y (Z_to_bv 64 7))) = true := by
  sym_br
example (x : word) (hx : bv_unsigned x < 5) :
    (!(bv_ltu x (Z_to_bv 64 6))) = false ∧ (!(bv_ltu x (Z_to_bv 64 7))) = false := by
  sym_br
example (x y : word) (hx : bv_unsigned x < 5) (hy : bv_unsigned y = 10) :
    bv_lts x y = true ∧ bv_lts x (Z_to_bv 64 6) = true := by
  sym_br
example (x y : word) (hx : bv_unsigned x < 5) (hy : bv_unsigned y = 10) :
    bv_ltu x y = true ∧ bv_ltu x (Z_to_bv 64 6) = true := by
  sym_br
example (x y : word) (hx : bv_unsigned x = 5) (hy : bv_unsigned y = 10) :
    bv_eqb x y = false ∧ bv_eqb x (Z_to_bv 64 6) = false := by
  sym_br
example (z : Int) (h1 : -3 ≤ z) (h2 : z ≤ 3) :
    bv_lts (Z_to_bv 64 z) (Z_to_bv 64 (-9)) = false := by
  sym_br
example (x y z : word) (hx0 : 0 ≤ bv_unsigned x) (hx : bv_unsigned x < 100)
    (hy0 : 0 ≤ bv_unsigned y) (hy : bv_unsigned y < 100) (hz : bv_unsigned z = 300) :
    bv_lts (Z_to_bv 64 (bv_unsigned (v_addiw x 1) + bv_unsigned (v_addiw y 2))) z = true := by
  sym_br
example (x y : word) (hx1 : 1 ≤ bv_unsigned x) (hx2 : bv_unsigned x < 50)
    (hy1 : 100 ≤ bv_unsigned y) (hy2 : bv_unsigned y < 200) :
    bv_ltu (v_addiw x (-1)) (v_addiw y (-2)) = true := by
  sym_br
-- `v_addiw_range` runs before `sym_u_norm`, as in Rocq.
example (a : Int) (y : word) (h0 : 0 ≤ a) (h1 : a < 100) (h2 : 2 ≤ bv_unsigned (Z_to_bv 64 a))
    (h3 : bv_unsigned (Z_to_bv 64 a) < 1000) (hy : bv_unsigned y = 200) :
    bv_ltu (v_addiw (Z_to_bv 64 a) (-2)) y = true := by
  sym_br
-- Each side condition is proved in a goal of its own.
example (a : Int) (y : word) (ha : bv_unsigned (Z_to_bv 64 a) < 100)
    (hy0 : 100 ≤ bv_unsigned y) (hy : bv_unsigned y < 1000)
    (hB : bv_unsigned (Z_to_bv 64 (bv_unsigned y + 1)) = bv_unsigned y + 1) :
    bv_lts (Z_to_bv 64 a) (Z_to_bv 64 (bv_unsigned y + 1)) = true := by
  sym_br
example (u x : word) (hA : bv_unsigned (v_addiw u 5) < 100) (h1 : 152 ≤ bv_unsigned x)
    (h2 : bv_unsigned x < 1000) (hB : 150 ≤ bv_unsigned (v_addiw x (-2))) :
    bv_lts (v_addiw u 5) (v_addiw x (-2)) = true := by
  sym_br
-- The side condition's `sym_u_norm` works on that goal alone, and the
-- main goal's runs too late for `bv_signed_lit`: fails, as Rocq's does.
example (x : word) (a : Int) (hx : bv_unsigned x = 0) (h0 : 0 ≤ a) (h1 : a < 5) :
    bv_lts x (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + 1)) = true := by
  fail_if_success sym_br
  rw [StepTac.u_Z2bv a (by omega) (by omega), SymBranch.bv_lts_signed,
    SymBranch.bv_signed_small x (by omega), SymBranch.bv_signed_lit (a + 1) (by omega)]
  exact decide_eq_true (by omega)
-- An operand `bv_signed_lit` does not take (`h3` does not put it below
-- `2 ^ 63`) and `bv_signed_small` does, once its side condition's
-- `sym_u_norm` has collapsed the projections in it, outer then inner:
-- closes, as Rocq's does.
example (a : Int) (y : word) (h0 : 0 ≤ a) (h1 : a < 5) (h2 : 0 ≤ bv_unsigned (Z_to_bv 64 a))
    (h3 : bv_unsigned (Z_to_bv 64 a) < 2 ^ 64 - 1) (hy : bv_unsigned y = 200) :
    bv_lts (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + 1)) y = true := by
  sym_br
-- A literal nested in a projection fails, as Rocq's twin does: dropping
-- the literal's `bv_signed` needs `bv_signed_lit`'s side condition over a
-- projection `omega` cannot see through, and `bv_signed_small` then
-- rewrites the literal operand first and meets the same projection.
example (y : word) (h : bv_unsigned y = 200) :
    bv_lts (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 7))) y = true := by
  fail_if_success sym_br
  rw [SymBranch.bv_lts_signed,
    SymBranch.bv_signed_lit _ (by rw [StepTac.u_Z2bv _ (by omega) (by omega)]; omega),
    SymBranch.bv_signed_small y (by omega), StepTac.u_Z2bv _ (by omega) (by omega)]
  exact decide_eq_true (by omega)
-- The branch stated only as the comparison itself: the macro rewrites the
-- goal and not `h`, whose comparison `omega` cannot read, so it fails, as
-- Rocq's does.
example (x y : word) (h : bv_lts x y = true) : bv_lts x y = true := by
  fail_if_success sym_br
  exact h
-- The branch goes the other way: the macro fails.
example (x : word) (_h : bv_unsigned x = 5) (hc : bv_ltu x (Z_to_bv 64 3) = false) :
    bv_ltu x (Z_to_bv 64 3) = false := by
  fail_if_success (have : bv_ltu x (Z_to_bv 64 3) = true := by sym_br)
  exact hc
-- An equation of an operand with itself: the final `omega` closes it.
example (r t : word) : (!(bv_eqb (r + t) (r + t))) = false := by
  sym_br
-- The first operand's side condition fails, so the loop stops before the
-- second's `bv_signed` is dropped, and `h2` does not apply: fails, as
-- Rocq's does.
example (a b : word) (h : bv_signed a < 5) (h2 : bv_unsigned b = 200) : bv_lts a b = true := by
  fail_if_success sym_br
  rw [SymBranch.bv_lts_signed, SymBranch.bv_signed_small b (by omega)]
  exact decide_eq_true (by omega)
-- The same stop is what keeps `bv_signed b` for `h1`: closes, as Rocq's does.
example (a b : word) (h : bv_signed a = -2 ^ 63) (h1 : bv_signed b = 3) (_h2 : bv_unsigned b < 2 ^ 63) :
    bv_lts a b = true := by
  sym_br
-- The literal step stops the same way: the first operand's side condition
-- fails, so the literal second operand keeps its `bv_signed`, which `h`
-- does not bound: fails, as Rocq's does.
example (a : Int) (h0 : 0 ≤ a) (h1 : a < 3) (h : bv_signed (Z_to_bv 64 a) < 3) :
    bv_lts (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a))) (Z_to_bv 64 5) = true := by
  fail_if_success sym_br
  rw [SymBranch.bv_lts_signed, StepTac.u_Z2bv a (by omega) (by omega),
    SymBranch.bv_signed_lit 5 (by omega)]
  exact decide_eq_true (by omega)
-- A literal operand whose `bv_signed` is read before `bv_signed_small`
-- could meet it: `bv_signed_small` would need `bv_unsigned (Z_to_bv 64 z)`
-- below `2 ^ 63`, which `h3` gives, and then leave `z`'s unsigned reading.
example (z : Int) (h1 : -3 ≤ z) (h2 : z ≤ 3) (_h3 : bv_unsigned (Z_to_bv 64 z) < 2 ^ 63) :
    bv_lts (Z_to_bv 64 z) (Z_to_bv 64 5) = true := by
  sym_br
-- With two goals open, it closes the first and leaves the second.
example (x y : word) (h : bv_unsigned x < bv_unsigned y) :
    bv_ltu x y = true ∧ (!(bv_eqb x y)) = true := by
  constructor
  sym_br
  guard_target =ₛ (!(bv_eqb x y)) = true
  sym_br
-- Comparisons of two 32-bit words: the comparison lemmas are stated for
-- `word`, so the macro fails, where Rocq's `unfold` reads every width.
example (a b : BitVec 32) (h : bv_unsigned a < bv_unsigned b) : bv_ltu a b = true := by
  fail_if_success sym_br
  unfold bv_ltu bv_unsigned at *
  rw [BitVec.ult]
  exact decide_eq_true (by omega)
example (a b : BitVec 32) (h : bv_unsigned a = bv_unsigned b) : bv_eqb a b = true := by
  fail_if_success sym_br
  unfold bv_eqb bv_unsigned at *
  simp only [beq_iff_eq]
  exact BitVec.eq_of_toNat_eq (by omega)
example (a b : BitVec 32) (h : bv_signed a < bv_signed b) : bv_lts a b = true := by
  fail_if_success sym_br
  have e : bv_lts a b = decide (bv_signed a < bv_signed b) := rfl
  rw [e]
  exact decide_eq_true h
-- Pin the reducible `decide` rewrites on the `BitVec 32` `+4096` operand.
example (a b : BitVec 32) (h : bv_unsigned a < 5) (hb0 : 0 ≤ bv_unsigned b)
    (hb : bv_unsigned b < 1000)
    (hp : bv_unsigned (Z_to_bv 32 (bv_unsigned b + 4096)) = bv_unsigned b + 4096) :
    bv_ltu a (Z_to_bv 32 (bv_unsigned b + 4096)) = true := by
  fail_if_success sym_br
  unfold bv_ltu bv_unsigned at *
  rw [BitVec.ult]
  exact decide_eq_true (by omega)
-- `omega` closes a goal a hypothesis states, before any arithmetic: closes,
-- where Rocq's `lia` fails.
example (a b : BitVec 32) (h : bv_eqb a b = false) : (!(bv_eqb a b)) = true := by
  sym_br
-- A `Bool` comparison in context, which the goal's own rewrite produces:
-- `omega` does not read it, and Rocq's `lia` does.
example (x : word) (h : decide (bv_unsigned x < 5) = true) : bv_ltu x (Z_to_bv 64 6) = true := by
  fail_if_success sym_br
  rw [decide_eq_true_eq] at h
  sym_br
-- A literal `Bool` equation: Lean's macro fails, where Rocq's `lia`
-- closes it (and so does Rocq's `sym_br`).
example : (!false) = true := by
  fail_if_success sym_br
  rfl
example : (!true) = false := by
  fail_if_success sym_br
  rfl
-- Pin the reducible `decide` rewrites on `zzB 3000`, a recursive
-- `@[instance_reducible]` definition in the goal.
@[instance_reducible] private def zzB : Nat → Bool | 0 => false | n + 1 => zzB n
example (x : Bool) (h : x = zzB 3000) : x = zzB 3000 := by first | sym_br | exact h
-- Linear bounds with a real solution and no integer one: `omega` has no
-- dark shadow, and Rocq's `lia` closes it.
example (x y : word) (h1 : 27 ≤ 11 * bv_unsigned x + 13 * bv_unsigned y)
    (h2 : 11 * bv_unsigned x + 13 * bv_unsigned y ≤ 45)
    (h3 : -10 ≤ 7 * bv_unsigned x - 9 * bv_unsigned y)
    (h4 : 7 * bv_unsigned x - 9 * bv_unsigned y ≤ 4) : bv_ltu x y = true := by
  fail_if_success sym_br
  exfalso
  have hx : bv_unsigned x = 1 ∨ bv_unsigned x = 2 := by omega
  rcases hx with hx | hx <;> omega
-- `sym_u_norm` leaves the rewritten goal open, and works on the first goal
-- alone.
example (x : word) (h0 : 0 ≤ bv_unsigned x) (h1 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x + 1)) = bv_unsigned x + 1 := by
  sym_u_norm
  guard_target =ₛ bv_unsigned x + 1 = bv_unsigned x + 1
  rfl
example (a b : Int) (h0 : 0 ≤ a) (h1 : a < 10) :
    bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 b)
      + bv_unsigned (Z_to_bv 64 a) = 3 * a + bv_unsigned (Z_to_bv 64 b) := by
  sym_u_norm
  guard_target =ₛ a + a + bv_unsigned (Z_to_bv 64 b) + a = 3 * a + bv_unsigned (Z_to_bv 64 b)
  omega
example (a b : Int) (ha0 : 0 ≤ a) (ha : a < 10) (hb0 : 0 ≤ b) (hb : b < 10) :
    bv_unsigned (Z_to_bv 64 a) < 10 ∧ bv_unsigned (Z_to_bv 64 b) < 10 := by
  constructor
  sym_u_norm
  · guard_target =ₛ a < 10
    omega
  · guard_target =ₛ bv_unsigned (Z_to_bv 64 b) < 10
    rw [StepTac.u_Z2bv b hb0 (by omega)]
    omega
-- A let-bound alias is unfolded by Lean's matching; Rocq leaves it alone.
example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    let w := Z_to_bv 64 z; bv_unsigned w = z := by
  intro w
  sym_u_norm
  guard_target =ₛ z = z
  rfl
-- A named width stays unchanged in Lean; Rocq's `u_norm` collapses it.
private def namedWidth : Nat := 64
example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv namedWidth z) = z := by
  sym_u_norm
  guard_target =ₛ bv_unsigned (Z_to_bv namedWidth z) = z
  exact StepTac.u_Z2bv z h0 h1
-- The lemmas at the ends of their ranges, with Rocq's explicit arguments.
example (i n : word) (Hn : bv_unsigned n ≤ bv_unsigned i) (Hi : bv_unsigned i < 2 ^ 63)
    (_Hn0 : 2 ^ 62 ≤ bv_unsigned n) : bv_lts i n = false := by
  rw [bv_lts_small _ _ (by omega) (by omega), decide_eq_false_iff_not]; omega
example (a b : word) : bv_ltu a b = decide (bv_unsigned a < bv_unsigned b) ∧
    bv_eqb a b = decide (bv_unsigned a = bv_unsigned b) :=
  ⟨SymBranch.bv_ltu_Z a b, SymBranch.bv_eqb_Z a b⟩
example : bv_signed (Z_to_bv 64 (-2 ^ 63)) = -2 ^ 63 ∧
    bv_signed (Z_to_bv 64 (2 ^ 63 - 1)) = 2 ^ 63 - 1 :=
  ⟨SymBranch.bv_signed_lit (-2 ^ 63) ⟨by omega, by omega⟩,
    SymBranch.bv_signed_lit (2 ^ 63 - 1) ⟨by omega, by omega⟩⟩
example (x : word) (h : bv_unsigned x = 2 ^ 31 + 1) : bv_unsigned (v_addiw x (-2)) = 2 ^ 31 - 1 := by
  rw [SymBranch.v_addiw_range x (-2) (by omega) (by omega)]; omega
-- The lemmas' statements, hypotheses in Rocq's order.
example : ∀ (a b : word), bv_unsigned a < 2 ^ 63 → bv_unsigned b < 2 ^ 63 →
    bv_lts a b = decide (bv_unsigned a < bv_unsigned b) := bv_lts_small
example : ∀ z : Int, -2 ^ 63 ≤ z ∧ z < 2 ^ 63 → bv_signed (Z_to_bv 64 z) = z := bv_signed_lit
example : ∀ (x : word) (imm : Int), 0 ≤ bv_unsigned x + imm → bv_unsigned x + imm < 2 ^ 31 →
    bv_unsigned (v_addiw x imm) = bv_unsigned x + imm := v_addiw_range
end LinuxProcessSemantics.Common.SymBranch

section
open LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SymBranch

-- Outside the namespace, with it and `PropExec` both open, the bare name
-- is `PropExec.bv_signed_small`: `protected` keeps it unambiguous.
example (x : word) (h : bv_unsigned x < 2 ^ 63) : bv_signed x = bv_unsigned x :=
  bv_signed_small x h
-- The keywords are not reserved tokens: the names still parse as identifiers.
example (sym_br sym_u_norm : Nat) (h : sym_br + sym_u_norm = 0) : sym_br = 0 := by
  omega

end
