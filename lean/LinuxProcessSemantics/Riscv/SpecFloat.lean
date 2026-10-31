-- Ports rocq-linux-process-semantics f1006fe8:theories/Riscv/Fpu.v
/-! # SpecFloat: the library floor under `theories/Riscv/Fpu.v`

`theories/Riscv/Fpu.v` opens with

```coq
From Stdlib Require Import ZArith SpecFloat.
From Flocq.IEEE754 Require BinarySingleNaN.
```

and then computes with names those two libraries define.  The Lean twin has
neither library and no Mathlib (`lean/lake-manifest.json` lists no package),
so this file is the port of exactly that closure: every `SpecFloat` and
`BinarySingleNaN.` name `Fpu.v` mentions, the Flocq and Rocq definitions those
rest on, and the handful of `Z` operations whose Rocq convention differs from
Lean's.  Nothing else from either library is ported.  This file imports nothing;
Lean core is all it uses.

## Which versions

The versions this repository builds against, read from
`rocq-linux-process-semantics-core.opam` (`"rocq-core" {>= "9.2" & < "9.3"}`,
`"rocq-stdlib" {>= "9.0"}`, `"coq-flocq" {>= "4.2"}`) and resolved in the opam
switch that builds the Rocq tree to `rocq-core.9.2.0`, `rocq-stdlib.9.2.0` and
`coq-flocq.4.2.2`.  The text ported is that switch's installed source:

- `rocq-core 9.2.0:theories/Corelib/Floats/SpecFloat.v`.  `rocq-stdlib`'s
  `theories/Floats/SpecFloat.v` is a one-line re-export of it, and the
  installed file read is `lib/coq/theories/Floats/SpecFloat.v`.
- `coq-flocq 4.2.2:Flocq/IEEE754/BinarySingleNaN.v` and
  `coq-flocq 4.2.2:Flocq/Calc/Round.v`, `coq-flocq 4.2.2:Flocq/Core/FLT.v`
  (`lib/coq/user-contrib/Flocq/...`)
- `rocq-core 9.2.0:theories/Corelib/BinNums/IntDef.v` for `Z.div_eucl`,
  `Z.even`, `Z.div2`, `Z.sqrtrem` and `Z.shiftl`, and
  `rocq-stdlib 9.2.0:theories/BinInt/BinIntDef.v` for `Z.log2`, which
  `IntDef.v` does not define.

Line numbers in the docstrings below are those files' lines.

## Representation

- Rocq `Z` is Lean `Int`, Rocq `bool` is `Bool`, Rocq `comparison`
  (`Eq`/`Lt`/`Gt`) is Lean's `Ordering` (`.eq`/`.lt`/`.gt`), and Rocq's
  `CompOpp` is `Ordering.swap`.
- Rocq `positive` is Lean `Nat` **with the invariant that it is strictly
  positive**.  Rocq's type enforces that; Lean's does not, so every function
  here that takes a former `positive` agrees with Rocq only on inputs `> 0`,
  and each such docstring says what Lean does at `0`.  `Z.pos m` transcribes
  to the coercion `(m : Int)`, `Pos.mul` to `*`, and `Pos.size` to
  `digits2_pos` (Rocq defines the two by the same recursion).
- A Rocq section variable is an ordinary leading argument: `SpecFloat.v`'s
  `Section FloatOps` has `Variable prec emax : Z`, so `fexp`, `shr_fexp`,
  `SFdiv_core_binary` and `SFsqrt_core_binary` take `prec emax` first, exactly
  as `Fpu.v` already writes them (`shr_fexp p em mx ex lx`).  Definitions that
  do not mention `prec`/`emax` (`digits2_pos`, `Zdigits2`, `shr`, `shl_align`,
  `new_location`, `SFcompare`, …) take neither, again as `Fpu.v` writes them.

## Rocq `Z` division against Lean `Int` division

Lean 4.34's `/` and `%` on `Int` are EUCLIDEAN (`(-7)/2 = -4`, `(-7)%2 = 1`,
but `7/(-2) = -3`), Rocq's `Z.div`/`Z.modulo` are FLOOR, and Rocq's
`Z.quot`/`Z.rem` truncate toward zero.  No ported definition below uses `/` or
`%` on `Int`.  Each one names the convention it needs — `Int.fdiv`/`Int.fmod`
for Rocq's `Z.div_eucl` and `Z.div2`, truncation toward zero for `shr_1`'s
mantissa step — and every one carries an `example` at the end of this file
pinning a negative case where the three conventions disagree.

## Reducibility

`theories/Riscv/FpuTests.v`'s pins are `:= eq_refl` in Rocq, with no tactic at
all, and `by decide`/`by rfl` in the twin, which the Lean KERNEL must
discharge.
A definition elaborated by well-founded recursion does not reduce in the
kernel, so nothing here is well-founded: every recursion is structural on a
`Nat`, and the bulk of the arithmetic is `Nat` primitives the kernel evaluates
with GMP (`Nat.add`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`,
`Nat.shiftRight`, `Nat.log2`, `Nat.testBit`).  Two definitions therefore take a
different SHAPE from Rocq's while computing the same value, and say so:
`shr` (closed form instead of iterating `shr_1`) and `natSqrt` (Newton's
method instead of `Pos.sqrtrem`'s digit recursion, because Lean core's
`Nat.sqrt` is well-founded and does not reduce).

## How the port was checked

Beyond the pins at the end of this file, every definition here was run against
the library it ports: 2460 generated cases — `binary_round_aux` over both
formats, all five modes, both signs, mantissas from one bit to a hundred and
exponents from -1200 to 1100, and `shr_fexp`, `shl_align`, `SFdiv_core_binary`,
`SFsqrt_core_binary`, `new_location`, `choice_mode`, `binary_overflow`,
`binary_fit_aux`, `SFcompare`, `shr`, `fexp`, `digits2_pos`, `Zdigits2`,
`Z.log2`, `Z.div2`, `Z.shiftl` and `Z.div_eucl` on the same inputs — were
computed by `coqc` against Rocq 9.2.0 and Flocq 4.2.2 and by `lean` against
this file, each encoded as a flat integer list.  The two lists, 8440 integers,
are identical. -/

namespace LinuxProcessSemantics.Riscv.SpecFloat

/-! ## `Z` operations with Rocq's conventions

Not part of `SpecFloat` or `BinarySingleNaN`: these are the `ZArith`
primitives the ported bodies call, given here once so the twin has a single
copy.  `Fpu.v` itself calls `Z.log2` (in `fp_ew`) and `Z.min`, which is why
`Zlog2` and `Zmin` are exported rather than kept private. -/

/-- `2 ^ n` as an `Int`, computed in `Nat`.  `Nat.pow` is a kernel GMP
primitive; `Int`'s `^` is a structural recursion over the exponent, so going
through `Nat` keeps a 2000-bit alignment shift cheap for `decide`. -/
def twoPow (n : Nat) : Int := ((2 ^ n : Nat) : Int)

/-- Rocq's `Z.max` (`IntDef.v`: `max n m` is `m` when `n ?= m` is `Lt`,
else `n`). -/
def Zmax (n m : Int) : Int := if n < m then m else n

/-- Rocq's `Z.min` (`IntDef.v`: `min n m` is `m` when `n ?= m` is `Gt`,
else `n`). -/
def Zmin (n m : Int) : Int := if m < n then m else n

/-- Rocq's `Z.compare`, landing in Lean's `Ordering` instead of Rocq's
`comparison`. -/
def Zcompare (n m : Int) : Ordering := compare n m

/-- Rocq's `Z.even` (`IntDef.v:313-319`): true on `0` and on both signs of an
even magnitude.  Parity ignores the sign, so the magnitude's low bit decides
it; `Z.even (-4) = true` and `Z.even (-3) = false`, pinned below. -/
def Zeven (z : Int) : Bool := z.natAbs % 2 == 0

/-- Rocq's `Z.div2` (`IntDef.v:327-333`): division by two ROUNDING TOWARD
BOTTOM, not toward zero — `Z.div2 (-3) = -2`.  Rocq writes it with `Pos.div2`
on a positive and `Pos.div2_up` on a negative, which is floor on both sides,
i.e. Lean's `Int.fdiv _ 2` (NOT `/`, which is Euclidean, nor `Int.tdiv`).
`SFsqrt_core_binary` applies it to a negative exponent, so the difference is
reachable. -/
def Zdiv2 (z : Int) : Int := Int.fdiv z 2

/-- Truncation toward zero by `2 ^ n`, the step `shr_1` takes on the mantissa.
Rocq spells it as four constructor cases (`Zpos (xO p) => Zpos p` and so on),
each of which drops the low bit of the MAGNITUDE and keeps the sign; that is
truncation toward zero, which for a negative argument is neither Lean's `/`
nor `Int.fdiv`. -/
def Zquot2pow (m : Int) (n : Nat) : Int :=
  if m < 0 then -((m.natAbs >>> n : Nat) : Int) else ((m.natAbs >>> n : Nat) : Int)

/-- Rocq's `Z.div_eucl` (`IntDef.v:249-268`): the quotient rounds toward
BOTTOM and the remainder takes the DIVISOR's sign, with `Z.div_eucl a 0 =
(0, a)` and `Z.div_eucl 0 b = (0, 0)`.  Lean's matching pair is
`Int.fdiv`/`Int.fmod`; the zero divisor is written out because the twin should
not depend on `Int.fdiv`'s own choice there. -/
def Zdiv_eucl (a b : Int) : Int × Int :=
  if b = 0 then (0, a) else (Int.fdiv a b, Int.fmod a b)

/-- Rocq's `Z.shiftl` (`IntDef.v:359-364`).  A POSITIVE count multiplies by
`2 ^ n`; a NEGATIVE count iterates `Z.div2`, i.e. divides by `2 ^ (-n)`
rounding toward bottom — not toward zero.  `Fpu.v` and the division and square
root cores only ever shift left, but the negative branch is Rocq's and is
pinned below. -/
def Zshiftl (a n : Int) : Int :=
  if 0 ≤ n then a * twoPow n.toNat else Int.fdiv a (twoPow (-n).toNat)

/-! ## `spec_float`, `location`, `shr_record` -/

/-- `SpecFloat.v:21-25`: the payload-free IEEE datum.  Rocq's `m : positive`
is a `Nat` that callers keep strictly positive. -/
inductive spec_float where
  | S754_zero (s : Bool)
  | S754_infinity (s : Bool)
  | S754_nan
  | S754_finite (s : Bool) (m : Nat) (e : Int)
  deriving DecidableEq, Repr, Inhabited

export spec_float (S754_zero S754_infinity S754_nan S754_finite)

/-- `SpecFloat.v:82`: where an exact value sits relative to the two candidate
mantissas.  Rocq's `loc_Inexact : comparison -> location` carries
`Lt`/`Eq`/`Gt`; here it carries `Ordering`'s `.lt`/`.eq`/`.gt`. -/
inductive location where
  | loc_Exact
  | loc_Inexact (c : Ordering)
  deriving DecidableEq, Repr, Inhabited

export location (loc_Exact loc_Inexact)

/-- `SpecFloat.v:84`: a mantissa with the round bit and the sticky bit shifted
out of it so far. -/
structure shr_record where
  shr_m : Int
  shr_r : Bool
  shr_s : Bool
  deriving DecidableEq, Repr, Inhabited

export shr_record (shr_m shr_r shr_s)

/-- Rocq's record constructor `Build_shr_record`, so a transcription of
`SpecFloat.v`'s bodies reads token for token. -/
def Build_shr_record (m : Int) (r s : Bool) : shr_record := ⟨m, r, s⟩

/-! ## Digit counts

`Section Zdigits2` of `SpecFloat.v`.  `digits2_pos` is outside the `prec`/
`emax` section's use, so it takes neither, as `Fpu.v` writes it. -/

/-- `SpecFloat.v:40-45`: the number of binary digits of a positive.  Rocq's
recursion is `xH => 1`, `xO p => succ (digits2_pos p)`, `xI p => succ
(digits2_pos p)`, which counts bits; `Nat.log2 n + 1` is the same count for
`n > 0` and is a kernel GMP primitive.  At `n = 0`, where Rocq has no input,
this gives `1`.  Rocq's `Pos.size` is defined by the same recursion, so
`Fpu.v`'s `Z.pos (Pos.size m)` is `(digits2_pos m : Int)`. -/
def digits2_pos (n : Nat) : Nat := Nat.log2 n + 1

/-- `SpecFloat.v:47-52`: `digits2_pos` of the MAGNITUDE, and `0` at `0`. -/
def Zdigits2 (n : Int) : Int :=
  if n = 0 then n else (digits2_pos n.natAbs : Int)

/-- Rocq's `Z.log2` (`IntDef.v`): `0` on `0` and on every negative, and the
index of the top bit on a positive, i.e. one less than its digit count.
Not a `SpecFloat` name; it is here because `Fpu.v`'s `fp_ew` is
`Z.log2 (fp_emax f) + 1` and the twin should hold one copy of it. -/
def Zlog2 (z : Int) : Int :=
  if 0 < z then (digits2_pos z.toNat : Int) - 1 else 0

/-! ## The exponent function

`SpecFloat.v:36-37`.  Flocq's `BinarySingleNaN.v:44-45` is
`Notation emin := (emin prec emax)` and `Notation fexp := (fexp prec emax)`,
the very same two definitions, and `Flocq/Core/FLT.v:41`'s
`FLT_exp e := Z.max (e - prec) emin` is that body again, so one `fexp` serves
`SpecFloat`, `BinarySingleNaN` and `FLT_exp` alike. -/

/-- `SpecFloat.v:36`: the exponent of the smallest subnormal. -/
def emin (prec emax : Int) : Int := 3 - emax - prec

/-- `SpecFloat.v:37`: the canonical exponent of a value whose digit count plus
exponent is `e`. -/
def fexp (prec emax e : Int) : Int := Zmax (e - prec) (emin prec emax)

/-! ## Shifting a mantissa right, with the round and sticky bits -/

/-- `SpecFloat.v:73-78`: Rocq's `iter_pos f n x` applies `f` exactly `n` times
(`xH => f x`, `xO n' => n'` twice, `xI n' => n'` twice after one `f`).  The
`Nat` version applies it `n` times too, and at `n = 0`, where Rocq has no
input, returns `x`.  Structural on `n`, so the kernel reduces it. -/
def iter_pos {A : Type} (f : A → A) : Nat → A → A
  | 0, x => x
  | n + 1, x => iter_pos f n (f x)

/-- `SpecFloat.v:86-97`: one right shift.  The sticky bit absorbs the old
round bit FIRST, then the mantissa loses its low bit and that bit becomes the
new round bit.

Rocq spells seven constructor cases.  All seven are
`Build_shr_record (trunc m 2) (odd m) (r || s)`: `Zpos (xO p) => Zpos p` and
`Zneg (xO p) => Zneg p` are truncation of an even number, `Zpos (xI p) =>
Zpos p` and `Zneg (xI p) => Zneg p` are truncation of an odd one with the
round bit set, `Zpos xH` and `Zneg xH` give `Z0` with the round bit set
(truncating `±1` by two is `0`, and `±1` is odd), and `Z0` gives `Z0` with the
round bit clear (`0` is even).  Truncation here is toward ZERO, which is why
it is `Zquot2pow` and not `Int.fdiv`. -/
def shr_1 (mrs : shr_record) : shr_record :=
  Build_shr_record (Zquot2pow mrs.shr_m 1) (!Zeven mrs.shr_m)
    (mrs.shr_r || mrs.shr_s)

/-- `SpecFloat.v:99-105`: read the location back off the two bits. -/
def loc_of_shr_record (mrs : shr_record) : location :=
  match mrs with
  | ⟨_, false, false⟩ => loc_Exact
  | ⟨_, false, true⟩ => loc_Inexact .lt
  | ⟨_, true, false⟩ => loc_Inexact .eq
  | ⟨_, true, true⟩ => loc_Inexact .gt

/-- `SpecFloat.v:107-113`: put a location into the two bits. -/
def shr_record_of_loc (m : Int) (l : location) : shr_record :=
  match l with
  | loc_Exact => Build_shr_record m false false
  | loc_Inexact .lt => Build_shr_record m false true
  | loc_Inexact .eq => Build_shr_record m true false
  | loc_Inexact .gt => Build_shr_record m true true

/-- `shr_1` applied `n` times, in closed form.

SHAPE DIFFERS FROM ROCQ, VALUE DOES NOT.  Rocq's `shr` iterates `shr_1`
`n` times (`iter_pos shr_1 p`); `shr_fexp` asks for about `prec` steps on a
normal operand and for hundreds on a subnormal one, and a `Nat`-structural
iteration of that length does not reduce cheaply in the kernel.  Unfolding the
iteration from `(m, r, s)`, with `a` the magnitude of `m`:

* the mantissa is truncated toward zero once per step, and truncation composes,
  so after `n` steps it is `m` truncated by `2 ^ n`;
* step `k` sets the round bit to bit `k-1` of `a`, so the last one leaves bit
  `n-1` of `a`;
* the sticky bit is `r || s` after the first step and absorbs the previous
  round bit at every later one, so after `n` steps it is
  `r || s || (bits 0 … n-2 of a are not all clear)`, i.e.
  `r || s || a % 2 ^ (n-1) ≠ 0`.

`shr_agrees_with_iter_pos` below pins the two against each other, over both
signs of `m`, all four `(r, s)` pairs and several `n`. -/
def shr_n (mrs : shr_record) (n : Nat) : shr_record :=
  if n = 0 then mrs
  else
    let a := mrs.shr_m.natAbs
    Build_shr_record (Zquot2pow mrs.shr_m n) (a.testBit (n - 1))
      (mrs.shr_r || mrs.shr_s || (a % 2 ^ (n - 1) != 0))

/-- `SpecFloat.v:115-119`: shift right by `n` and add `n` to the exponent, and
do nothing at all when `n` is not positive (Rocq matches `Zpos p` only). -/
def shr (mrs : shr_record) (e n : Int) : shr_record × Int :=
  if 0 < n then (shr_n mrs n.toNat, e + n) else (mrs, e)

/-- `SpecFloat.v:121-122`: shift the mantissa down to the canonical exponent
for its digit count. -/
def shr_fexp (prec emax m e : Int) (l : location) : shr_record × Int :=
  shr (shr_record_of_loc m l) e (fexp prec emax (Zdigits2 m + e) - e)

/-- `SpecFloat.v:141-145`: shift a mantissa LEFT to reach the smaller exponent
`ex'`, and do nothing when `ex'` is not smaller (Rocq matches `Zneg d`, i.e.
`ex' - ex < 0`, and then `Pos.iter xO mx d` is `mx * 2 ^ d`).  At `mx = 0`,
which Rocq's `positive` cannot hold, this returns `(0, ex')` or `(0, ex)`, the
natural extension; no caller passes it. -/
def shl_align (mx : Nat) (ex ex' : Int) : Nat × Int :=
  if ex' - ex < 0 then (mx * 2 ^ (ex - ex').toNat, ex') else (mx, ex)

/-! ## Locations from a remainder -/

/-- `SpecFloat.v:295-297`. -/
def new_location_even (nb_steps k : Int) : location :=
  if k = 0 then loc_Exact else loc_Inexact (Zcompare (2 * k) nb_steps)

/-- `SpecFloat.v:299-307`.  The midpoint of an odd step count cannot be hit, so
`Eq` is folded into `Lt`. -/
def new_location_odd (nb_steps k : Int) : location :=
  if k = 0 then loc_Exact
  else
    loc_Inexact
      (match Zcompare (2 * k + 1) nb_steps with
       | .lt => .lt
       | .eq => .lt
       | .gt => .gt)

/-- `SpecFloat.v:309-310`.  Rocq partially applies the chosen branch to
`nb_steps`; here both arguments are taken, which is how `Fpu.v` calls it
(`new_location d r`). -/
def new_location (nb_steps k : Int) : location :=
  if Zeven nb_steps then new_location_even nb_steps k else new_location_odd nb_steps k

/-! ## Comparison -/

/-- `SpecFloat.v:177-209`.  `None` is "unordered".  Rocq's `CompOpp` on the
negative-negative branch is `Ordering.swap`, and `Pos.compare_cont Eq m1 m2`
is `compare` on the `Nat` mantissas. -/
def SFcompare (f1 f2 : spec_float) : Option Ordering :=
  match f1, f2 with
  | S754_nan, _ => none
  | _, S754_nan => none
  | S754_infinity s1, S754_infinity s2 =>
    some
      (match s1, s2 with
       | true, true => .eq
       | false, false => .eq
       | true, false => .lt
       | false, true => .gt)
  | S754_infinity s, _ => some (if s then .lt else .gt)
  | _, S754_infinity s => some (if s then .gt else .lt)
  | S754_finite s _ _, S754_zero _ => some (if s then .lt else .gt)
  | S754_zero _, S754_finite s _ _ => some (if s then .gt else .lt)
  | S754_zero _, S754_zero _ => some .eq
  | S754_finite s1 m1 e1, S754_finite s2 m2 e2 =>
    some
      (match s1, s2 with
       | true, false => .lt
       | false, true => .gt
       | false, false =>
         match Zcompare e1 e2 with
         | .lt => .lt
         | .gt => .gt
         | .eq => compare m1 m2
       | true, true =>
         match Zcompare e1 e2 with
         | .lt => .gt
         | .gt => .lt
         | .eq => (compare m1 m2).swap)

/-! ## Division and square root cores -/

/-- `SpecFloat.v:312-324`.  Aligns the dividend so the quotient has enough
digits, divides, and reads the location off the remainder.  The division is
Rocq's `Z.div_eucl`; both operands are non-negative where `Fpu.v` calls this,
but the floor convention is kept anyway. -/
def SFdiv_core_binary (prec emax m1 e1 m2 e2 : Int) : Int × Int × location :=
  let d1 := Zdigits2 m1
  let d2 := Zdigits2 m2
  let e' := Zmin (fexp prec emax (d1 + e1 - (d2 + e2))) (e1 - e2)
  let s := e1 - e2 - e'
  let m' := if 0 < s then Zshiftl m1 s else if s = 0 then m1 else 0
  let (q, r) := Zdiv_eucl m' m2
  (q, e', new_location m2 r)

/-- Newton's method for `Nat.sqrt`, descending from a start that is at least
the answer.  Structural on `fuel`, so the kernel reduces it.

SHAPE DIFFERS FROM ROCQ, VALUE DOES NOT.  Rocq's `Z.sqrtrem` calls
`Pos.sqrtrem`, a recursion over the binary digits of the argument; Lean core's
`Nat.sqrt` is well-founded and does NOT reduce in the kernel, so neither is
usable here.  From a guess `g ≥ ⌊√n⌋ > 0` the step `g' = (g + n / g) / 2`
stays `≥ ⌊√n⌋` and strictly decreases until `g = ⌊√n⌋`, where it stops; the
caller starts at `2 ^ ((digits2_pos n + 1) / 2)`, which is `≥ √n` and within a
factor of two of it, so the quadratic convergence reaches the answer in far
fewer than `fuel` steps for any argument this file can produce (the largest is
a few thousand bits). -/
def natSqrtAux : Nat → Nat → Nat → Nat
  | 0, _, g => g
  | fuel + 1, n, g =>
    let g' := (g + n / g) / 2
    if g' < g then natSqrtAux fuel n g' else g

/-- `⌊√n⌋`. -/
def natSqrt (n : Nat) : Nat :=
  if n = 0 then 0 else natSqrtAux 128 n (2 ^ ((digits2_pos n + 1) / 2))

/-- Rocq's `Z.sqrtrem` (`IntDef.v:337-346`): `(⌊√n⌋, n - ⌊√n⌋²)` on a
positive, and `(0, 0)` on `0` and on every NEGATIVE. -/
def Zsqrtrem (n : Int) : Int × Int :=
  if n ≤ 0 then (0, 0)
  else
    let s := natSqrt n.toNat
    ((s : Int), n - ((s * s : Nat) : Int))

/-- `SpecFloat.v:342-356`.  Note the two `Z.div2`, which are FLOOR divisions
and are applied to exponents that are routinely negative. -/
def SFsqrt_core_binary (prec emax m e : Int) : Int × Int × location :=
  let d := Zdigits2 m
  let e' := Zmin (fexp prec emax (Zdiv2 (d + e + 1))) (Zdiv2 e)
  let s := e - 2 * e'
  let m' := if 0 < s then Zshiftl m s else if s = 0 then m else 0
  let (q, r) := Zsqrtrem m'
  let l := if r = 0 then loc_Exact else loc_Inexact (if r ≤ q then .lt else .gt)
  (q, e', l)

/-! ## Flocq's rounding modes and rounding kernel

`coq-flocq 4.2.2:Flocq/IEEE754/BinarySingleNaN.v`, with the three location
helpers it imports from `coq-flocq 4.2.2:Flocq/Calc/Round.v`. -/

/-- `Calc/Round.v:115`. -/
def cond_incr (b : Bool) (m : Int) : Int := if b then m + 1 else m

/-- `Calc/Round.v:415-421`: round to nearest, with `p` deciding the tie. -/
def round_N (p : Bool) (l : location) : Bool :=
  match l with
  | loc_Exact => false
  | loc_Inexact .lt => false
  | loc_Inexact .eq => p
  | loc_Inexact .gt => true

/-- `Calc/Round.v:180-184`: round toward `-∞`, on a magnitude with the sign
supplied separately. -/
def round_sign_DN (s : Bool) (l : location) : Bool :=
  match l with
  | loc_Exact => false
  | _ => s

/-- `Calc/Round.v:273-277`: round toward `+∞`, likewise. -/
def round_sign_UP (s : Bool) (l : location) : Bool :=
  match l with
  | loc_Exact => false
  | _ => !s

/-- `BinarySingleNaN.v:1129`: the five IEEE rounding modes. -/
inductive mode where
  | mode_NE
  | mode_ZR
  | mode_DN
  | mode_UP
  | mode_NA
  deriving DecidableEq, Repr, Inhabited

export mode (mode_NE mode_ZR mode_DN mode_UP mode_NA)

/-- `BinarySingleNaN.v:1140-1147`: whether the rounded magnitude is `mx` or
`mx + 1`.  Rocq's `negb (Z.even mx)` is the even-tie test for `mode_NE`. -/
def choice_mode (m : mode) (sx : Bool) (mx : Int) (lx : location) : Int :=
  match m with
  | mode_NE => cond_incr (round_N (!Zeven mx) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx

/-- `BinarySingleNaN.v:1173-1180`: whether an overflow delivers an infinity or
the largest finite number. -/
def overflow_to_inf (m : mode) (s : Bool) : Bool :=
  match m with
  | mode_NE => true
  | mode_NA => true
  | mode_ZR => false
  | mode_UP => !s
  | mode_DN => s

/-- `BinarySingleNaN.v:1182-1184`: the overflowed result.  Rocq writes the
finite case `S754_finite s (Z.to_pos (2 ^ prec - 1)) (emax - prec)`; the
mantissa is a `Nat` here, computed as `2 ^ prec - 1`.  Rocq's section carries
`Prec_gt_0 prec`, so `prec > 0` is a precondition of this definition, and at
`prec ≤ 0` the two differ (`Z.to_pos (-1)` is `1` in Rocq, `0` here). -/
def binary_overflow (prec emax : Int) (m : mode) (s : Bool) : spec_float :=
  if overflow_to_inf m s then S754_infinity s
  else S754_finite s (2 ^ prec.toNat - 1) (emax - prec)

/-- `BinarySingleNaN.v:1229-1231`: deliver the rounded datum, or overflow.  At
`mx = 0`, which Rocq's `positive` cannot hold, this returns
`S754_finite sx 0 ex`, the natural extension; no caller passes it. -/
def binary_fit_aux (prec emax : Int) (m : mode) (sx : Bool) (mx : Nat) (ex : Int) :
    spec_float :=
  if ex ≤ emax - prec then S754_finite sx mx ex else binary_overflow prec emax m sx

/-- `BinarySingleNaN.v:1270-1277`: the rounding kernel.  Shift the operand to
its canonical exponent, apply the mode to the resulting magnitude and
location, and normalize once more in case rounding up carried out of the
mantissa.  Rocq's final match is on `Z0` / `Zpos m` / `_`; the negative case is
unreachable because mantissas are non-negative, and Rocq returns `S754_nan`
there, as this does. -/
def binary_round_aux (prec emax : Int) (m : mode) (sx : Bool) (mx ex : Int)
    (lx : location) : spec_float :=
  let (mrs', e') := shr_fexp prec emax mx ex lx
  let (mrs'', e'') :=
    shr_fexp prec emax (choice_mode m sx mrs'.shr_m (loc_of_shr_record mrs')) e' loc_Exact
  let mz := mrs''.shr_m
  if mz = 0 then S754_zero sx
  else if 0 < mz then binary_fit_aux prec emax m sx mz.toNat e''
  else S754_nan

/-! ## Pins

Rocq's `Example … Proof. vm_compute. reflexivity. Qed.` is `by decide` here.
Every function above whose Rocq convention could disagree with Lean's `Int`
division, shifting or parity carries a NEGATIVE case, because that is where
the three conventions (`Int./` Euclidean, `Int.fdiv` floor, truncation toward
zero) part company. -/

/-- The three `Int` division conventions really do disagree, which is why no
definition above uses `/` or `%` on `Int`. -/
example : (-7 : Int) / 2 = -4 := by decide
example : Int.fdiv (-7) 2 = -4 := by decide
example : Int.tdiv (-7) 2 = -3 := by decide
example : (7 : Int) / (-2) = -3 := by decide
example : Int.fdiv 7 (-2) = -4 := by decide

-- `Zmax`/`Zmin`, including across zero.
example : Zmax (-5) (-7) = -5 := by decide
example : Zmin (-5) (-7) = -7 := by decide
example : Zmax (-5) 3 = 3 := by decide

-- `Zeven`: Rocq's `Z.even` is true on both signs of an even magnitude.
example : Zeven (-4) = true := by decide
example : Zeven (-3) = false := by decide
example : Zeven 0 = true := by decide

-- `Zdiv2` rounds toward bottom: `-3` halves to `-2`, not `-1`.
example : Zdiv2 (-3) = -2 := by decide
example : Zdiv2 (-4) = -2 := by decide
example : Zdiv2 (-1) = -1 := by decide
example : Zdiv2 7 = 3 := by decide

-- `Zquot2pow` truncates toward zero: `-7` by two is `-3`, not `-4`.
example : Zquot2pow (-7) 1 = -3 := by decide
example : Zquot2pow (-7) 2 = -1 := by decide
example : Zquot2pow (-1) 1 = 0 := by decide
example : Zquot2pow 7 2 = 1 := by decide

-- `Zdiv_eucl`: quotient toward bottom, remainder with the DIVISOR's sign,
-- and Rocq's two zero cases.
example : Zdiv_eucl (-7) 2 = (-4, 1) := by decide
example : Zdiv_eucl 7 (-2) = (-4, -1) := by decide
example : Zdiv_eucl (-7) (-2) = (3, -1) := by decide
example : Zdiv_eucl 7 2 = (3, 1) := by decide
example : Zdiv_eucl (-7) 0 = (0, -7) := by decide
example : Zdiv_eucl 0 (-7) = (0, 0) := by decide

-- `Zshiftl`: left on a negative value, and right (negative count) rounding
-- toward bottom, which is Rocq's iterated `Z.div2`.
example : Zshiftl (-3) 2 = -12 := by decide
example : Zshiftl (-7) (-1) = -4 := by decide
example : Zshiftl 7 (-1) = 3 := by decide
example : Zshiftl 1 10 = 1024 := by decide

-- `digits2_pos` is `Pos.size`, and `Zdigits2` counts the MAGNITUDE's digits.
example : digits2_pos 1 = 1 := by decide
example : digits2_pos 2 = 2 := by decide
example : digits2_pos 3 = 2 := by decide
example : digits2_pos 255 = 8 := by decide
example : digits2_pos 256 = 9 := by decide
example : Zdigits2 0 = 0 := by decide
example : Zdigits2 (-5) = 3 := by decide
example : Zdigits2 5 = 3 := by decide
example : Zdigits2 (-(2 ^ 52)) = 53 := by decide

-- A wide argument stays cheap for the kernel, which is the point of routing
-- the digit count through `Nat.log2` and the powers through `Nat.pow`.
set_option exponentiation.threshold 2048 in
example : digits2_pos (2 ^ 300) = 301 := by decide
set_option exponentiation.threshold 2048 in
example : twoPow 300 = (2 : Int) ^ 300 := by decide

-- `Zlog2`: `0` on `0` and on negatives.
example : Zlog2 (-8) = 0 := by decide
example : Zlog2 0 = 0 := by decide
example : Zlog2 1 = 0 := by decide
example : Zlog2 128 = 7 := by decide
-- The two `fp_ew` that `Fpu.v` asks for.
example : Zlog2 128 + 1 = 8 := by decide
example : Zlog2 1024 + 1 = 11 := by decide

-- `fexp`/`emin` for binary32 and binary64.  `fexp` is the LARGER of
-- `e - prec` and `emin`, so the third binary64 case below is the one where
-- the subnormal floor wins.
example : emin 24 128 = -149 := by decide
example : emin 53 1024 = -1074 := by decide
example : fexp 24 128 0 = -24 := by decide
example : fexp 53 1024 0 = -53 := by decide
example : fexp 53 1024 (-1000) = -1053 := by decide
example : fexp 53 1024 (-1030) = -1074 := by decide
example : fexp 53 1024 1024 = 971 := by decide

-- `shr_1` over all seven of Rocq's constructor cases.
example : shr_1 (Build_shr_record 0 false false) = Build_shr_record 0 false false := by decide
example : shr_1 (Build_shr_record 1 false false) = Build_shr_record 0 true false := by decide
example : shr_1 (Build_shr_record (-1) false false) = Build_shr_record 0 true false := by decide
example : shr_1 (Build_shr_record 6 false false) = Build_shr_record 3 false false := by decide
example : shr_1 (Build_shr_record 7 false false) = Build_shr_record 3 true false := by decide
example : shr_1 (Build_shr_record (-6) false false) = Build_shr_record (-3) false false := by decide
example : shr_1 (Build_shr_record (-7) false false) = Build_shr_record (-3) true false := by decide
-- The sticky bit absorbs the OLD round bit.
example : shr_1 (Build_shr_record 4 true false) = Build_shr_record 2 false true := by decide

/-- The closed-form `shr_n` against Rocq's `iter_pos shr_1`, over both signs of
the mantissa, all four `(round, sticky)` pairs and the shift counts `1 … 6`.
This is the pin for the one place where this file's shape departs from
`SpecFloat.v`'s. -/
example :
    (List.range 7 |>.all fun n =>
      [(-13 : Int), -8, -1, 0, 1, 8, 13, 255, -255].all fun m =>
        [(false, false), (false, true), (true, false), (true, true)].all
          fun rs => shr_n (Build_shr_record m rs.1 rs.2) n
                      == iter_pos shr_1 n (Build_shr_record m rs.1 rs.2))
      = true := by
  decide

-- `shr` itself: no shift unless `n` is positive, and the exponent moves by `n`.
example : shr (Build_shr_record 13 false false) 5 0 = (Build_shr_record 13 false false, 5) := by
  decide
example : shr (Build_shr_record 13 false false) 5 (-3) = (Build_shr_record 13 false false, 5) := by
  decide
example : shr (Build_shr_record 13 false false) 5 2 = (Build_shr_record 3 false true, 7) := by
  decide
example : shr (Build_shr_record (-13) false false) (-5) 2 = (Build_shr_record (-3) false true, -3) := by
  decide

-- `loc_of_shr_record` and `shr_record_of_loc` are inverse on the two bits.
example : loc_of_shr_record (Build_shr_record 9 true true) = loc_Inexact .gt := by decide
example : shr_record_of_loc 9 (loc_Inexact .eq) = Build_shr_record 9 true false := by decide
example :
    ([loc_Exact, loc_Inexact .lt, loc_Inexact .eq, loc_Inexact .gt].all fun l =>
      loc_of_shr_record (shr_record_of_loc (-9) l) == l) = true := by
  decide

-- `shr_fexp` at a negative exponent, binary64: an operand whose digit count
-- puts it ABOVE the canonical exponent is shifted down to it, the discarded
-- bits become the location, and the exponent rises by the shift.
example : shr_fexp 53 1024 (2 ^ 54) (-1) loc_Exact
    = (Build_shr_record (2 ^ 52) false false, 1) := by decide
example : shr_fexp 53 1024 ((2 ^ 54) + 1) (-1) loc_Exact
    = (Build_shr_record (2 ^ 52) false true, 1) := by decide
example : shr_fexp 53 1024 1 (-1200) loc_Exact
    = (Build_shr_record 0 false true, -1074) := by decide

-- `shl_align`: left only, and only when the target exponent is smaller.
example : shl_align 3 (-5) (-8) = (24, -8) := by decide
example : shl_align 3 (-5) (-5) = (3, -5) := by decide
example : shl_align 3 (-5) (-2) = (3, -5) := by decide

-- `new_location` on an even and on an odd step count, including the midpoint.
example : new_location 8 0 = loc_Exact := by decide
example : new_location 8 3 = loc_Inexact .lt := by decide
example : new_location 8 4 = loc_Inexact .eq := by decide
example : new_location 8 5 = loc_Inexact .gt := by decide
example : new_location 7 3 = loc_Inexact .lt := by decide
example : new_location 7 4 = loc_Inexact .gt := by decide

-- `SFcompare`, including the negative branch Rocq flips with `CompOpp`.
example : SFcompare S754_nan (S754_zero false) = none := by decide
example : SFcompare (S754_zero true) (S754_zero false) = some .eq := by decide
example : SFcompare (S754_infinity true) (S754_infinity false) = some .lt := by decide
example : SFcompare (S754_finite true 5 0) (S754_zero false) = some .lt := by decide
example : SFcompare (S754_finite true 5 0) (S754_finite true 4 0) = some .lt := by decide
example : SFcompare (S754_finite false 5 0) (S754_finite false 4 0) = some .gt := by decide
example : SFcompare (S754_finite true 5 0) (S754_finite true 5 1) = some .gt := by decide
example : SFcompare (S754_finite true 5 0) (S754_finite false 5 0) = some .lt := by decide

-- `natSqrt`/`Zsqrtrem`, with Rocq's `(0, 0)` on a negative argument.
example : natSqrt 0 = 0 := by decide
example : natSqrt 1 = 1 := by decide
example : natSqrt 2 = 1 := by decide
example : natSqrt 10 = 3 := by decide
example : natSqrt 16 = 4 := by decide
example : natSqrt 9999 = 99 := by decide
example : natSqrt (2 ^ 106) = 2 ^ 53 := by decide
example : Zsqrtrem (-4) = (0, 0) := by decide
example : Zsqrtrem 0 = (0, 0) := by decide
example : Zsqrtrem 10 = (3, 1) := by decide
example : Zsqrtrem 16 = (4, 0) := by decide

-- `choice_mode`: the sign argument is the sign of the MAGNITUDE's value, and
-- `mode_NE` ties on the magnitude's parity.
example : choice_mode mode_NE false 4 (loc_Inexact .eq) = 4 := by decide
example : choice_mode mode_NE false 5 (loc_Inexact .eq) = 6 := by decide
example : choice_mode mode_NA false 4 (loc_Inexact .eq) = 5 := by decide
example : choice_mode mode_ZR true 5 (loc_Inexact .gt) = 5 := by decide
example : choice_mode mode_DN true 5 (loc_Inexact .lt) = 6 := by decide
example : choice_mode mode_DN false 5 (loc_Inexact .lt) = 5 := by decide
example : choice_mode mode_UP true 5 (loc_Inexact .lt) = 5 := by decide
example : choice_mode mode_UP false 5 (loc_Inexact .lt) = 6 := by decide
example : choice_mode mode_UP false 5 loc_Exact = 5 := by decide
-- A negative mantissa still has its parity read as Rocq reads it.
example : choice_mode mode_NE false (-5) (loc_Inexact .eq) = -4 := by decide

-- `binary_overflow` for binary64: `±inf` or `±MAXFLOAT`, by mode and sign.
example : binary_overflow 53 1024 mode_NE true = S754_infinity true := by decide
example : binary_overflow 53 1024 mode_ZR true = S754_finite true (2 ^ 53 - 1) 971 := by decide
example : binary_overflow 53 1024 mode_DN false = S754_finite false (2 ^ 53 - 1) 971 := by decide
example : binary_overflow 53 1024 mode_DN true = S754_infinity true := by decide
example : binary_overflow 53 1024 mode_UP false = S754_infinity false := by decide
example : binary_overflow 53 1024 mode_UP true = S754_finite true (2 ^ 53 - 1) 971 := by decide

-- `binary_fit_aux` at the boundary exponent.
example : binary_fit_aux 53 1024 mode_NE false 5 971 = S754_finite false 5 971 := by decide
example : binary_fit_aux 53 1024 mode_NE false 5 972 = S754_infinity false := by decide

-- `binary_round_aux`, binary64.  Exact; one ulp below a tie, rounding down;
-- a tie rounding to even; the carry out of the mantissa; underflow to zero;
-- and overflow.
example : binary_round_aux 53 1024 mode_NE false (2 ^ 52) 0 loc_Exact
    = S754_finite false (2 ^ 52) 0 := by decide
example : binary_round_aux 53 1024 mode_NE false (2 ^ 53) (-1) loc_Exact
    = S754_finite false (2 ^ 52) 0 := by decide
example : binary_round_aux 53 1024 mode_NE false (2 * (2 ^ 53) + 1) (-2) loc_Exact
    = S754_finite false (2 ^ 52) 0 := by decide
example : binary_round_aux 53 1024 mode_NE false (2 * (2 ^ 53) + 3) (-2) loc_Exact
    = S754_finite false (2 ^ 52 + 1) 0 := by decide
example : binary_round_aux 53 1024 mode_UP false (2 * (2 ^ 53) + 1) (-2) loc_Exact
    = S754_finite false (2 ^ 52 + 1) 0 := by decide
example : binary_round_aux 53 1024 mode_DN false (2 * (2 ^ 53) + 1) (-2) loc_Exact
    = S754_finite false (2 ^ 52) 0 := by decide
example : binary_round_aux 53 1024 mode_NE true (2 ^ 54 - 1) 0 loc_Exact
    = S754_finite true (2 ^ 52) 2 := by decide
example : binary_round_aux 53 1024 mode_NE false 1 (-1200) loc_Exact
    = S754_zero false := by decide
example : binary_round_aux 53 1024 mode_NE false 1 2000 loc_Exact
    = S754_infinity false := by decide
example : binary_round_aux 53 1024 mode_ZR false 1 2000 loc_Exact
    = S754_finite false (2 ^ 53 - 1) 971 := by decide
-- The smallest subnormal, and half of it rounding to even (to zero).
example : binary_round_aux 53 1024 mode_NE false 1 (-1074) loc_Exact
    = S754_finite false 1 (-1074) := by decide
example : binary_round_aux 53 1024 mode_NE false 1 (-1075) loc_Exact
    = S754_zero false := by decide
example : binary_round_aux 53 1024 mode_UP false 1 (-1075) loc_Exact
    = S754_finite false 1 (-1074) := by decide

-- `SFdiv_core_binary`, binary64: an exact quotient, and `1/3`, whose exact
-- value sits just below the midpoint between two mantissas.
example : SFdiv_core_binary 53 1024 (2 ^ 52) 0 1 0 = (2 ^ 53, -1, loc_Exact) := by decide
example : SFdiv_core_binary 53 1024 1 0 3 0 = (6004799503160661, -54, loc_Inexact .lt) := by
  decide
example : binary_round_aux 53 1024 mode_NE false
      (SFdiv_core_binary 53 1024 1 0 3 0).1
      (SFdiv_core_binary 53 1024 1 0 3 0).2.1
      (SFdiv_core_binary 53 1024 1 0 3 0).2.2
    = S754_finite false 6004799503160661 (-54) := by decide

-- `SFsqrt_core_binary`, binary64, at a negative exponent (the `Z.div2` floor
-- cases): the exact `sqrt 4`, and `sqrt 2`, whose exact value sits above the
-- midpoint so the kernel rounds the mantissa up.
example : SFsqrt_core_binary 53 1024 (2 ^ 54) (-52) = (2 ^ 52, -51, loc_Exact) := by decide
example : SFsqrt_core_binary 53 1024 (2 ^ 53) (-52)
    = (6369051672525772, -52, loc_Inexact .gt) := by decide
example : binary_round_aux 53 1024 mode_NE false
      (SFsqrt_core_binary 53 1024 (2 ^ 53) (-52)).1
      (SFsqrt_core_binary 53 1024 (2 ^ 53) (-52)).2.1
      (SFsqrt_core_binary 53 1024 (2 ^ 53) (-52)).2.2
    = S754_finite false 6369051672525773 (-52) := by decide

end LinuxProcessSemantics.Riscv.SpecFloat
