-- Ports rocq-linux-process-semantics f1006fe8:theories/Riscv/Fpu.v
import LinuxProcessSemantics.Riscv.SpecFloat

/-! # Fpu: IEEE-754 binary arithmetic with RISC-V exception flags

Mirrors `theories/Riscv/Fpu.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

`Sem` needs FP operations that return BOTH a result and the five IEEE
exception flags, because in RISC-V the flags are architectural: they
accrue into fcsr[4:0], a program can read them with `csrr fflags`, and a
compiler is free to branch on them.  A semantics that produced only the
value would be unsound the moment a binary looked at fflags.

The value half is not reinvented here.  Rounding is `binary_round_aux`,
the rounding kernel of the Flocq library's binary-float development: it
takes a sign, an unrounded mantissa, an exponent and a LOCATION (where
the exact value sits relative to the two candidate mantissas), and
returns the correctly rounded `spec_float` — the payload-free IEEE datum
of the standard library's `SpecFloat`.  Flocq proves that kernel equal to
real-number rounding, and `round_aux_value` below pins our flag-carrying
restatement to it, so the value this file computes is exactly the value
Flocq's theorem is about.

The flag half is ours, and it is derived from the same intermediate the
kernel rounds from:

- NX (inexact): the location after aligning the operand to the target's
  canonical exponent is not `loc_Exact`.  That is literally "some bits
  were discarded", i.e. the rounded result differs from the exact one.
- OF (overflow): the rounded exponent exceeds `emax - prec`, the same
  test the kernel uses to choose between a finite result and
  `binary_overflow`.  Overflow always implies NX.  Which of ±inf and
  ±MAXFLOAT comes out is `binary_overflow`'s business and is
  rounding-mode dependent (RTZ never produces an infinity; RDN/RUP
  produce one only on the side they round away to).
- UF (underflow): TINY AND INEXACT, with tininess detected AFTER
  rounding — the IEEE option RISC-V mandates.  "After rounding" means
  rounding to `prec` bits AS THOUGH THE EXPONENT RANGE WERE UNBOUNDED
  and asking whether that magnitude stays strictly below the smallest
  normal.  That is NOT the same as "the delivered result is subnormal":
  just below the smallest normal the unbounded grid is twice as fine as
  the subnormal grid, so a value in the lower part of that last gap can
  carry up to the smallest normal under the real (bounded) rounding
  while the unbounded-range rounding stays tiny — UF is raised even
  though the delivered result is normal.  `round_tiny` implements the
  unbounded-range rounding.
- NV (invalid) and DZ (divide by zero) never come from rounding; they
  are raised by the special-case dispatch of each operation (0×inf,
  inf−inf, sqrt of a negative, a signalling NaN operand, a finite
  nonzero divided by zero, an out-of-range float→int).

RISC-V specifics that this file, not the IEEE kernel, decides:

- Every NaN RESULT is the canonical quiet NaN (sign 0, exponent all
  ones, mantissa = the quiet bit alone).  RISC-V does not propagate
  payloads, which is why `spec_float`'s payload-free `S754_nan` is the
  right datum and why NaN-ness alone is not enough state to carry:
  signalling-ness has to be read off the BIT PATTERN before decoding
  (`fp_is_snan`), since decoding forgets it.
- fmin/fmax return the non-NaN operand when exactly one operand is NaN,
  and raise NV only for a SIGNALLING NaN; −0 is ordered below +0, which
  a bitwise comparison would get wrong.
- feq is a QUIET compare (NV only on a signalling NaN); flt/fle are
  SIGNALLING (NV on any NaN).
- float→int saturates: out-of-range, infinite and NaN inputs produce the
  nearest representable integer and raise NV, and NV SUPPRESSES NX — a
  saturated conversion reports one problem, not two.

Everything here is a computation over `Int` (Rocq's `Z`) on RAW BIT
PATTERNS of the format's width (32 or 64).  Register width, NaN boxing
and the fcsr update belong to `Sem`; this file never sees a bitvector.

## Lean-side shapes

- Rocq `Z` is `Int`, Rocq `bool` is `Bool`, and Rocq `positive` is `Nat`
  with the invariant "strictly positive" — the convention
  `Riscv/SpecFloat.lean` fixes for `S754_finite`'s mantissa.  Rocq's
  `Zpos p` match arms are therefore written as an explicit positivity
  test followed by `Int.toNat`, which computes the same datum; the three
  places this happens (`fp_decode`, `round_aux`, `round_scaled`) say so.
- Rocq's `Pos.size` and `SpecFloat`'s `digits2_pos` are the same
  function (both count binary digits), so `fp_encode` uses
  `digits2_pos`.
- Rocq's `comparison` is Lean's `Ordering`, as `SpecFloat.SFcompare`
  returns it.
- `Z.shiftl`, `Z.log2`, `Z.div_eucl` and `Z.min` are `SpecFloat`'s
  `Zshiftl`, `Zlog2`, `Zdiv_eucl` and `Zmin`.  The four bit operations
  `SpecFloat` does not need are below.
-/

namespace LinuxProcessSemantics.Riscv.Fpu

open LinuxProcessSemantics.Riscv.SpecFloat

/-! ## The `Z` bit operations this file adds

Lean core gives `Int` no bitwise operations.  `SpecFloat` ports the ones
its own definitions need; the four below are used only here, and carry
Rocq's semantics: a two's-complement reading extended infinitely to the
left, which for a negative `Int` is `Int.negSucc n = ~n`.

Every call site passes a non-negative bit index or width, which is where
`Int.toNat` agrees with Rocq's `Z.to_nat`. -/

/-- Rocq's `Z.ones n` for `0 ≤ n`: the low `n` bits set. -/
def Zones (n : Int) : Int := twoPow n.toNat - 1

/-- Rocq's `Z.shiftr`.  Rocq defines it as `Z.shiftl` with the count
negated, which is exactly `SpecFloat.Zshiftl`'s negative branch: an
ARITHMETIC shift, i.e. division by `2 ^ n` rounding toward minus
infinity. -/
def Zshiftr (x n : Int) : Int := Zshiftl x (-n)

/-- Rocq's `Z.testbit` for a non-negative index. -/
def Ztestbit (x i : Int) : Bool :=
  match x with
  | .ofNat n => n.testBit i.toNat
  | .negSucc n => !(n.testBit i.toNat)

/-- Rocq's `Z.land`.  `Int.negSucc n` is the bit pattern `~n`, so the
mixed cases are `m &&& ~n = m - (m &&& n)` and `~m &&& ~n = ~(m ||| n)`. -/
def Zland (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => Int.ofNat (m &&& n)
  | .ofNat m, .negSucc n => Int.ofNat (m - (m &&& n))
  | .negSucc m, .ofNat n => Int.ofNat (n - (m &&& n))
  | .negSucc m, .negSucc n => Int.negSucc (m ||| n)

/-- Rocq's `Z.lxor`.  `~m ^^^ n = ~(m ^^^ n)` and `~m ^^^ ~n = m ^^^ n`. -/
def Zlxor (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => Int.ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => Int.negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => Int.negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => Int.ofNat (m ^^^ n)

/-! ## Formats

A binary format is pinned by `prec` (significand bits, including the
implicit leading one) and `emax` (the exponent of the infinities); every
other constant is derived, so there is one place to look and no way for
the two formats to disagree about their own layout.  `fp_emin` is the
exponent of the SMALLEST SUBNORMAL, which is the exponent `SpecFloat`
gives every subnormal datum — not the smallest normal exponent. -/

/-- Rocq's `Record format := Fmt { fp_prec : Z; fp_emax : Z }`. -/
structure format where
  Fmt ::
  fp_prec : Int
  fp_emax : Int
  deriving DecidableEq, Repr, Inhabited

def fmt_single : format := format.Fmt 24 128
def fmt_double : format := format.Fmt 53 1024

/-- Mantissa field width. -/
def fp_mw (f : format) : Int := f.fp_prec - 1
/-- Exponent field width. -/
def fp_ew (f : format) : Int := Zlog2 f.fp_emax + 1
def fp_emin (f : format) : Int := 3 - f.fp_emax - f.fp_prec

/-! ## Exception flags

The five IEEE flags, in the fcsr[4:0] bit order RISC-V assigns them.
Kept as a record rather than a bitmask so that every operation below has
to name the flags it raises; `fflags_bits` is the single place the
encoding is spelled. -/

/-- Rocq's `Record fflags := Fflags { … }`. -/
structure fflags where
  Fflags ::
  /-- invalid operation -/
  fl_nv : Bool
  /-- divide by zero -/
  fl_dz : Bool
  /-- overflow -/
  fl_of : Bool
  /-- underflow -/
  fl_uf : Bool
  /-- inexact -/
  fl_nx : Bool
  deriving DecidableEq, Repr, Inhabited

def no_flags : fflags := fflags.Fflags false false false false false
def nv_flag : fflags := fflags.Fflags true false false false false
def dz_flag : fflags := fflags.Fflags false true false false false
def nx_flag : fflags := fflags.Fflags false false false false true

def fflags_bits (fl : fflags) : Int :=
  let b (p : Bool) (i : Int) : Int := if p then Zshiftl 1 i else 0
  b fl.fl_nx 0 + b fl.fl_uf 1 + b fl.fl_of 2
  + b fl.fl_dz 3 + b fl.fl_nv 4

/-! ## Rounding modes

The five architectural modes.  The instruction's 3-bit rm field also has
the DYNAMIC encoding 7 (use fcsr's frm) and two RESERVED encodings, 5 and
6; `rmode_of_field` returns `none` for those, and for a dynamic rm whose
frm is itself reserved.  `none` is an ILLEGAL INSTRUCTION at the `Sem`
level, not a defaulted mode: executing a reserved rounding mode as if it
were round-to-nearest would give a wrong answer silently, where trapping
is what real hardware does. -/

inductive rmode : Type
  | RNE | RTZ | RDN | RUP | RMM
  deriving DecidableEq, Repr, Inhabited

export rmode (RNE RTZ RDN RUP RMM)

def rmode_of_Z (z : Int) : Option rmode :=
  if z == 0 then some RNE
  else if z == 1 then some RTZ
  else if z == 2 then some RDN
  else if z == 3 then some RUP
  else if z == 4 then some RMM
  else none

/-- `rm` is the instruction field, `frm` the fcsr rounding mode. -/
def rmode_of_field (rm frm : Int) : Option rmode :=
  if rm == 7 then rmode_of_Z frm else rmode_of_Z rm

def flocq_mode (m : rmode) : mode :=
  match m with
  | RNE => mode_NE
  | RTZ => mode_ZR
  | RDN => mode_DN
  | RUP => mode_UP
  | RMM => mode_NA

/-! ## Bit patterns

Decode and encode the interchange format by hand: the standard library's
`spec_float` is an abstract datum with no layout, and the layout is
exactly what an ISA semantics has to be explicit about.  `digits2_pos`
is the number of significant bits of a positive (Rocq writes `Pos.size`
here, the same function), which is how a subnormal RESULT is recognized
on the way out (fewer than `prec` significant bits, which for a
canonical datum can only happen at the minimum exponent). -/

def fp_sign_bit (f : format) (x : Int) : Bool :=
  Ztestbit x (fp_mw f + fp_ew f)
def fp_exp_field (f : format) (x : Int) : Int :=
  Zland (Zshiftr x (fp_mw f)) (Zones (fp_ew f))
def fp_man_field (f : format) (x : Int) : Int :=
  Zland x (Zones (fp_mw f))

/-- Rocq matches the mantissa against `Zpos p`; `positive` is `Nat` here,
so the test is written out and `Int.toNat` takes the place of the match's
binder.  Same cases, same datum: the fall-through arm is Rocq's, for a
mantissa that is not strictly positive. -/
def fp_decode (f : format) (x : Int) : spec_float :=
  let s := fp_sign_bit f x
  let e := fp_exp_field f x
  let m := fp_man_field f x
  if e == 0 then
    (if 0 < m then S754_finite s m.toNat (fp_emin f) else S754_zero s)
  else if e == Zones (fp_ew f) then
    (if m == 0 then S754_infinity s else S754_nan)
  else
    let im := Zshiftl 1 (fp_mw f) + m
    -- unreachable `S754_nan`: the implicit bit makes `im` positive
    (if 0 < im then S754_finite s im.toNat (e + fp_emin f - 1) else S754_nan)

/-- The one NaN this semantics ever produces. -/
def fp_canonical_nan (f : format) : Int :=
  Zshiftl (Zones (fp_ew f)) (fp_mw f) + Zshiftl 1 (fp_mw f - 1)

def fp_encode (f : format) (x : spec_float) : Int :=
  let sb (s : Bool) : Int := if s then Zshiftl 1 (fp_mw f + fp_ew f) else 0
  match x with
  | S754_nan => fp_canonical_nan f
  | S754_zero s => sb s
  | S754_infinity s => sb s + Zshiftl (Zones (fp_ew f)) (fp_mw f)
  | S754_finite s m e =>
      if (digits2_pos m : Int) < f.fp_prec
      then sb s + (m : Int)                                  -- subnormal
      else sb s + Zshiftl (e - fp_emin f + 1) (fp_mw f)
           + ((m : Int) - Zshiftl 1 (fp_mw f))

/-- A signalling NaN is a NaN whose leading mantissa bit is CLEAR.  Read
off the bit pattern, because `fp_decode` collapses every NaN to
`S754_nan` and the distinction only matters for raising NV. -/
def fp_is_snan (f : format) (x : Int) : Bool :=
  (fp_exp_field f x == Zones (fp_ew f)) &&
    ((!(fp_man_field f x == 0)) && (!(Ztestbit x (fp_mw f - 1))))

def fp_is_nan (f : format) (x : Int) : Bool :=
  (fp_exp_field f x == Zones (fp_ew f)) && (!(fp_man_field f x == 0))

/-- Flip the sign bit — the negation fused-multiply-add's variants and
fsub are defined by, and NOT an arithmetic negation: it leaves NaN-ness
and signalling-ness alone, which is what makes `fp_sub`-as-`fp_add`-of-a-
negated-operand raise exactly the flags a native subtraction would. -/
def fp_neg (f : format) (x : Int) : Int :=
  Zlxor x (Zshiftl 1 (fp_mw f + fp_ew f))

/-! ## The rounding kernel, with flags

The body is `binary_round_aux`'s, with the intermediate location and
exponent kept instead of discarded: `l1` (the location after aligning
`mx` to the canonical exponent) IS inexactness, and `e2` against
`emax - prec` IS overflow.  The second `shr_fexp` is the carry-out
normalization for the case where rounding up overflowed the mantissa; it
is exact, so it cannot change `l1`.

`round_aux_value` states the coincidence with Flocq's kernel, so a reader
can check the value against Flocq's correctness theorem without
re-reading this body. -/

def mk_round_flags (of_ uf nx : Bool) : fflags :=
  fflags.Fflags false false of_ uf nx

/-- Tininess detected after rounding: round the SAME intermediate to
`prec` bits as though the exponent range were unbounded — the target
exponent is `digits − prec` below the operand's, with no `emin` floor —
and the value is tiny when that magnitude ends up strictly below the
smallest normal, `2 ^ (emin + prec − 1)`.  The magnitude comparison reads
off the rounded mantissa's digit count: `m · 2 ^ e < 2 ^ k` for a
canonical (or carried, `prec`+1-digit) mantissa exactly when
`digits(m) + e ≤ k`.

The operand contract is `round_aux`'s own: an inexact location only ever
arrives on a mantissa of at least `prec` digits (the div/sqrt cores
construct that many; exact operands carry `loc_Exact`), so the right
shift below never has to invent bits it cannot see. -/
def round_tiny (f : format) (md : rmode) (sx : Bool)
    (mx ex : Int) (lx : location) : Bool :=
  let (mrs, e') := shr (shr_record_of_loc mx lx) ex (Zdigits2 mx - f.fp_prec)
  let m' := choice_mode (flocq_mode md) sx (shr_m mrs) (loc_of_shr_record mrs)
  decide (Zdigits2 m' + e' ≤ fp_emin f + f.fp_prec - 1)

/-- Rocq's final match is on `Z0` / `Zpos mz` / `Zneg _`; `positive` is
`Nat` here, so the sign test is written out and the mantissa handed to
`S754_finite` is `Int.toNat` — the same three cases over the same datum,
and the same shape `SpecFloat.binary_round_aux` uses.

Rocq's `let p := fp_prec f` and `let em := fp_emax f` are written out at
each use, so that this body and `binary_round_aux`'s share every
scrutinee and `round_aux_value` below is a case split. -/
def round_aux (f : format) (md : rmode) (sx : Bool)
    (mx ex : Int) (lx : location) : spec_float × fflags :=
  let (mrs1, e1) := shr_fexp f.fp_prec f.fp_emax mx ex lx
  let (mrs2, e2) :=
    shr_fexp f.fp_prec f.fp_emax
      (choice_mode (flocq_mode md) sx (shr_m mrs1) (loc_of_shr_record mrs1))
      e1 location.loc_Exact
  let nx := match loc_of_shr_record mrs1 with
            | location.loc_Exact => false
            | _ => true
  if shr_m mrs2 = 0 then (S754_zero sx, mk_round_flags false nx nx)
  else if 0 < shr_m mrs2 then
    (if e2 ≤ f.fp_emax - f.fp_prec
     then (S754_finite sx (shr_m mrs2).toNat e2,
           mk_round_flags false (nx && round_tiny f md sx mx ex lx) nx)
     else (binary_overflow f.fp_prec f.fp_emax (flocq_mode md) sx,
           mk_round_flags true false true))
  else (S754_nan, no_flags)   -- unreachable: mantissas are non-negative

/-- `round_aux`'s kernel can only shift a mantissa RIGHT, so it assumes
the operand is already at or below the target's canonical exponent.
Products, quotients and square roots arrive that way by construction, but
an EXACT operand need not: a cancelling sum `1 − (1 − 2^-52)` or a
widening conversion (a single-precision datum read in double precision)
has far fewer significant bits than the format's precision at an exponent
well above the minimum.  Left-aligning first (`shl_align` to the
canonical exponent, which is a no-op when the operand is already
canonical) is what keeps the RESULT canonical — and the result's
canonicity is exactly what `fp_encode` reads to tell a subnormal from a
normal. -/
def round_exact (f : format) (md : rmode) (sx : Bool)
    (mx : Nat) (ex : Int) : spec_float × fflags :=
  let (mz, ez) :=
    shl_align mx ex (fexp f.fp_prec f.fp_emax ((digits2_pos mx : Int) + ex))
  round_aux f md sx (mz : Int) ez location.loc_Exact

/-- The value `round_aux` computes IS Flocq's `binary_round_aux`; only the
flags are ours.  Rocq discharges this by unfolding both and destructing the
two `shr_fexp` results and the final mantissa, which is what this script
does; the two bodies share every scrutinee, so once the pairs are named the
rest is a case split and a projection. -/
theorem round_aux_value (f : format) (md : rmode) (sx : Bool)
    (mx ex : Int) (lx : location) :
    (round_aux f md sx mx ex lx).fst
      = binary_round_aux f.fp_prec f.fp_emax (flocq_mode md) sx mx ex lx := by
  unfold round_aux binary_round_aux binary_fit_aux
  rcases h1 : shr_fexp f.fp_prec f.fp_emax mx ex lx with ⟨mrs1, e1⟩
  dsimp only
  rcases h2 : shr_fexp f.fp_prec f.fp_emax
      (choice_mode (flocq_mode md) sx (shr_m mrs1) (loc_of_shr_record mrs1))
      e1 location.loc_Exact with ⟨mrs2, e2⟩
  dsimp only
  by_cases hz : shr_m mrs2 = 0
  · simp [hz]
  · by_cases hp : 0 < shr_m mrs2
    · by_cases he : e2 ≤ f.fp_emax - f.fp_prec <;> simp [hz, hp, he]
    · simp [hz, hp]

/-! ## Exact operands as scaled integers

Addition and fused multiply-add both need the EXACT sum of two scaled
integers before any rounding happens.  Representing a finite datum as
(signed mantissa, exponent) and aligning to the smaller exponent makes
that a single integer addition; zero is `(0, 0)`, which is the additive
unit and so needs no case of its own.  The alignment shift is bounded by
the format's exponent range (about 2100 bits for binary64), so the
intermediate is a bignum but a small one. -/

def sf_scaled (x : spec_float) : Int × Int :=
  match x with
  | S754_finite s m e => ((if s then -(m : Int) else (m : Int)), e)
  | _ => (0, 0)

def scaled_add (a b : Int × Int) : Int × Int :=
  let (ma, ea) := a
  let (mb, eb) := b
  let e := Zmin ea eb
  (Zshiftl ma (ea - e) + Zshiftl mb (eb - e), e)

def sf_sign (x : spec_float) : Bool :=
  match x with
  | S754_zero s => s
  | S754_infinity s => s
  | S754_finite s _ _ => s
  | S754_nan => false

/-- The sign of an EXACTLY ZERO sum.  IEEE: when two operands of opposite
sign cancel exactly the result is +0, except under round-toward-negative
where it is −0; when the signs agree the result keeps that sign (so
−0 + −0 = −0, and x + x keeps x's sign even at zero). -/
def zero_sign (md : rmode) (sa sb : Bool) : Bool :=
  if sa == sb then sa
  else match md with | RDN => true | _ => false

/-- Round an exact scaled integer, using `szero` for the sign of a zero
result (the kernel's sign argument is the sign of a NONZERO value, so a
cancelling sum has to supply its own).

Rocq matches `m` against `Z0` / `Zpos p` / `Zneg p`; `positive` is `Nat`
here, so the three cases are a zero test and a sign test, and the
magnitude is `Int.natAbs` (which is `Int.toNat` on the positive side). -/
def round_scaled (f : format) (md : rmode) (szero : Bool)
    (v : Int × Int) : spec_float × fflags :=
  let (m, e) := v
  if m == 0 then (S754_zero szero, no_flags)
  else if 0 < m then round_exact f md false m.natAbs e
  else round_exact f md true m.natAbs e

/-! ## NaN pre-pass

Every arithmetic operation starts the same way: a signalling NaN operand
raises NV, any NaN operand makes the result the canonical NaN, and only
then do the infinity/zero special cases matter.  Factoring it out keeps
each operation's own dispatch to the cases that are actually about that
operation. -/

def nan_pass1 (f : format) (a : Int) : Option (Int × fflags) :=
  if fp_is_nan f a
  then some (fp_canonical_nan f, if fp_is_snan f a then nv_flag else no_flags)
  else none

def nan_pass2 (f : format) (a b : Int) : Option (Int × fflags) :=
  if fp_is_nan f a || fp_is_nan f b
  then some (fp_canonical_nan f,
             if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags)
  else none

def nan_pass3 (f : format) (a b c : Int) : Option (Int × fflags) :=
  if fp_is_nan f a || (fp_is_nan f b || fp_is_nan f c)
  then some (fp_canonical_nan f,
             if fp_is_snan f a || (fp_is_snan f b || fp_is_snan f c)
             then nv_flag else no_flags)
  else none

def enc (f : format) (r : spec_float × fflags) : Int × fflags :=
  (fp_encode f r.fst, r.snd)

/-! ## Addition, subtraction, multiplication, division, square root -/

def fp_add (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    let x := fp_decode f a
    let y := fp_decode f b
    match x, y with
    | S754_infinity sa, S754_infinity sb =>
        if sa == sb
        then (fp_encode f (S754_infinity sa), no_flags)
        else (fp_canonical_nan f, nv_flag)   -- inf − inf
    | S754_infinity sa, _ => (fp_encode f (S754_infinity sa), no_flags)
    | _, S754_infinity sb => (fp_encode f (S754_infinity sb), no_flags)
    | _, _ =>
        enc f (round_scaled f md (zero_sign md (sf_sign x) (sf_sign y))
                            (scaled_add (sf_scaled x) (sf_scaled y)))

/-- Subtraction is addition of the sign-flipped operand: `fp_neg` is a bit
flip, so it changes neither NaN-ness nor signalling-ness, and the
zero-sign rule then reads correctly off the flipped sign (x − x = +0
except under RDN; −0 − +0 = −0). -/
def fp_sub (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  fp_add f md a (fp_neg f b)

def fp_mul (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    match fp_decode f a, fp_decode f b with
    | S754_infinity _, S754_zero _
    | S754_zero _, S754_infinity _ =>
        (fp_canonical_nan f, nv_flag)        -- 0 × inf
    | S754_infinity sa, y =>
        (fp_encode f (S754_infinity (Bool.xor sa (sf_sign y))), no_flags)
    | x, S754_infinity sb =>
        (fp_encode f (S754_infinity (Bool.xor (sf_sign x) sb)), no_flags)
    | S754_zero sa, y =>
        (fp_encode f (S754_zero (Bool.xor sa (sf_sign y))), no_flags)
    | x, S754_zero sb =>
        (fp_encode f (S754_zero (Bool.xor (sf_sign x) sb)), no_flags)
    | S754_finite sa ma ea, S754_finite sb mb eb =>
        enc f (round_exact f md (Bool.xor sa sb) (ma * mb) (ea + eb))
    | _, _ => (fp_canonical_nan f, no_flags)  -- unreachable: NaNs handled above

def fp_div (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    match fp_decode f a, fp_decode f b with
    | S754_infinity _, S754_infinity _ => (fp_canonical_nan f, nv_flag)
    | S754_zero _, S754_zero _ => (fp_canonical_nan f, nv_flag)
    | S754_infinity sa, y =>
        (fp_encode f (S754_infinity (Bool.xor sa (sf_sign y))), no_flags)
    | x, S754_infinity sb =>
        (fp_encode f (S754_zero (Bool.xor (sf_sign x) sb)), no_flags)
    | S754_zero sa, y =>
        (fp_encode f (S754_zero (Bool.xor sa (sf_sign y))), no_flags)
    -- finite nonzero / zero: the only divide-by-zero there is
    | x, S754_zero sb =>
        (fp_encode f (S754_infinity (Bool.xor (sf_sign x) sb)), dz_flag)
    | S754_finite sa ma ea, S754_finite sb mb eb =>
        let (mz, ez, lz) :=
          SFdiv_core_binary f.fp_prec f.fp_emax (ma : Int) ea (mb : Int) eb
        enc f (round_aux f md (Bool.xor sa sb) mz ez lz)
    | _, _ => (fp_canonical_nan f, no_flags)  -- unreachable

/-- sqrt(−0) is −0, not an invalid operation: IEEE makes the negative ZERO
the one negative input with a result. -/
def fp_sqrt (f : format) (md : rmode) (a : Int) : Int × fflags :=
  match nan_pass1 f a with
  | some r => r
  | none =>
    match fp_decode f a with
    | S754_zero s => (fp_encode f (S754_zero s), no_flags)
    | S754_infinity false => (fp_encode f (S754_infinity false), no_flags)
    | S754_infinity true => (fp_canonical_nan f, nv_flag)
    | S754_finite true _ _ => (fp_canonical_nan f, nv_flag)
    | S754_finite false m e =>
        let (mz, ez, lz) := SFsqrt_core_binary f.fp_prec f.fp_emax (m : Int) e
        enc f (round_aux f md false mz ez lz)
    | S754_nan => (fp_canonical_nan f, no_flags)  -- unreachable

/-! ## Fused multiply-add

FUSED: the product is not rounded before the addend is applied, so the
exact product's mantissa and the addend are summed as scaled integers and
rounded ONCE.  That is the whole point of the instruction and the only
reason it cannot be composed from `fp_mul` and `fp_add`.

An invalid product (0 × inf) raises NV even when the addend is a quiet
NaN — the product is examined first, per IEEE's fusedMultiplyAdd. -/

def fp_fma (f : format) (md : rmode) (a b c : Int) : Int × fflags :=
  let x := fp_decode f a
  let y := fp_decode f b
  let prod_invalid :=
    match x, y with
    | S754_infinity _, S754_zero _
    | S754_zero _, S754_infinity _ => true
    | _, _ => false
  if prod_invalid && (!(fp_is_nan f a || fp_is_nan f b))
  then (fp_canonical_nan f, nv_flag)
  else
  match nan_pass3 f a b c with
  | some r => r
  | none =>
    let z := fp_decode f c
    let sp := Bool.xor (sf_sign x) (sf_sign y)
    match x, y with
    -- An infinite product: the addend can only make it invalid.
    | S754_infinity _, _
    | _, S754_infinity _ =>
        match z with
        | S754_infinity sz =>
            if sp == sz
            then (fp_encode f (S754_infinity sp), no_flags)
            else (fp_canonical_nan f, nv_flag)
        | _ => (fp_encode f (S754_infinity sp), no_flags)
    | S754_finite _ ma ea, S754_finite _ mb eb =>
        -- A finite product plus an INFINITE addend is that infinity;
        -- `sf_scaled` maps every non-finite datum to 0, so without this
        -- case the addend would silently vanish.
        match z with
        | S754_infinity sz => (fp_encode f (S754_infinity sz), no_flags)
        | _ =>
          let prod : Int × Int :=
            ((if sp then -((ma * mb : Nat) : Int) else ((ma * mb : Nat) : Int)),
             ea + eb)
          enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                              (scaled_add prod (sf_scaled z)))
    -- A zero product: the sum is the addend, but the ZERO SIGN still
    -- follows the product's sign when the addend is zero too.
    | _, _ =>
        match z with
        | S754_infinity sz => (fp_encode f (S754_infinity sz), no_flags)
        | _ => enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                                   (sf_scaled z))

/-! ## Comparisons, min/max, classification -/

/-- `none` is "unordered", i.e. a NaN operand.  Rocq's `comparison` is
Lean's `Ordering`. -/
def fp_compare (f : format) (a b : Int) : Option Ordering :=
  SFcompare (fp_decode f a) (fp_decode f b)

/-- feq is QUIET: only a signalling NaN raises NV.  flt/fle are
SIGNALLING: any NaN raises it.  All three answer false when unordered. -/
def fp_eq (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with | some .eq => true | _ => false),
   if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags)

def fp_lt (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with | some .lt => true | _ => false),
   if fp_is_nan f a || fp_is_nan f b then nv_flag else no_flags)

def fp_le (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with
    | some .lt => true | some .eq => true | _ => false),
   if fp_is_nan f a || fp_is_nan f b then nv_flag else no_flags)

/-- fmin/fmax.  Three RISC-V rules a naive `fp_compare` would miss: one
NaN operand yields the OTHER operand (both NaN yields the canonical NaN),
NV is raised only for a SIGNALLING NaN, and −0 is strictly less than +0
even though `SFcompare` calls them equal — so the equal case is decided
on the sign bits. -/
def fp_minmax (f : format) (is_max : Bool) (a b : Int) : Int × fflags :=
  let fl := if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags
  if fp_is_nan f a && fp_is_nan f b then (fp_canonical_nan f, fl)
  else if fp_is_nan f a then (b, fl)
  else if fp_is_nan f b then (a, fl)
  else
    let a_lt_b :=
      match fp_compare f a b with
      | some .lt => true
      | some .eq => fp_sign_bit f a && (!(fp_sign_bit f b))
      | _ => false
    ((if Bool.xor is_max a_lt_b then a else b), fl)

/-- The fclass bit mask: bit 0 −inf, 1 −normal, 2 −subnormal, 3 −0, 4 +0,
5 +subnormal, 6 +normal, 7 +inf, 8 sNaN, 9 qNaN. -/
def fp_class (f : format) (a : Int) : Int :=
  let s := fp_sign_bit f a
  let e := fp_exp_field f a
  let m := fp_man_field f a
  if e == Zones (fp_ew f) then
    (if m == 0 then (if s then 1 else Zshiftl 1 7)
     else if fp_is_snan f a then Zshiftl 1 8 else Zshiftl 1 9)
  else if e == 0 then
    (if m == 0 then (if s then Zshiftl 1 3 else Zshiftl 1 4)
     else if s then Zshiftl 1 2 else Zshiftl 1 5)
  else (if s then Zshiftl 1 1 else Zshiftl 1 6)

/-! ## Conversions

float → integer.  `bits` is the integer width (32 or 64) and `signed` its
signedness; the answer is the RAW two's-complement value in that width,
which `Sem` sign-extends into the 64-bit destination register (RISC-V
sign-extends fcvt.wu's unsigned result too).

Saturation, not wraparound: an out-of-range magnitude, an infinity or a
NaN gives the nearest representable integer and raises NV.  A NaN gives
the MAXIMUM in both signednesses.  NV suppresses NX, so a saturated
conversion reports exactly one exception. -/

def int_lo (signed : Bool) (bits : Int) : Int :=
  if signed then -(Zshiftl 1 (bits - 1)) else 0
def int_hi (signed : Bool) (bits : Int) : Int :=
  if signed then Zshiftl 1 (bits - 1) - 1 else Zshiftl 1 bits - 1

/-- Two's-complement image of `v` in `bits` bits. -/
def int_wrap (bits v : Int) : Int := Zland v (Zones bits)

def fp_to_int (f : format) (md : rmode) (signed : Bool) (bits : Int)
    (a : Int) : Int × fflags :=
  let sat (v : Int) : Int × fflags := (int_wrap bits v, nv_flag)
  if fp_is_nan f a then sat (int_hi signed bits)
  else
    match fp_decode f a with
    | S754_infinity s =>
        sat (if s then int_lo signed bits else int_hi signed bits)
    | S754_zero _ => (0, no_flags)
    | S754_nan => sat (int_hi signed bits)   -- unreachable
    | S754_finite s m e =>
        -- Split the scaled mantissa at the binary point: `q` is the
        -- truncated magnitude, `l` says where the discarded part sits
        -- between `q` and `q+1`, and `choice_mode` applies the rounding
        -- rule to the MAGNITUDE with the sign supplied separately — the
        -- same convention the FP kernel uses.
        let ql : Int × location :=
          if 0 ≤ e then (Zshiftl (m : Int) e, location.loc_Exact)
          else
            let d := Zshiftl 1 (-e)
            let (q, r) := Zdiv_eucl (m : Int) d
            (q, new_location d r)
        let q := ql.fst
        let l := ql.snd
        let q' := choice_mode (flocq_mode md) s q l
        let v := if s then -q' else q'
        if decide (v < int_lo signed bits) || decide (int_hi signed bits < v)
        then sat (if s then int_lo signed bits else int_hi signed bits)
        else (int_wrap bits v,
              match l with | location.loc_Exact => no_flags | _ => nx_flag)

/-- integer → float.  `v` is the raw `bits`-wide value from the source
register, read with the requested signedness before rounding. -/
def fp_of_int (f : format) (md : rmode) (signed : Bool) (bits : Int)
    (v : Int) : Int × fflags :=
  let u := int_wrap bits v
  let n := if signed && Ztestbit u (bits - 1)
           then u - Zshiftl 1 bits else u
  enc f (round_scaled f md false (n, 0))

/-- float → float.  Widening is exact; narrowing rounds and can overflow
or underflow, so both directions go through the same kernel and the flags
fall out.  A NaN converts to the DESTINATION's canonical NaN, and a
signalling one raises NV. -/
def fp_convert (src dst : format) (md : rmode) (a : Int) : Int × fflags :=
  if fp_is_nan src a
  then (fp_canonical_nan dst, if fp_is_snan src a then nv_flag else no_flags)
  else
    match fp_decode src a with
    | S754_zero s => (fp_encode dst (S754_zero s), no_flags)
    | S754_infinity s => (fp_encode dst (S754_infinity s), no_flags)
    | S754_nan => (fp_canonical_nan dst, no_flags)   -- unreachable
    | S754_finite s m e => enc dst (round_exact dst md s m e)

end LinuxProcessSemantics.Riscv.Fpu
