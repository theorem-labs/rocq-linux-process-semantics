(** * Fpu: IEEE-754 binary arithmetic with RISC-V exception flags

    TRUST BOUNDARY: this file is part of the trusted specification.

    [Sem] needs FP operations that return BOTH a result and the five
    IEEE exception flags, because in RISC-V the flags are
    architectural: they accrue into fcsr[4:0], a program can read them
    with [csrr fflags], and a compiler is free to branch on them.  A
    semantics that produced only the value would be unsound the moment
    a binary looked at fflags.

    The value half is not reinvented here.  Rounding is
    [binary_round_aux], the rounding kernel of the Flocq library's
    binary-float development: it takes a sign, an unrounded mantissa,
    an exponent and a LOCATION (where the exact value sits relative to
    the two candidate mantissas), and returns the correctly rounded
    [spec_float] — the payload-free IEEE datum of the standard
    library's [SpecFloat].  Flocq proves that kernel equal to
    real-number rounding, and [round_aux_value] below pins our
    flag-carrying restatement to it definitionally, so the value this
    file computes is exactly the value Flocq's theorem is about.

    The flag half is ours, and it is derived from the same
    intermediate the kernel rounds from:

    - NX (inexact): the location after aligning the operand to the
      target's canonical exponent is not [loc_Exact].  That is
      literally "some bits were discarded", i.e. the rounded result
      differs from the exact one.
    - OF (overflow): the rounded exponent exceeds [emax - prec], the
      same test the kernel uses to choose between a finite result and
      [binary_overflow].  Overflow always implies NX.  Which of ±inf
      and ±MAXFLOAT comes out is [binary_overflow]'s business and is
      rounding-mode dependent (RTZ never produces an infinity; RDN/RUP
      produce one only on the side they round away to).
    - UF (underflow): TINY AND INEXACT, with tininess detected AFTER
      rounding — the IEEE option RISC-V mandates.  "After rounding"
      means rounding to [prec] bits AS THOUGH THE EXPONENT RANGE WERE
      UNBOUNDED and asking whether that magnitude stays strictly below
      the smallest normal.  That is NOT the same as "the delivered
      result is subnormal": just below the smallest normal the
      unbounded grid is twice as fine as the subnormal grid, so a
      value in the lower part of that last gap can carry up to the
      smallest normal under the real (bounded) rounding while the
      unbounded-range rounding stays tiny — UF is raised even though
      the delivered result is normal.  [round_tiny] implements the
      unbounded-range rounding.
    - NV (invalid) and DZ (divide by zero) never come from rounding;
      they are raised by the special-case dispatch of each operation
      (0×inf, inf−inf, sqrt of a negative, a signalling NaN operand,
      a finite nonzero divided by zero, an out-of-range float→int).

    RISC-V specifics that this file, not the IEEE kernel, decides:

    - Every NaN RESULT is the canonical quiet NaN (sign 0, exponent
      all ones, mantissa = the quiet bit alone).  RISC-V does not
      propagate payloads, which is why [spec_float]'s payload-free
      [S754_nan] is the right datum and why NaN-ness alone is not
      enough state to carry: signalling-ness has to be read off the
      BIT PATTERN before decoding ([is_snan]), since decoding forgets
      it.
    - fmin/fmax return the non-NaN operand when exactly one operand
      is NaN, and raise NV only for a SIGNALLING NaN; −0 is ordered
      below +0, which a bitwise comparison would get wrong.
    - feq is a QUIET compare (NV only on a signalling NaN); flt/fle
      are SIGNALLING (NV on any NaN).
    - float→int saturates: out-of-range, infinite and NaN inputs
      produce the nearest representable integer and raise NV, and NV
      SUPPRESSES NX — a saturated conversion reports one problem, not
      two.

    Everything here is a computation over [Z] on RAW BIT PATTERNS of
    the format's width (32 or 64).  Register width, NaN boxing and
    the fcsr update belong to [Sem]; this file never sees a
    bitvector. *)

From Stdlib Require Import ZArith SpecFloat.
From Flocq.IEEE754 Require BinarySingleNaN.

Local Open Scope Z_scope.

(** ** Formats

    A binary format is pinned by [prec] (significand bits, including
    the implicit leading one) and [emax] (the exponent of the
    infinities); every other constant is derived, so there is one
    place to look and no way for the two formats to disagree about
    their own layout.  [fp_emin] is the exponent of the SMALLEST
    SUBNORMAL, which is the exponent [SpecFloat] gives every
    subnormal datum — not the smallest normal exponent. *)

Record format := Fmt { fp_prec : Z; fp_emax : Z }.

Definition fmt_single : format := Fmt 24 128.
Definition fmt_double : format := Fmt 53 1024.

Definition fp_mw (f : format) : Z := fp_prec f - 1.        (** mantissa field *)
Definition fp_ew (f : format) : Z := Z.log2 (fp_emax f) + 1. (** exponent field *)
Definition fp_emin (f : format) : Z := 3 - fp_emax f - fp_prec f.

(** ** Exception flags

    The five IEEE flags, in the fcsr[4:0] bit order RISC-V assigns
    them.  Kept as a record rather than a bitmask so that every
    operation below has to name the flags it raises; [fflags_bits] is
    the single place the encoding is spelled. *)

Record fflags := Fflags {
  fl_nv : bool;  (** invalid operation *)
  fl_dz : bool;  (** divide by zero *)
  fl_of : bool;  (** overflow *)
  fl_uf : bool;  (** underflow *)
  fl_nx : bool   (** inexact *)
}.

Definition no_flags : fflags := Fflags false false false false false.
Definition nv_flag : fflags := Fflags true false false false false.
Definition dz_flag : fflags := Fflags false true false false false.
Definition nx_flag : fflags := Fflags false false false false true.

Definition fflags_bits (fl : fflags) : Z :=
  let b (p : bool) (i : Z) := if p then Z.shiftl 1 i else 0 in
  b (fl_nx fl) 0 + b (fl_uf fl) 1 + b (fl_of fl) 2
  + b (fl_dz fl) 3 + b (fl_nv fl) 4.

(** ** Rounding modes

    The five architectural modes.  The instruction's 3-bit rm field
    also has the DYNAMIC encoding 7 (use fcsr's frm) and two RESERVED
    encodings, 5 and 6; [rmode_of_field] returns [None] for those, and
    for a dynamic rm whose frm is itself reserved.  [None] is an
    ILLEGAL INSTRUCTION at the [Sem] level, not a defaulted mode:
    executing a reserved rounding mode as if it were round-to-nearest
    would give a wrong answer silently, where trapping is what real
    hardware does. *)

Inductive rmode : Type := RNE | RTZ | RDN | RUP | RMM.

Definition rmode_of_Z (z : Z) : option rmode :=
  if Z.eqb z 0 then Some RNE
  else if Z.eqb z 1 then Some RTZ
  else if Z.eqb z 2 then Some RDN
  else if Z.eqb z 3 then Some RUP
  else if Z.eqb z 4 then Some RMM
  else None.

(** [rm] is the instruction field, [frm] the fcsr rounding mode. *)
Definition rmode_of_field (rm frm : Z) : option rmode :=
  if Z.eqb rm 7 then rmode_of_Z frm else rmode_of_Z rm.

Definition flocq_mode (m : rmode) : BinarySingleNaN.mode :=
  match m with
  | RNE => BinarySingleNaN.mode_NE
  | RTZ => BinarySingleNaN.mode_ZR
  | RDN => BinarySingleNaN.mode_DN
  | RUP => BinarySingleNaN.mode_UP
  | RMM => BinarySingleNaN.mode_NA
  end.

(** ** Bit patterns

    Decode and encode the interchange format by hand: the standard
    library's [spec_float] is an abstract datum with no layout, and
    the layout is exactly what an ISA semantics has to be explicit
    about.  [Pos.size] is the number of significant bits of a
    positive, which is how a subnormal RESULT is recognized on the way
    out (fewer than [prec] significant bits, which for a canonical
    datum can only happen at the minimum exponent). *)

Definition fp_sign_bit (f : format) (x : Z) : bool :=
  Z.testbit x (fp_mw f + fp_ew f).
Definition fp_exp_field (f : format) (x : Z) : Z :=
  Z.land (Z.shiftr x (fp_mw f)) (Z.ones (fp_ew f)).
Definition fp_man_field (f : format) (x : Z) : Z :=
  Z.land x (Z.ones (fp_mw f)).

Definition fp_decode (f : format) (x : Z) : spec_float :=
  let s := fp_sign_bit f x in
  let e := fp_exp_field f x in
  let m := fp_man_field f x in
  if Z.eqb e 0 then
    match m with
    | Zpos p => S754_finite s p (fp_emin f)
    | _ => S754_zero s
    end
  else if Z.eqb e (Z.ones (fp_ew f)) then
    (if Z.eqb m 0 then S754_infinity s else S754_nan)
  else
    match Z.shiftl 1 (fp_mw f) + m with
    | Zpos p => S754_finite s p (e + fp_emin f - 1)
    | _ => S754_nan   (* unreachable: the implicit bit makes this positive *)
    end.

(** The one NaN this semantics ever produces. *)
Definition fp_canonical_nan (f : format) : Z :=
  Z.shiftl (Z.ones (fp_ew f)) (fp_mw f) + Z.shiftl 1 (fp_mw f - 1).

Definition fp_encode (f : format) (x : spec_float) : Z :=
  let sb (s : bool) := if s then Z.shiftl 1 (fp_mw f + fp_ew f) else 0 in
  match x with
  | S754_nan => fp_canonical_nan f
  | S754_zero s => sb s
  | S754_infinity s => sb s + Z.shiftl (Z.ones (fp_ew f)) (fp_mw f)
  | S754_finite s m e =>
      if Z.ltb (Z.pos (Pos.size m)) (fp_prec f)
      then sb s + Z.pos m                                   (* subnormal *)
      else sb s + Z.shiftl (e - fp_emin f + 1) (fp_mw f)
           + (Z.pos m - Z.shiftl 1 (fp_mw f))
  end.

(** A signalling NaN is a NaN whose leading mantissa bit is CLEAR.
    Read off the bit pattern, because [fp_decode] collapses every NaN
    to [S754_nan] and the distinction only matters for raising NV. *)
Definition fp_is_snan (f : format) (x : Z) : bool :=
  andb (Z.eqb (fp_exp_field f x) (Z.ones (fp_ew f)))
       (andb (negb (Z.eqb (fp_man_field f x) 0))
             (negb (Z.testbit x (fp_mw f - 1)))).

Definition fp_is_nan (f : format) (x : Z) : bool :=
  andb (Z.eqb (fp_exp_field f x) (Z.ones (fp_ew f)))
       (negb (Z.eqb (fp_man_field f x) 0)).

(** Flip the sign bit — the negation fused-multiply-add's variants and
    fsub are defined by, and NOT an arithmetic negation: it leaves
    NaN-ness and signalling-ness alone, which is what makes
    [fp_sub]-as-[fp_add]-of-a-negated-operand raise exactly the flags
    a native subtraction would. *)
Definition fp_neg (f : format) (x : Z) : Z :=
  Z.lxor x (Z.shiftl 1 (fp_mw f + fp_ew f)).

(** ** The rounding kernel, with flags

    The body is [BinarySingleNaN.binary_round_aux]'s, with the
    intermediate location and exponent kept instead of discarded:
    [l1] (the location after aligning [mx] to the canonical exponent)
    IS inexactness, and [e2] against [emax - prec] IS overflow.  The
    second [shr_fexp] is the carry-out normalization for the case
    where rounding up overflowed the mantissa; it is exact, so it
    cannot change [l1].

    [round_aux_value] states the coincidence with Flocq's kernel, so
    a reader can check the value against Flocq's correctness theorem
    without re-reading this body. *)

Definition mk_round_flags (of_ uf nx : bool) : fflags :=
  Fflags false false of_ uf nx.

(** Tininess detected after rounding: round the SAME intermediate to
    [prec] bits as though the exponent range were unbounded — the
    target exponent is [digits − prec] below the operand's, with no
    [emin] floor — and the value is tiny when that magnitude ends up
    strictly below the smallest normal, 2^(emin + prec − 1).  The
    magnitude comparison reads off the rounded mantissa's digit count:
    m·2^e < 2^k for a canonical (or carried, [prec]+1-digit) mantissa
    exactly when digits(m) + e ≤ k.

    The operand contract is [round_aux]'s own: an inexact location
    only ever arrives on a mantissa of at least [prec] digits (the
    div/sqrt cores construct that many; exact operands carry
    [loc_Exact]), so the right shift below never has to invent bits it
    cannot see. *)
Definition round_tiny (f : format) (md : rmode) (sx : bool)
    (mx ex : Z) (lx : location) : bool :=
  let '(mrs, e') := shr (shr_record_of_loc mx lx) ex (Zdigits2 mx - fp_prec f) in
  let m' := BinarySingleNaN.choice_mode (flocq_mode md) sx (shr_m mrs)
              (loc_of_shr_record mrs) in
  Z.leb (Zdigits2 m' + e') (fp_emin f + fp_prec f - 1).

Definition round_aux (f : format) (md : rmode) (sx : bool)
    (mx ex : Z) (lx : location) : spec_float * fflags :=
  let p := fp_prec f in
  let em := fp_emax f in
  let '(mrs1, e1) := shr_fexp p em mx ex lx in
  let l1 := loc_of_shr_record mrs1 in
  let nx := match l1 with loc_Exact => false | _ => true end in
  let '(mrs2, e2) :=
    shr_fexp p em (BinarySingleNaN.choice_mode (flocq_mode md) sx (shr_m mrs1) l1)
             e1 loc_Exact in
  match shr_m mrs2 with
  | Z0 => (S754_zero sx, mk_round_flags false nx nx)
  | Zpos mz =>
      if Z.leb e2 (em - p)
      then (S754_finite sx mz e2,
            mk_round_flags false (andb nx (round_tiny f md sx mx ex lx)) nx)
      else (BinarySingleNaN.binary_overflow p em (flocq_mode md) sx,
            mk_round_flags true false true)
  | Zneg _ => (S754_nan, no_flags)   (* unreachable: mantissas are non-negative *)
  end.

(** [round_aux]'s kernel can only shift a mantissa RIGHT, so it
    assumes the operand is already at or below the target's canonical
    exponent.  Products, quotients and square roots arrive that way by
    construction, but an EXACT operand need not: a cancelling sum
    (1 − (1 − 2^-52)) or a widening conversion (a single-precision
    datum read in double precision) has far fewer significant bits
    than the format's precision at an exponent well above the minimum.
    Left-aligning first ([shl_align] to the canonical exponent, which
    is a no-op when the operand is already canonical) is what keeps
    the RESULT canonical — and the result's canonicity is exactly what
    [fp_encode] reads to tell a subnormal from a normal. *)
Definition round_exact (f : format) (md : rmode) (sx : bool)
    (mx : positive) (ex : Z) : spec_float * fflags :=
  let '(mz, ez) :=
    shl_align mx ex (fexp (fp_prec f) (fp_emax f)
                          (Z.pos (digits2_pos mx) + ex)) in
  round_aux f md sx (Z.pos mz) ez loc_Exact.

Lemma round_aux_value : forall f md sx mx ex lx,
  fst (round_aux f md sx mx ex lx)
  = BinarySingleNaN.binary_round_aux (fp_prec f) (fp_emax f) (flocq_mode md)
      sx mx ex lx.
Proof.
  intros f md sx mx ex lx.
  unfold round_aux, BinarySingleNaN.binary_round_aux,
         BinarySingleNaN.binary_fit_aux.
  destruct (shr_fexp (fp_prec f) (fp_emax f) mx ex lx) as [mrs1 e1].
  destruct (shr_fexp (fp_prec f) (fp_emax f) _ e1 loc_Exact) as [mrs2 e2].
  destruct (shr_m mrs2); simpl; [reflexivity| |reflexivity].
  destruct (Z.leb e2 (fp_emax f - fp_prec f)); reflexivity.
Qed.

(** ** Exact operands as scaled integers

    Addition and fused multiply-add both need the EXACT sum of two
    scaled integers before any rounding happens.  Representing a
    finite datum as (signed mantissa, exponent) and aligning to the
    smaller exponent makes that a single integer addition; zero is
    (0, 0), which is the additive unit and so needs no case of its
    own.  The alignment shift is bounded by the format's exponent
    range (about 2100 bits for binary64), so the intermediate is a
    bignum but a small one. *)

Definition sf_scaled (x : spec_float) : Z * Z :=
  match x with
  | S754_finite s m e => ((if s then Z.opp (Z.pos m) else Z.pos m), e)
  | _ => (0, 0)
  end.

Definition scaled_add (a b : Z * Z) : Z * Z :=
  let '(ma, ea) := a in
  let '(mb, eb) := b in
  let e := Z.min ea eb in
  (Z.shiftl ma (ea - e) + Z.shiftl mb (eb - e), e).

Definition sf_sign (x : spec_float) : bool :=
  match x with
  | S754_zero s | S754_infinity s | S754_finite s _ _ => s
  | S754_nan => false
  end.

(** The sign of an EXACTLY ZERO sum.  IEEE: when two operands of
    opposite sign cancel exactly the result is +0, except under
    round-toward-negative where it is −0; when the signs agree the
    result keeps that sign (so −0 + −0 = −0, and x + x keeps x's sign
    even at zero). *)
Definition zero_sign (md : rmode) (sa sb : bool) : bool :=
  if Bool.eqb sa sb then sa
  else match md with RDN => true | _ => false end.

(** Round an exact scaled integer, using [szero] for the sign of a
    zero result (the kernel's sign argument is the sign of a NONZERO
    value, so a cancelling sum has to supply its own). *)
Definition round_scaled (f : format) (md : rmode) (szero : bool)
    (v : Z * Z) : spec_float * fflags :=
  let '(m, e) := v in
  match m with
  | Z0 => (S754_zero szero, no_flags)
  | Zpos p => round_exact f md false p e
  | Zneg p => round_exact f md true p e
  end.

(** ** NaN pre-pass

    Every arithmetic operation starts the same way: a signalling NaN
    operand raises NV, any NaN operand makes the result the canonical
    NaN, and only then do the infinity/zero special cases matter.
    Factoring it out keeps each operation's own dispatch to the cases
    that are actually about that operation. *)

Definition nan_pass1 (f : format) (a : Z) : option (Z * fflags) :=
  if fp_is_nan f a
  then Some (fp_canonical_nan f,
             if fp_is_snan f a then nv_flag else no_flags)
  else None.

Definition nan_pass2 (f : format) (a b : Z) : option (Z * fflags) :=
  if orb (fp_is_nan f a) (fp_is_nan f b)
  then Some (fp_canonical_nan f,
             if orb (fp_is_snan f a) (fp_is_snan f b) then nv_flag else no_flags)
  else None.

Definition nan_pass3 (f : format) (a b c : Z) : option (Z * fflags) :=
  if orb (fp_is_nan f a) (orb (fp_is_nan f b) (fp_is_nan f c))
  then Some (fp_canonical_nan f,
             if orb (fp_is_snan f a) (orb (fp_is_snan f b) (fp_is_snan f c))
             then nv_flag else no_flags)
  else None.

Definition enc (f : format) (r : spec_float * fflags) : Z * fflags :=
  (fp_encode f (fst r), snd r).

(** ** Addition, subtraction, multiplication, division, square root *)

Definition fp_add (f : format) (md : rmode) (a b : Z) : Z * fflags :=
  match nan_pass2 f a b with
  | Some r => r
  | None =>
    let x := fp_decode f a in
    let y := fp_decode f b in
    match x, y with
    | S754_infinity sa, S754_infinity sb =>
        if Bool.eqb sa sb
        then (fp_encode f (S754_infinity sa), no_flags)
        else (fp_canonical_nan f, nv_flag)   (* inf − inf *)
    | S754_infinity sa, _ => (fp_encode f (S754_infinity sa), no_flags)
    | _, S754_infinity sb => (fp_encode f (S754_infinity sb), no_flags)
    | _, _ =>
        enc f (round_scaled f md (zero_sign md (sf_sign x) (sf_sign y))
                            (scaled_add (sf_scaled x) (sf_scaled y)))
    end
  end.

(** Subtraction is addition of the sign-flipped operand: [fp_neg] is a
    bit flip, so it changes neither NaN-ness nor signalling-ness, and
    the zero-sign rule then reads correctly off the flipped sign
    (x − x = +0 except under RDN; −0 − +0 = −0). *)
Definition fp_sub (f : format) (md : rmode) (a b : Z) : Z * fflags :=
  fp_add f md a (fp_neg f b).

Definition fp_mul (f : format) (md : rmode) (a b : Z) : Z * fflags :=
  match nan_pass2 f a b with
  | Some r => r
  | None =>
    match fp_decode f a, fp_decode f b with
    | S754_infinity sa, S754_zero _ | S754_zero _, S754_infinity sa =>
        (fp_canonical_nan f, nv_flag)        (* 0 × inf *)
    | S754_infinity sa, y => (fp_encode f (S754_infinity (xorb sa (sf_sign y))), no_flags)
    | x, S754_infinity sb => (fp_encode f (S754_infinity (xorb (sf_sign x) sb)), no_flags)
    | S754_zero sa, y => (fp_encode f (S754_zero (xorb sa (sf_sign y))), no_flags)
    | x, S754_zero sb => (fp_encode f (S754_zero (xorb (sf_sign x) sb)), no_flags)
    | S754_finite sa ma ea, S754_finite sb mb eb =>
        enc f (round_exact f md (xorb sa sb) (Pos.mul ma mb) (ea + eb))
    | _, _ => (fp_canonical_nan f, no_flags)  (* unreachable: NaNs handled above *)
    end
  end.

(** An exponent range for the division core wide enough that no
    quotient of two finite operands reaches its floor.  The smallest
    exponent [SFdiv_core_binary] asks for is
    [4 - 2 * emax - 2 * prec] (a one-bit subnormal over the largest
    finite value), and with this [emax] the core's own minimum exponent
    is [3 - 2 * emax - 2 * prec], one below it. *)
Definition div_core_emax (f : format) : Z := 2 * fp_emax f + fp_prec f.

Definition fp_div (f : format) (md : rmode) (a b : Z) : Z * fflags :=
  match nan_pass2 f a b with
  | Some r => r
  | None =>
    match fp_decode f a, fp_decode f b with
    | S754_infinity _, S754_infinity _ => (fp_canonical_nan f, nv_flag)
    | S754_zero _, S754_zero _ => (fp_canonical_nan f, nv_flag)
    | S754_infinity sa, y => (fp_encode f (S754_infinity (xorb sa (sf_sign y))), no_flags)
    | x, S754_infinity sb => (fp_encode f (S754_zero (xorb (sf_sign x) sb)), no_flags)
    | S754_zero sa, y => (fp_encode f (S754_zero (xorb sa (sf_sign y))), no_flags)
    (* finite nonzero / zero: the only divide-by-zero there is *)
    | x, S754_zero sb => (fp_encode f (S754_infinity (xorb (sf_sign x) sb)), dz_flag)
    | S754_finite sa ma ea, S754_finite sb mb eb =>
        (* The core runs over [div_core_emax], so the quotient keeps
           [prec] significant bits even when it is subnormal.  The value
           does not change: [round_aux] still rounds onto the format's
           own grid.  The flags do: with [fp_emax f] the core truncates
           a subnormal quotient to the subnormal grid already, and
           [round_tiny] then rounds that, not the exact quotient.  A
           quotient in the last gap below the smallest normal that
           rounds up to it under the format's range, but stays below it
           with the range unbounded, would lose its UF flag
           ([div_tiny_carries_to_normal_uf] in FpuTests). *)
        let '(mz, ez, lz) :=
          SFdiv_core_binary (fp_prec f) (div_core_emax f) (Z.pos ma) ea (Z.pos mb) eb in
        enc f (round_aux f md (xorb sa sb) mz ez lz)
    | _, _ => (fp_canonical_nan f, no_flags)  (* unreachable *)
    end
  end.

(** sqrt(−0) is −0, not an invalid operation: IEEE makes the negative
    ZERO the one negative input with a result. *)
Definition fp_sqrt (f : format) (md : rmode) (a : Z) : Z * fflags :=
  match nan_pass1 f a with
  | Some r => r
  | None =>
    match fp_decode f a with
    | S754_zero s => (fp_encode f (S754_zero s), no_flags)
    | S754_infinity false => (fp_encode f (S754_infinity false), no_flags)
    | S754_infinity true => (fp_canonical_nan f, nv_flag)
    | S754_finite true _ _ => (fp_canonical_nan f, nv_flag)
    | S754_finite false m e =>
        let '(mz, ez, lz) := SFsqrt_core_binary (fp_prec f) (fp_emax f) (Z.pos m) e in
        enc f (round_aux f md false mz ez lz)
    | S754_nan => (fp_canonical_nan f, no_flags)  (* unreachable *)
    end
  end.

(** ** Fused multiply-add

    FUSED: the product is not rounded before the addend is applied, so
    the exact product's mantissa and the addend are summed as scaled
    integers and rounded ONCE.  That is the whole point of the
    instruction and the only reason it cannot be composed from
    [fp_mul] and [fp_add].

    An invalid product (0 × inf) raises NV even when the addend is a
    quiet NaN — the product is examined first, per IEEE's
    fusedMultiplyAdd. *)

Definition fp_fma (f : format) (md : rmode) (a b c : Z) : Z * fflags :=
  let x := fp_decode f a in
  let y := fp_decode f b in
  let prod_invalid :=
    match x, y with
    | S754_infinity _, S754_zero _ | S754_zero _, S754_infinity _ => true
    | _, _ => false
    end in
  if andb prod_invalid (negb (orb (fp_is_nan f a) (fp_is_nan f b)))
  then (fp_canonical_nan f, nv_flag)
  else
  match nan_pass3 f a b c with
  | Some r => r
  | None =>
    let z := fp_decode f c in
    let sp := xorb (sf_sign x) (sf_sign y) in
    match x, y with
    (* An infinite product: the addend can only make it invalid. *)
    | S754_infinity _, _ | _, S754_infinity _ =>
        match z with
        | S754_infinity sz =>
            if Bool.eqb sp sz
            then (fp_encode f (S754_infinity sp), no_flags)
            else (fp_canonical_nan f, nv_flag)
        | _ => (fp_encode f (S754_infinity sp), no_flags)
        end
    | S754_finite sa ma ea, S754_finite sb mb eb =>
        (* A finite product plus an INFINITE addend is that infinity;
           [sf_scaled] maps every non-finite datum to 0, so without
           this case the addend would silently vanish. *)
        match z with
        | S754_infinity sz => (fp_encode f (S754_infinity sz), no_flags)
        | _ =>
          let prod := ((if sp then Z.opp (Z.pos (Pos.mul ma mb))
                              else Z.pos (Pos.mul ma mb)), ea + eb) in
          enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                              (scaled_add prod (sf_scaled z)))
        end
    (* A zero product: the sum is the addend, but the ZERO SIGN still
       follows the product's sign when the addend is zero too. *)
    | _, _ =>
        match z with
        | S754_infinity sz => (fp_encode f (S754_infinity sz), no_flags)
        | _ => enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                                   (sf_scaled z))
        end
    end
  end.

(** ** Comparisons, min/max, classification *)

(** [None] is "unordered", i.e. a NaN operand. *)
Definition fp_compare (f : format) (a b : Z) : option comparison :=
  SFcompare (fp_decode f a) (fp_decode f b).

(** feq is QUIET: only a signalling NaN raises NV.  flt/fle are
    SIGNALLING: any NaN raises it.  All three answer false when
    unordered. *)
Definition fp_eq (f : format) (a b : Z) : bool * fflags :=
  ((match fp_compare f a b with Some Eq => true | _ => false end),
   if orb (fp_is_snan f a) (fp_is_snan f b) then nv_flag else no_flags).

Definition fp_lt (f : format) (a b : Z) : bool * fflags :=
  ((match fp_compare f a b with Some Lt => true | _ => false end),
   if orb (fp_is_nan f a) (fp_is_nan f b) then nv_flag else no_flags).

Definition fp_le (f : format) (a b : Z) : bool * fflags :=
  ((match fp_compare f a b with Some Lt | Some Eq => true | _ => false end),
   if orb (fp_is_nan f a) (fp_is_nan f b) then nv_flag else no_flags).

(** fmin/fmax.  Three RISC-V rules a naive [fp_compare] would miss:
    one NaN operand yields the OTHER operand (both NaN yields the
    canonical NaN), NV is raised only for a SIGNALLING NaN, and −0 is
    strictly less than +0 even though [SFcompare] calls them equal —
    so the equal case is decided on the sign bits. *)
Definition fp_minmax (f : format) (is_max : bool) (a b : Z) : Z * fflags :=
  let fl := if orb (fp_is_snan f a) (fp_is_snan f b) then nv_flag else no_flags in
  if andb (fp_is_nan f a) (fp_is_nan f b) then (fp_canonical_nan f, fl)
  else if fp_is_nan f a then (b, fl)
  else if fp_is_nan f b then (a, fl)
  else
    let a_lt_b :=
      match fp_compare f a b with
      | Some Lt => true
      | Some Eq => andb (fp_sign_bit f a) (negb (fp_sign_bit f b))
      | _ => false
      end in
    ((if xorb is_max a_lt_b then a else b), fl).

(** The fclass bit mask: bit 0 −inf, 1 −normal, 2 −subnormal, 3 −0,
    4 +0, 5 +subnormal, 6 +normal, 7 +inf, 8 sNaN, 9 qNaN. *)
Definition fp_class (f : format) (a : Z) : Z :=
  let s := fp_sign_bit f a in
  let e := fp_exp_field f a in
  let m := fp_man_field f a in
  if Z.eqb e (Z.ones (fp_ew f)) then
    (if Z.eqb m 0 then (if s then 1 else Z.shiftl 1 7)
     else if fp_is_snan f a then Z.shiftl 1 8 else Z.shiftl 1 9)
  else if Z.eqb e 0 then
    (if Z.eqb m 0 then (if s then Z.shiftl 1 3 else Z.shiftl 1 4)
     else if s then Z.shiftl 1 2 else Z.shiftl 1 5)
  else (if s then Z.shiftl 1 1 else Z.shiftl 1 6).

(** ** Conversions *)

(** float → integer.  [bits] is the integer width (32 or 64) and
    [signed] its signedness; the answer is the RAW two's-complement
    value in that width, which [Sem] sign-extends into the 64-bit
    destination register (RISC-V sign-extends fcvt.wu's unsigned
    result too).

    Saturation, not wraparound: an out-of-range magnitude, an
    infinity or a NaN gives the nearest representable integer and
    raises NV.  A NaN gives the MAXIMUM in both signednesses.  NV
    suppresses NX, so a saturated conversion reports exactly one
    exception. *)

Definition int_lo (signed : bool) (bits : Z) : Z :=
  if signed then Z.opp (Z.shiftl 1 (bits - 1)) else 0.
Definition int_hi (signed : bool) (bits : Z) : Z :=
  if signed then Z.shiftl 1 (bits - 1) - 1 else Z.shiftl 1 bits - 1.

(** Two's-complement image of [v] in [bits] bits. *)
Definition int_wrap (bits v : Z) : Z := Z.land v (Z.ones bits).

Definition fp_to_int (f : format) (md : rmode) (signed : bool) (bits : Z)
    (a : Z) : Z * fflags :=
  let sat (v : Z) := (int_wrap bits v, nv_flag) in
  if fp_is_nan f a then sat (int_hi signed bits)
  else
    match fp_decode f a with
    | S754_infinity s => sat (if s then int_lo signed bits else int_hi signed bits)
    | S754_zero _ => (0, no_flags)
    | S754_nan => sat (int_hi signed bits)   (* unreachable *)
    | S754_finite s m e =>
        (* Split the scaled mantissa at the binary point: [q] is the
           truncated magnitude, [l] says where the discarded part sits
           between [q] and [q+1], and [choice_mode] applies the
           rounding rule to the MAGNITUDE with the sign supplied
           separately — the same convention the FP kernel uses. *)
        let '(q, l) :=
          if Z.leb 0 e then (Z.shiftl (Z.pos m) e, loc_Exact)
          else
            let d := Z.shiftl 1 (Z.opp e) in
            let '(q, r) := Z.div_eucl (Z.pos m) d in
            (q, new_location d r) in
        let q' := BinarySingleNaN.choice_mode (flocq_mode md) s q l in
        let v := if s then Z.opp q' else q' in
        if orb (Z.ltb v (int_lo signed bits)) (Z.ltb (int_hi signed bits) v)
        then sat (if s then int_lo signed bits else int_hi signed bits)
        else (int_wrap bits v,
              match l with loc_Exact => no_flags | _ => nx_flag end)
    end.

(** integer → float.  [v] is the raw [bits]-wide value from the
    source register, read with the requested signedness before
    rounding. *)
Definition fp_of_int (f : format) (md : rmode) (signed : bool) (bits : Z)
    (v : Z) : Z * fflags :=
  let u := int_wrap bits v in
  let n := if andb signed (Z.testbit u (bits - 1))
           then u - Z.shiftl 1 bits else u in
  enc f (round_scaled f md false (n, 0)).

(** float → float.  Widening is exact; narrowing rounds and can
    overflow or underflow, so both directions go through the same
    kernel and the flags fall out.  A NaN converts to the
    DESTINATION's canonical NaN, and a signalling one raises NV. *)
Definition fp_convert (src dst : format) (md : rmode) (a : Z) : Z * fflags :=
  if fp_is_nan src a
  then (fp_canonical_nan dst, if fp_is_snan src a then nv_flag else no_flags)
  else
    match fp_decode src a with
    | S754_zero s => (fp_encode dst (S754_zero s), no_flags)
    | S754_infinity s => (fp_encode dst (S754_infinity s), no_flags)
    | S754_nan => (fp_canonical_nan dst, no_flags)   (* unreachable *)
    | S754_finite s m e => enc dst (round_exact dst md s m e)
    end.
