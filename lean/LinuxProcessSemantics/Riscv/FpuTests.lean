-- Ports rocq-linux-process-semantics f1006fe8:theories/Riscv/FpuTests.v
import LinuxProcessSemantics.Riscv.Prelude
import LinuxProcessSemantics.Riscv.Instr
import LinuxProcessSemantics.Riscv.Fpu
import LinuxProcessSemantics.Riscv.Sem

/-! # FpuTests: in-Lean checks of the FP semantics

Mirrors `theories/Riscv/FpuTests.v`.

An instruction-by-instruction differential test against the Sail RISC-V
model (both sides get the same FP register file and fcsr, execute one
instruction, and are compared on all 32 FP registers plus fcsr) covers
the arithmetic, the flags and the special cases far more thoroughly than
a hand-written table could.

What it CANNOT cover is the cases where the answer is "illegal
instruction": a reserved rounding mode traps under Sail, and a trap is
not a state such a test can compare a retired instruction against — it
can only observe that both sides declined, which says nothing about
WHICH of them declined for the right reason.  Those cases live here
instead, together with a small table of results that are worth pinning
in the source tree because they are the ones a reader is most likely to
want to check by hand: the rounding modes at a tie, the boundary where
UNDERFLOW switches on, saturation, and NaN canonicalization.

Every check is Rocq's `Definition … := eq_refl`, i.e. discharged by
computation, so this file also demonstrates that the semantics REDUCES —
an FP instruction has to evaluate inside the kernel, not merely
typecheck.  Here that is `by decide` wherever the two sides have a
`DecidableEq`, and `by rfl` for the seven `exec` pins, whose `eff` holds
a continuation function and so has none.  Rocq's names are kept, as
`theorem`s rather than `Definition`s: a Rocq `Definition x : a = b :=
eq_refl` and a Lean `theorem x : a = b := by decide` are the same
claim, closed the same way. -/

namespace LinuxProcessSemantics.Riscv.FpuTests

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Fpu
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Riscv.Sem.eff

/-! ## Rounding-mode resolution

rm = 0..4 are the architectural modes, 7 is DYNAMIC (take frm from
fcsr), and 5 and 6 are RESERVED.  A reserved mode — statically, or
dynamically via a reserved frm — is an illegal instruction. -/

theorem rm_static_ok : rmode_of_field 0 0 = some RNE := by decide
theorem rm_static_rtz : rmode_of_field 1 0 = some RTZ := by decide
theorem rm_static_rdn : rmode_of_field 2 0 = some RDN := by decide
theorem rm_static_rup : rmode_of_field 3 0 = some RUP := by decide
theorem rm_static_rmm : rmode_of_field 4 0 = some RMM := by decide

/-! The two reserved encodings, whatever frm says. -/
theorem rm_reserved_5 : rmode_of_field 5 0 = none := by decide
theorem rm_reserved_6 : rmode_of_field 6 0 = none := by decide
theorem rm_reserved_5_frm : rmode_of_field 5 2 = none := by decide

/-! DYN reads frm... -/
theorem rm_dyn_rne : rmode_of_field 7 0 = some RNE := by decide
theorem rm_dyn_rdn : rmode_of_field 7 2 = some RDN := by decide
theorem rm_dyn_rmm : rmode_of_field 7 4 = some RMM := by decide

/-! ...and inherits frm's reserved values: 5, 6 and 7 are not modes. -/
theorem rm_dyn_reserved_5 : rmode_of_field 7 5 = none := by decide
theorem rm_dyn_reserved_6 : rmode_of_field 7 6 = none := by decide
theorem rm_dyn_reserved_7 : rmode_of_field 7 7 = none := by decide

/-! ## Reserved rounding modes are illegal instructions

At the `Sem` level: a reserved rm makes `exec` issue `EIllegal` with the
pc ALREADY ADVANCED (the pc-advance contract), rather than defaulting to
round-to-nearest and retiring a wrong answer.  The same instruction with
a legal rm retires. -/

def core0 (fcsr : Int) : core :=
  core.Core bvmap_empty
    (bvmap_set 1 (Z_to_bv 64 0x3ff0000000000000)
      (bvmap_set 2 (Z_to_bv 64 0x4008000000000000) bvmap_empty))
    (Z_to_bv 64 0x1000)
    (Z_to_bv 32 fcsr)
    none

/-- fadd.d f3, f1, f2 with rm = 5 (reserved). -/
theorem fadd_rm5_illegal :
    exec (Z_to_bv 64 4) (instr.Fari .F_ADD .FMT_D 3 1 2 5) (core0 0)
      = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := by rfl

theorem fadd_rm6_illegal :
    exec (Z_to_bv 64 4) (instr.Fari .F_ADD .FMT_D 3 1 2 6) (core0 0)
      = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := by rfl

/-- rm = DYN with frm = 5 (fcsr = 5 << 5 = 0xa0) is illegal too: the
reserved mode reaches the instruction through fcsr. -/
theorem fadd_dyn_reserved_frm_illegal :
    exec (Z_to_bv 64 4) (instr.Fari .F_ADD .FMT_D 3 1 2 7) (core0 0xa0)
      = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0xa0)) := by rfl

/-- The same instruction with a legal rm retires, writing 1.0 + 3.0 = 4.0
into f3 and leaving fcsr alone (the result is exact).

`with_unfolding_all` because this is the one `exec` pin that READS the FP
register file: `bvmap_get` goes through `Prelude.positive.ofNat`, which is
well-founded, so the elaborator's `whnf` stops at it while the kernel
reduces it.  `Prelude.lean` works around the same thing with
`decide +kernel` (`key_zero`, `register_one_uses_left_child`); the proof
term is still `Eq.refl` and the kernel still checks it. -/
theorem fadd_rm0_retires :
    exec (Z_to_bv 64 4) (instr.Fari .F_ADD .FMT_D 3 1 2 0) (core0 0)
      = EDone (fset 3 (Z_to_bv 64 0x4010000000000000)
                 (with_pc (Z_to_bv 64 0x1004) (core0 0))) := by
  with_unfolding_all rfl

/-! Reserved modes on the other rm-bearing instructions. -/

theorem fsqrt_rm5_illegal :
    exec (Z_to_bv 64 4) (instr.Fsqrt .FMT_D 3 1 5) (core0 0)
      = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := by rfl

theorem fma_rm6_illegal :
    exec (Z_to_bv 64 4) (instr.Fma .F_MADD .FMT_D 3 1 2 1 6) (core0 0)
      = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := by rfl

theorem fcvt_rm5_illegal :
    exec (Z_to_bv 64 4) (instr.Fcvt .FC_W .FC_D 3 1 5) (core0 0)
      = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := by rfl

/-! ## Rounding at a tie

3.0 / 2.0 is exact; 1.0 / 3.0 is not, and the five modes disagree about
it in the two directions a reader can check by eye (RDN and RTZ truncate
a positive value, RUP goes the other way). -/

/-- Rocq's `Abbreviation D := fmt_double`. -/
abbrev D : format := fmt_double

theorem div_rne : fp_div D RNE 0x3ff0000000000000 0x4008000000000000
    = (0x3fd5555555555555, nx_flag) := by decide
theorem div_rtz : fp_div D RTZ 0x3ff0000000000000 0x4008000000000000
    = (0x3fd5555555555555, nx_flag) := by decide
theorem div_rup : fp_div D RUP 0x3ff0000000000000 0x4008000000000000
    = (0x3fd5555555555556, nx_flag) := by decide

/-- A tie under RNE goes to the EVEN mantissa; under RMM it goes away
from zero.  0x1.0000000000001 8 is exactly halfway between two doubles
when it comes out of a sum of two exact operands. -/
theorem tie_rne :
    fp_add D RNE 0x4340000000000000 0x3ff0000000000000
      = (0x4340000000000000, nx_flag) := by decide
theorem tie_rmm :
    fp_add D RMM 0x4340000000000000 0x3ff0000000000000
      = (0x4340000000000001, nx_flag) := by decide

/-! ## Overflow

Which of ±inf and ±MAXFLOAT an overflow produces is rounding-mode
dependent, and both raise OF and NX. -/

theorem overflow_rne :
    fp_mul D RNE 0x7fefffffffffffff 0x4000000000000000
      = (0x7ff0000000000000, fflags.Fflags false false true false true) := by decide
theorem overflow_rtz :
    fp_mul D RTZ 0x7fefffffffffffff 0x4000000000000000
      = (0x7fefffffffffffff, fflags.Fflags false false true false true) := by decide
theorem overflow_rdn :
    fp_mul D RDN 0x7fefffffffffffff 0x4000000000000000
      = (0x7fefffffffffffff, fflags.Fflags false false true false true) := by decide

/-! ## Underflow is TINY AND INEXACT

Halving the smallest normal is exact and lands on a subnormal: tiny, but
NOT inexact, so no flag at all.  Halving the smallest SUBNORMAL is
inexact and rounds to zero: tiny and inexact, so UF and NX. -/

theorem subnormal_exact_no_uf :
    fp_div D RNE 0x0010000000000000 0x4000000000000000
      = (0x0008000000000000, no_flags) := by decide
theorem subnormal_inexact_uf :
    fp_div D RNE 0x0000000000000001 0x4000000000000000
      = (0x0000000000000000, fflags.Fflags false false false true true) := by decide

/-- Tininess is detected AFTER ROUNDING — rounding to 53 bits AS THOUGH
THE EXPONENT RANGE WERE UNBOUNDED, which is finer than the subnormal grid
the delivered result is quantized to.  This trio pins the distinction.

The exact product `2^-1022 * (1 - 2^-53) = 2^-1022 - 2^-1075` IS a 53-bit
value, so the unbounded-range rounding returns it exactly, below the
smallest normal: tiny.  Under RNE the DELIVERED result still carries up
to the smallest normal (the product is the midpoint of the last subnormal
gap and the normal's mantissa is the even one) — a normal result whose UF
flag is set, the case a delivered-result-is-subnormal test gets wrong.
Under RTZ the delivered result stays subnormal, so UF as well. -/
theorem tiny_carries_to_normal_uf :
    fp_mul D RNE 0x0010000000000000 0x3fefffffffffffff
      = (0x0010000000000000, fflags.Fflags false false false true true) := by decide
theorem tiny_stays_subnormal_uf :
    fp_mul D RTZ 0x0010000000000000 0x3fefffffffffffff
      = (0x000fffffffffffff, fflags.Fflags false false false true true) := by decide

/-- ...whereas a product HALF AN UNBOUNDED ULP higher,
`2^-1022 - 2^-1076 = (2^27-1)(2^27+1) * 2^-1076`, rounds up to the
smallest normal even with the exponent range unbounded (an RNE tie whose
even mantissa is the normal's): NOT tiny, NX alone. -/
theorem not_tiny_at_unbounded_range_no_uf :
    fp_mul D RNE 0x1ffffffffc000000 0x2000000002000000
      = (0x0010000000000000, nx_flag) := by decide

/-! The directed-rounding shape of the same boundary, in single precision
(fmsub.s / fmsub.d under RDN).  RDN on a NEGATIVE result rounds the
magnitude up, so an exact fused result in the last gap below the smallest
normal delivers `-2^-126` either way; whether UF comes with NX depends on
which side of the last UNBOUNDED-grid point (`2^-126 - 2^-150`) the exact
value lies.  fmsub `rs1*rs2 - rs3` is `fp_fma` of the negated addend, so
these pin the fused path end to end:

    (1 - 3*2^-24) * -2^-127 - 2^-127     = -(2^-126 - 3*2^-151), below
      the last grid point: the unbounded rounding stays tiny, UF+NX;
    (1 - 3*2^-24) * -2^-128 - 3*2^-128   = -(2^-126 - 3*2^-152), above
      it: even the unbounded rounding reaches -2^-126, NX alone. -/

/-- Rocq's `Abbreviation S := fmt_single`. -/
abbrev S : format := fmt_single

theorem fused_tiny_carries_to_normal_uf :
    fp_fma S RDN 0x3f7ffffd 0x80400000 0x80400000
      = (0x80800000, fflags.Fflags false false false true true) := by decide
theorem fused_not_tiny_no_uf :
    fp_fma S RDN 0x3f7ffffd 0x80200000 0x80600000
      = (0x80800000, nx_flag) := by decide

/-! ## Invalid operations and divide by zero -/

theorem inf_minus_inf :
    fp_add D RNE 0x7ff0000000000000 0xfff0000000000000
      = (0x7ff8000000000000, nv_flag) := by decide
theorem zero_times_inf :
    fp_mul D RNE 0 0x7ff0000000000000
      = (0x7ff8000000000000, nv_flag) := by decide
theorem one_over_zero :
    fp_div D RNE 0x3ff0000000000000 0
      = (0x7ff0000000000000, dz_flag) := by decide
theorem zero_over_zero :
    fp_div D RNE 0 0 = (0x7ff8000000000000, nv_flag) := by decide
theorem sqrt_negative :
    fp_sqrt D RNE 0xbff0000000000000 = (0x7ff8000000000000, nv_flag) := by decide
/-- sqrt(-0) is -0, the one negative input with a result. -/
theorem sqrt_negative_zero :
    fp_sqrt D RNE 0x8000000000000000 = (0x8000000000000000, no_flags) := by decide

/-! A quiet NaN operand propagates as the CANONICAL NaN and raises
nothing; a signalling one raises NV.  Payloads never survive, so a
non-canonical quiet NaN comes back canonical.  The quiet bit is the TOP
mantissa bit, which is why 0x7ff4... is signalling and 0x7ffc... is quiet
even though both have a nonzero payload. -/

theorem qnan_propagates_canonical :
    fp_add D RNE 0x7ffc000000000000 0x3ff0000000000000
      = (0x7ff8000000000000, no_flags) := by decide
theorem snan_payload_raises_nv :
    fp_add D RNE 0x7ff4000000000000 0x3ff0000000000000
      = (0x7ff8000000000000, nv_flag) := by decide
theorem snan_raises_nv :
    fp_add D RNE 0x7ff0000000000001 0x3ff0000000000000
      = (0x7ff8000000000000, nv_flag) := by decide

/-! ## Comparisons

feq is quiet, flt is signalling: with a QUIET NaN operand they both
answer false, but only flt raises NV. -/

theorem feq_qnan_quiet :
    fp_eq D 0x7ff8000000000000 0x3ff0000000000000 = (false, no_flags) := by decide
theorem flt_qnan_signals :
    fp_lt D 0x7ff8000000000000 0x3ff0000000000000 = (false, nv_flag) := by decide
theorem feq_snan_signals :
    fp_eq D 0x7ff0000000000001 0x3ff0000000000000 = (false, nv_flag) := by decide
/-- -0 compares EQUAL to +0. -/
theorem feq_zeros : fp_eq D 0x8000000000000000 0 = (true, no_flags) := by decide

/-! ## fmin/fmax

A single NaN operand yields the OTHER operand — not a NaN — and only a
signalling one raises NV.  -0 is strictly below +0, which the equal case
of the comparison has to decide on the sign bits. -/

theorem fmin_qnan_returns_other :
    fp_minmax D false 0x7ff8000000000000 0x3ff0000000000000
      = (0x3ff0000000000000, no_flags) := by decide
theorem fmax_snan_returns_other_with_nv :
    fp_minmax D true 0x7ff0000000000001 0x3ff0000000000000
      = (0x3ff0000000000000, nv_flag) := by decide
theorem fmin_both_nan :
    fp_minmax D false 0x7ff8000000000000 0x7ff8000000000000
      = (0x7ff8000000000000, no_flags) := by decide
theorem fmin_signed_zeros :
    fp_minmax D false 0x8000000000000000 0
      = (0x8000000000000000, no_flags) := by decide
theorem fmax_signed_zeros :
    fp_minmax D true 0x8000000000000000 0 = (0, no_flags) := by decide

/-! ## float -> integer saturates, and NV suppresses NX -/

theorem cvt_trunc : fp_to_int D RTZ true 32 0x400d999999999999
    = (3, nx_flag) := by decide
theorem cvt_exact : fp_to_int D RTZ true 32 0x4008000000000000
    = (3, no_flags) := by decide
theorem cvt_saturate_high : fp_to_int D RTZ true 32 0x41e0000000000000
    = (0x7fffffff, nv_flag) := by decide
/-- -(2^31) is representable, so truncating -(2^31 + 2^-21) to it is
merely inexact; -(2^31 + 1) is the first value that saturates. -/
theorem cvt_low_edge_is_representable :
    fp_to_int D RTZ true 32 0xc1e0000000000001 = (0x80000000, nx_flag) := by decide
theorem cvt_saturate_low : fp_to_int D RTZ true 32 0xc1e0000000200000
    = (0x80000000, nv_flag) := by decide
/-- A NaN gives the MAXIMUM in both signednesses. -/
theorem cvt_nan_signed : fp_to_int D RTZ true 32 0x7ff8000000000000
    = (0x7fffffff, nv_flag) := by decide
theorem cvt_nan_unsigned : fp_to_int D RTZ false 32 0x7ff8000000000000
    = (0xffffffff, nv_flag) := by decide
/-- A negative value converted unsigned saturates to 0, NOT to a wrapped
two's-complement pattern. -/
theorem cvt_negative_unsigned : fp_to_int D RTZ false 64 0xbff0000000000000
    = (0, nv_flag) := by decide
/-- -0.5 truncates to 0 under RTZ, and that IS a representable unsigned
result: inexact, not invalid. -/
theorem cvt_neg_half_unsigned : fp_to_int D RTZ false 32 0xbfe0000000000000
    = (0, nx_flag) := by decide

/-! ## integer -> float and float -> float -/

theorem cvt_int_exact : fp_of_int D RNE true 64 12345
    = (0x40c81c8000000000, no_flags) := by decide
/-- 2^53 + 1 is not representable as a double: the conversion rounds. -/
theorem cvt_int_inexact : fp_of_int D RNE true 64 9007199254740993
    = (0x4340000000000000, nx_flag) := by decide
/-! Widening is exact; narrowing rounds. -/
theorem cvt_widen_exact : fp_convert fmt_single D RNE 0x3f800000
    = (0x3ff0000000000000, no_flags) := by decide
theorem cvt_narrow_inexact : fp_convert D fmt_single RNE 0x3fd5555555555555
    = (0x3eaaaaab, nx_flag) := by decide
/-- A signalling NaN narrows to the DESTINATION's canonical NaN. -/
theorem cvt_snan : fp_convert D fmt_single RNE 0x7ff0000000000001
    = (0x7fc00000, nv_flag) := by decide

/-! ## fclass, one bit per class -/

theorem class_neg_inf : fp_class D 0xfff0000000000000 = 1 := by decide
theorem class_neg_normal : fp_class D 0xbff0000000000000 = 2 := by decide
theorem class_neg_subnormal : fp_class D 0x8000000000000001 = 4 := by decide
theorem class_neg_zero : fp_class D 0x8000000000000000 = 8 := by decide
theorem class_pos_zero : fp_class D 0 = 16 := by decide
theorem class_pos_subnormal : fp_class D 0x0000000000000001 = 32 := by decide
theorem class_pos_normal : fp_class D 0x3ff0000000000000 = 64 := by decide
theorem class_pos_inf : fp_class D 0x7ff0000000000000 = 128 := by decide
theorem class_snan : fp_class D 0x7ff0000000000001 = 256 := by decide
theorem class_qnan : fp_class D 0x7ff8000000000000 = 512 := by decide

/-! ## NaN boxing

A single-precision operand that is not boxed with all-ones in the high
half reads as the canonical NaN, and every single-precision result is
written back boxed.

Compared at `bv_unsigned`: two bitvectors with the same value can carry
syntactically different well-formedness proofs, so the values are what a
computational check can compare. -/

theorem unboxed_reads_as_nan :
    bv_unsigned (unbox_s (Z_to_bv 64 0x000000003f800000)) = 0x7fc00000 := by decide
theorem boxed_reads_through :
    bv_unsigned (unbox_s (Z_to_bv 64 0xffffffff3f800000)) = 0x3f800000 := by decide
theorem results_are_boxed :
    bv_unsigned (nan_box (Z_to_bv 32 0x3f800000)) = 0xffffffff3f800000 := by decide

/-! ## Flags ACCRUE

fcsr[4:0] is sticky: an instruction ORs its exceptions in and clears
nothing.  Starting from fcsr = NV set, an inexact divide leaves NV|NX. -/

theorem flags_accrue :
    bv_unsigned (accrue nx_flag (core0 0x10)).c_fcsr = 0x11 := by decide
theorem flags_preserve_frm :
    bv_unsigned (accrue nx_flag (core0 0x60)).c_fcsr = 0x61 := by decide

end LinuxProcessSemantics.Riscv.FpuTests
