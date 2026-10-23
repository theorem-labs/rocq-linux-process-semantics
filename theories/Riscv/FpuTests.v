(** * FpuTests: in-Rocq checks of the FP semantics

    An instruction-by-instruction differential test against the Sail
    RISC-V model (both sides get the same FP register file and fcsr,
    execute one instruction, and are compared on all 32 FP registers
    plus fcsr) covers the arithmetic, the flags and the special cases
    far more thoroughly than a hand-written table could.

    What it CANNOT cover is the cases where the answer is "illegal
    instruction": a reserved rounding mode traps under Sail, and a
    trap is not a state such a test can compare a retired instruction
    against — it can only observe that both sides declined, which says
    nothing about WHICH of them declined for the right reason.  Those
    cases live here instead, together with a small table of results
    that are worth pinning in the source tree because they are the
    ones a reader is most likely to want to check by hand: the
    rounding modes at a tie, the boundary where UNDERFLOW switches on,
    saturation, and NaN canonicalization.

    Every check is [Definition ... := eq_refl], i.e. discharged by
    computation, so this file also demonstrates that the semantics
    REDUCES — an FP instruction has to evaluate inside the example
    proofs' symbolic-execution engine, not merely typecheck. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.

Local Open Scope Z_scope.

(** ** Rounding-mode resolution

    rm = 0..4 are the architectural modes, 7 is DYNAMIC (take frm from
    fcsr), and 5 and 6 are RESERVED.  A reserved mode — statically, or
    dynamically via a reserved frm — is an illegal instruction. *)

Definition rm_static_ok : rmode_of_field 0 0 = Some RNE := eq_refl.
Definition rm_static_rtz : rmode_of_field 1 0 = Some RTZ := eq_refl.
Definition rm_static_rdn : rmode_of_field 2 0 = Some RDN := eq_refl.
Definition rm_static_rup : rmode_of_field 3 0 = Some RUP := eq_refl.
Definition rm_static_rmm : rmode_of_field 4 0 = Some RMM := eq_refl.

(** The two reserved encodings, whatever frm says. *)
Definition rm_reserved_5 : rmode_of_field 5 0 = None := eq_refl.
Definition rm_reserved_6 : rmode_of_field 6 0 = None := eq_refl.
Definition rm_reserved_5_frm : rmode_of_field 5 2 = None := eq_refl.

(** DYN reads frm... *)
Definition rm_dyn_rne : rmode_of_field 7 0 = Some RNE := eq_refl.
Definition rm_dyn_rdn : rmode_of_field 7 2 = Some RDN := eq_refl.
Definition rm_dyn_rmm : rmode_of_field 7 4 = Some RMM := eq_refl.

(** ...and inherits frm's reserved values: 5, 6 and 7 are not modes. *)
Definition rm_dyn_reserved_5 : rmode_of_field 7 5 = None := eq_refl.
Definition rm_dyn_reserved_6 : rmode_of_field 7 6 = None := eq_refl.
Definition rm_dyn_reserved_7 : rmode_of_field 7 7 = None := eq_refl.

(** ** Reserved rounding modes are illegal instructions

    At the [Sem] level: a reserved rm makes [exec] issue [EIllegal]
    with the pc ALREADY ADVANCED (the pc-advance contract), rather
    than defaulting to round-to-nearest and retiring a wrong answer.
    The same instruction with a legal rm retires. *)

Definition core0 (fcsr : Z) : core :=
  {| c_regs := bvmap_empty;
     c_fregs := bvmap_set 1 (Z_to_bv 64 0x3ff0000000000000)
                  (bvmap_set 2 (Z_to_bv 64 0x4008000000000000) bvmap_empty);
     c_pc := Z_to_bv 64 0x1000;
     c_fcsr := Z_to_bv 32 fcsr;
     c_resv := None |}.

(** fadd.d f3, f1, f2 with rm = 5 (reserved). *)
Definition fadd_rm5_illegal :
  exec (Z_to_bv 64 4) (Fari F_ADD FMT_D 3 1 2 5) (core0 0)
  = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := eq_refl.

Definition fadd_rm6_illegal :
  exec (Z_to_bv 64 4) (Fari F_ADD FMT_D 3 1 2 6) (core0 0)
  = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := eq_refl.

(** rm = DYN with frm = 5 (fcsr = 5 << 5 = 0xa0) is illegal too: the
    reserved mode reaches the instruction through fcsr. *)
Definition fadd_dyn_reserved_frm_illegal :
  exec (Z_to_bv 64 4) (Fari F_ADD FMT_D 3 1 2 7) (core0 0xa0)
  = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0xa0)) := eq_refl.

(** The same instruction with a legal rm retires, writing 1.0 + 3.0 =
    4.0 into f3 and leaving fcsr alone (the result is exact). *)
Definition fadd_rm0_retires :
  exec (Z_to_bv 64 4) (Fari F_ADD FMT_D 3 1 2 0) (core0 0)
  = EDone (fset 3 (Z_to_bv 64 0x4010000000000000)
                (with_pc (Z_to_bv 64 0x1004) (core0 0))) := eq_refl.

(** Reserved modes on the other rm-bearing instructions. *)
Definition fsqrt_rm5_illegal :
  exec (Z_to_bv 64 4) (Fsqrt FMT_D 3 1 5) (core0 0)
  = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := eq_refl.

Definition fma_rm6_illegal :
  exec (Z_to_bv 64 4) (Fma F_MADD FMT_D 3 1 2 1 6) (core0 0)
  = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := eq_refl.

Definition fcvt_rm5_illegal :
  exec (Z_to_bv 64 4) (Fcvt FC_W FC_D 3 1 5) (core0 0)
  = EIllegal (with_pc (Z_to_bv 64 0x1004) (core0 0)) := eq_refl.

(** ** Rounding at a tie

    3.0 / 2.0 is exact; 1.0 / 3.0 is not, and the five modes disagree
    about it in the two directions a reader can check by eye (RDN and
    RTZ truncate a positive value, RUP goes the other way). *)

Abbreviation D := fmt_double.

Definition div_rne : fp_div D RNE 0x3ff0000000000000 0x4008000000000000
  = (0x3fd5555555555555, nx_flag) := eq_refl.
Definition div_rtz : fp_div D RTZ 0x3ff0000000000000 0x4008000000000000
  = (0x3fd5555555555555, nx_flag) := eq_refl.
Definition div_rup : fp_div D RUP 0x3ff0000000000000 0x4008000000000000
  = (0x3fd5555555555556, nx_flag) := eq_refl.

(** A tie under RNE goes to the EVEN mantissa; under RMM it goes away
    from zero.  0x1.0000000000001 8 is exactly halfway between two
    doubles when it comes out of a sum of two exact operands. *)
Definition tie_rne :
  fp_add D RNE 0x4340000000000000 0x3ff0000000000000
  = (0x4340000000000000, nx_flag) := eq_refl.
Definition tie_rmm :
  fp_add D RMM 0x4340000000000000 0x3ff0000000000000
  = (0x4340000000000001, nx_flag) := eq_refl.

(** ** Overflow

    Which of ±inf and ±MAXFLOAT an overflow produces is
    rounding-mode dependent, and both raise OF and NX. *)
Definition overflow_rne :
  fp_mul D RNE 0x7fefffffffffffff 0x4000000000000000
  = (0x7ff0000000000000, Fflags false false true false true) := eq_refl.
Definition overflow_rtz :
  fp_mul D RTZ 0x7fefffffffffffff 0x4000000000000000
  = (0x7fefffffffffffff, Fflags false false true false true) := eq_refl.
Definition overflow_rdn :
  fp_mul D RDN 0x7fefffffffffffff 0x4000000000000000
  = (0x7fefffffffffffff, Fflags false false true false true) := eq_refl.

(** ** Underflow is TINY AND INEXACT

    Halving the smallest normal is exact and lands on a subnormal:
    tiny, but NOT inexact, so no flag at all.  Halving the smallest
    SUBNORMAL is inexact and rounds to zero: tiny and inexact, so UF
    and NX. *)
Definition subnormal_exact_no_uf :
  fp_div D RNE 0x0010000000000000 0x4000000000000000
  = (0x0008000000000000, no_flags) := eq_refl.
Definition subnormal_inexact_uf :
  fp_div D RNE 0x0000000000000001 0x4000000000000000
  = (0x0000000000000000, Fflags false false false true true) := eq_refl.

(** Tininess is detected AFTER ROUNDING — rounding to 53 bits AS
    THOUGH THE EXPONENT RANGE WERE UNBOUNDED, which is finer than the
    subnormal grid the delivered result is quantized to.  This trio
    pins the distinction.

    The exact product 2^-1022 * (1 - 2^-53) = 2^-1022 - 2^-1075 IS a
    53-bit value, so the unbounded-range rounding returns it exactly,
    below the smallest normal: tiny.  Under RNE the DELIVERED result
    still carries up to the smallest normal (the product is the
    midpoint of the last subnormal gap and the normal's mantissa is
    the even one) — a normal result whose UF flag is set, the case a
    delivered-result-is-subnormal test gets wrong.  Under RTZ the delivered
    result stays subnormal, so UF as well. *)
Definition tiny_carries_to_normal_uf :
  fp_mul D RNE 0x0010000000000000 0x3fefffffffffffff
  = (0x0010000000000000, Fflags false false false true true) := eq_refl.
Definition tiny_stays_subnormal_uf :
  fp_mul D RTZ 0x0010000000000000 0x3fefffffffffffff
  = (0x000fffffffffffff, Fflags false false false true true) := eq_refl.

(** ...whereas a product HALF AN UNBOUNDED ULP higher, 2^-1022 -
    2^-1076 = (2^27-1)(2^27+1) * 2^-1076, rounds up to the smallest
    normal even with the exponent range unbounded (an RNE tie whose
    even mantissa is the normal's): NOT tiny, NX alone. *)
Definition not_tiny_at_unbounded_range_no_uf :
  fp_mul D RNE 0x1ffffffffc000000 0x2000000002000000
  = (0x0010000000000000, nx_flag) := eq_refl.

(** The same boundary for a QUOTIENT.  (2^-1021 - 2^-1074) / 2 is
    2^-1022 - 2^-1075 again, the midpoint of the last subnormal gap, so
    the division must flag it exactly as the product above: UF and NX
    under RNE, where the delivered result carries up to the smallest
    normal, and under RTZ, where it stays subnormal.  The single and RUP
    forms are the same case: 2^-126 / (1 + 2^-23) lies in the last gap
    and RUP delivers 2^-126. *)
Definition div_tiny_carries_to_normal_uf :
  fp_div D RNE 0x001fffffffffffff 0x4000000000000000
  = (0x0010000000000000, Fflags false false false true true) := eq_refl.
Definition div_tiny_stays_subnormal_uf :
  fp_div D RTZ 0x001fffffffffffff 0x4000000000000000
  = (0x000fffffffffffff, Fflags false false false true true) := eq_refl.
Definition div_tiny_carries_to_normal_uf_s_rup :
  fp_div fmt_single RUP 0x00800000 0x3f800001
  = (0x00800000, Fflags false false false true true) := eq_refl.

(** The directed-rounding shape of the same boundary, in single
    precision (fmsub.s / fmsub.d under RDN).  RDN on a NEGATIVE
    result rounds the magnitude up, so an exact fused result in the
    last gap below the smallest normal delivers -2^-126 either way;
    whether UF comes with NX depends on which side of the last
    UNBOUNDED-grid point (2^-126 - 2^-150) the exact value lies.
    fmsub rs1*rs2 - rs3 is [fp_fma] of the negated addend, so these
    pin the fused path end to end:

    (1 - 3*2^-24) * -2^-127 - 2^-127     = -(2^-126 - 3*2^-151), below
      the last grid point: the unbounded rounding stays tiny, UF+NX;
    (1 - 3*2^-24) * -2^-128 - 3*2^-128   = -(2^-126 - 3*2^-152), above
      it: even the unbounded rounding reaches -2^-126, NX alone. *)
Abbreviation S := fmt_single.

Definition fused_tiny_carries_to_normal_uf :
  fp_fma S RDN 0x3f7ffffd 0x80400000 0x80400000
  = (0x80800000, Fflags false false false true true) := eq_refl.
Definition fused_not_tiny_no_uf :
  fp_fma S RDN 0x3f7ffffd 0x80200000 0x80600000
  = (0x80800000, nx_flag) := eq_refl.

(** ** Invalid operations and divide by zero *)
Definition inf_minus_inf :
  fp_add D RNE 0x7ff0000000000000 0xfff0000000000000
  = (0x7ff8000000000000, nv_flag) := eq_refl.
Definition zero_times_inf :
  fp_mul D RNE 0 0x7ff0000000000000
  = (0x7ff8000000000000, nv_flag) := eq_refl.
Definition one_over_zero :
  fp_div D RNE 0x3ff0000000000000 0
  = (0x7ff0000000000000, dz_flag) := eq_refl.
Definition zero_over_zero :
  fp_div D RNE 0 0 = (0x7ff8000000000000, nv_flag) := eq_refl.
Definition sqrt_negative :
  fp_sqrt D RNE 0xbff0000000000000 = (0x7ff8000000000000, nv_flag) := eq_refl.
(** sqrt(-0) is -0, the one negative input with a result. *)
Definition sqrt_negative_zero :
  fp_sqrt D RNE 0x8000000000000000 = (0x8000000000000000, no_flags) := eq_refl.

(** A quiet NaN operand propagates as the CANONICAL NaN and raises
    nothing; a signalling one raises NV.  Payloads never survive, so
    a non-canonical quiet NaN comes back canonical.  The quiet bit is
    the TOP mantissa bit, which is why 0x7ff4... is signalling and
    0x7ffc... is quiet even though both have a nonzero payload. *)
Definition qnan_propagates_canonical :
  fp_add D RNE 0x7ffc000000000000 0x3ff0000000000000
  = (0x7ff8000000000000, no_flags) := eq_refl.
Definition snan_payload_raises_nv :
  fp_add D RNE 0x7ff4000000000000 0x3ff0000000000000
  = (0x7ff8000000000000, nv_flag) := eq_refl.
Definition snan_raises_nv :
  fp_add D RNE 0x7ff0000000000001 0x3ff0000000000000
  = (0x7ff8000000000000, nv_flag) := eq_refl.

(** ** Comparisons

    feq is quiet, flt is signalling: with a QUIET NaN operand they
    both answer false, but only flt raises NV. *)
Definition feq_qnan_quiet :
  fp_eq D 0x7ff8000000000000 0x3ff0000000000000 = (false, no_flags) := eq_refl.
Definition flt_qnan_signals :
  fp_lt D 0x7ff8000000000000 0x3ff0000000000000 = (false, nv_flag) := eq_refl.
Definition feq_snan_signals :
  fp_eq D 0x7ff0000000000001 0x3ff0000000000000 = (false, nv_flag) := eq_refl.
(** -0 compares EQUAL to +0. *)
Definition feq_zeros : fp_eq D 0x8000000000000000 0 = (true, no_flags) := eq_refl.

(** ** fmin/fmax

    A single NaN operand yields the OTHER operand — not a NaN — and
    only a signalling one raises NV.  -0 is strictly below +0, which
    the equal case of the comparison has to decide on the sign bits. *)
Definition fmin_qnan_returns_other :
  fp_minmax D false 0x7ff8000000000000 0x3ff0000000000000
  = (0x3ff0000000000000, no_flags) := eq_refl.
Definition fmax_snan_returns_other_with_nv :
  fp_minmax D true 0x7ff0000000000001 0x3ff0000000000000
  = (0x3ff0000000000000, nv_flag) := eq_refl.
Definition fmin_both_nan :
  fp_minmax D false 0x7ff8000000000000 0x7ff8000000000000
  = (0x7ff8000000000000, no_flags) := eq_refl.
Definition fmin_signed_zeros :
  fp_minmax D false 0x8000000000000000 0 = (0x8000000000000000, no_flags) := eq_refl.
Definition fmax_signed_zeros :
  fp_minmax D true 0x8000000000000000 0 = (0, no_flags) := eq_refl.

(** ** float -> integer saturates, and NV suppresses NX *)
Definition cvt_trunc : fp_to_int D RTZ true 32 0x400d999999999999
  = (3, nx_flag) := eq_refl.
Definition cvt_exact : fp_to_int D RTZ true 32 0x4008000000000000
  = (3, no_flags) := eq_refl.
Definition cvt_saturate_high : fp_to_int D RTZ true 32 0x41e0000000000000
  = (0x7fffffff, nv_flag) := eq_refl.
(** -(2^31) is representable, so truncating -(2^31 + 2^-21) to it is
    merely inexact; -(2^31 + 1) is the first value that saturates. *)
Definition cvt_low_edge_is_representable :
  fp_to_int D RTZ true 32 0xc1e0000000000001 = (0x80000000, nx_flag) := eq_refl.
Definition cvt_saturate_low : fp_to_int D RTZ true 32 0xc1e0000000200000
  = (0x80000000, nv_flag) := eq_refl.
(** A NaN gives the MAXIMUM in both signednesses. *)
Definition cvt_nan_signed : fp_to_int D RTZ true 32 0x7ff8000000000000
  = (0x7fffffff, nv_flag) := eq_refl.
Definition cvt_nan_unsigned : fp_to_int D RTZ false 32 0x7ff8000000000000
  = (0xffffffff, nv_flag) := eq_refl.
(** A negative value converted unsigned saturates to 0, NOT to a
    wrapped two's-complement pattern. *)
Definition cvt_negative_unsigned : fp_to_int D RTZ false 64 0xbff0000000000000
  = (0, nv_flag) := eq_refl.
(** -0.5 truncates to 0 under RTZ, and that IS a representable
    unsigned result: inexact, not invalid. *)
Definition cvt_neg_half_unsigned : fp_to_int D RTZ false 32 0xbfe0000000000000
  = (0, nx_flag) := eq_refl.

(** ** integer -> float and float -> float *)
Definition cvt_int_exact : fp_of_int D RNE true 64 12345
  = (0x40c81c8000000000, no_flags) := eq_refl.
(** 2^53 + 1 is not representable as a double: the conversion rounds. *)
Definition cvt_int_inexact : fp_of_int D RNE true 64 9007199254740993
  = (0x4340000000000000, nx_flag) := eq_refl.
(** Widening is exact; narrowing rounds. *)
Definition cvt_widen_exact : fp_convert fmt_single D RNE 0x3f800000
  = (0x3ff0000000000000, no_flags) := eq_refl.
Definition cvt_narrow_inexact : fp_convert D fmt_single RNE 0x3fd5555555555555
  = (0x3eaaaaab, nx_flag) := eq_refl.
(** A signalling NaN narrows to the DESTINATION's canonical NaN. *)
Definition cvt_snan : fp_convert D fmt_single RNE 0x7ff0000000000001
  = (0x7fc00000, nv_flag) := eq_refl.

(** ** fclass, one bit per class *)
Definition class_neg_inf : fp_class D 0xfff0000000000000 = 1 := eq_refl.
Definition class_neg_normal : fp_class D 0xbff0000000000000 = 2 := eq_refl.
Definition class_neg_subnormal : fp_class D 0x8000000000000001 = 4 := eq_refl.
Definition class_neg_zero : fp_class D 0x8000000000000000 = 8 := eq_refl.
Definition class_pos_zero : fp_class D 0 = 16 := eq_refl.
Definition class_pos_subnormal : fp_class D 0x0000000000000001 = 32 := eq_refl.
Definition class_pos_normal : fp_class D 0x3ff0000000000000 = 64 := eq_refl.
Definition class_pos_inf : fp_class D 0x7ff0000000000000 = 128 := eq_refl.
Definition class_snan : fp_class D 0x7ff0000000000001 = 256 := eq_refl.
Definition class_qnan : fp_class D 0x7ff8000000000000 = 512 := eq_refl.

(** ** NaN boxing

    A single-precision operand that is not boxed with all-ones in the
    high half reads as the canonical NaN, and every single-precision
    result is written back boxed. *)
(* Compared at [bv_unsigned]: two bitvectors with the same value can
   carry syntactically different well-formedness proofs, so the values
   are what a computational check can compare. *)
Definition unboxed_reads_as_nan :
  bv_unsigned (unbox_s (Z_to_bv 64 0x000000003f800000)) = 0x7fc00000 := eq_refl.
Definition boxed_reads_through :
  bv_unsigned (unbox_s (Z_to_bv 64 0xffffffff3f800000)) = 0x3f800000 := eq_refl.
Definition results_are_boxed :
  bv_unsigned (nan_box (Z_to_bv 32 0x3f800000)) = 0xffffffff3f800000 := eq_refl.

(** ** Flags ACCRUE

    fcsr[4:0] is sticky: an instruction ORs its exceptions in and
    clears nothing.  Starting from fcsr = NV set, an inexact divide
    leaves NV|NX. *)
Definition flags_accrue :
  bv_unsigned (c_fcsr (accrue nx_flag (core0 0x10))) = 0x11 := eq_refl.
Definition flags_preserve_frm :
  bv_unsigned (c_fcsr (accrue nx_flag (core0 0x60))) = 0x61 := eq_refl.
