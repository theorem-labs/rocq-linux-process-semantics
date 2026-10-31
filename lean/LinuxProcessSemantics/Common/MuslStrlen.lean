import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StepTac

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.MuslStrlen — musl's word-at-a-time `strlen`, shared machinery

Ported from `theories/Common/MuslStrlen.v` at the baseline above, with the
Rocq names and statements.  Read that file's header before reusing
`read_word_stack` or `argv_word_readable`: it says why musl's has-zero test
is exact at word granularity but not byte by byte, which is why
`Tz_haszero` carries its "every lower byte nonzero" premise, and why the
word load's over-read past the NUL is sound for the argv and envp strings
of the initial stack image (the lemmas here state it for argv strings).
Its WARNING names cases the argument does not transfer to.  The walk over
the routine itself stays per example, for the reason that header gives.

At the baseline that header is wrong about pages, and nothing here rests on
what it says about them.  Its lines 53-56 say the model has no pages, but
the model maps the entry stack image to the top of its page
(`Run.entry_stack_image`, `Run.entry_page_top`), and the break and the
modeled `mmap` grant in whole pages (`Mmap.brk_zeros`, from a page-aligned
`Run.valid_brk`; the grant in `Mmap.mmap_spec` is page-aligned and
page-rounded).  So where its WARNING says a string ending at the last byte
of the break or of an mmap region over-reads into unmapped memory, a fault
in the model (its lines 71-73 and 78-79), it is false too: an aligned word
load that starts inside a whole-page mapping ends inside it.  The argument
here still does not transfer to such a string, for the other reason that
case gives: no AT_RANDOM tail follows it.

Spellings that differ:
- `Module HZ` is the namespace `HZ`.
- `Z.land`, `Z.lxor` and `Z.lor` are `PropExec`'s `Z_land`, `Z_lxor` and
  `Z_lor`, and `Z.shiftl y 8` is `Z_shiftl y 8`.  `Z.shiftr x n` at a
  non-negative `n` is `x >>> n`, which floors as `Z.shiftr` does.
- `2 ^ (8 * Z.of_nat i)` has the `Nat` exponent `8 * i`; elsewhere
  `Z.of_nat` is the `Nat`-to-`Int` cast.  Rocq's `/` and `mod` floor; at
  the positive divisors used here they agree with Lean's `/` and `%`.
- `Forall P l` is `∀ d ∈ l, P d`, `nth i l d` is `l.getD i d`, and
  `firstn`/`skipn` are `take`/`drop`.
- Section `ArgvWord`'s variables and hypotheses are explicit leading
  arguments, in Rocq's discharge order, and each lemma takes only the ones
  its Rocq original is discharged over.
- Rocq's `by8` tactic has no twin; the cases it closes by `vm_compute` are
  closed by `decide` here.

The Lean-only helpers say so in their docstrings.  Most are the stdlib bit
facts the Rocq proofs cite (`Z.bits_inj'`, `Z.land_spec`, `Z.lxor_spec`,
`Z.shiftr_land`, `Z.shiftr_lxor`, `Z.land_ones`, `Z.land_nonneg`), which
core Lean 4.34 does not state for this port's `Z_testbit`, `Z_land` and
`Z_lxor`.  Two more are stdlib bit facts no Rocq proof here cites:
`Z_testbit_shiftr` (`Z.shiftr_spec`), which the two shift facts' proofs go
through, and `Z_testbit_lor` (`Z.lor_spec`), whose docstring says why it
is stated. -/

namespace LinuxProcessSemantics.Common.MuslStrlen

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac

/-! ## Bits of `Z_land`, `Z_lxor` and `Z_lor` -/

/-- Lean-only helper: two naturals with no bit in common add without a
carry, so their sum is their or.  Core Lean 4.34 states this for `BitVec`
only, so it is read back through a width both operands fit in. -/
theorem nat_add_eq_or (c d : Nat) (h : c &&& d = 0) : c + d = c ||| d := by
  have hc : c < 2 ^ (c + d) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right c d))
  have hd : d < 2 ^ (c + d) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left d c))
  have hx : BitVec.ofNat (c + d) c &&& BitVec.ofNat (c + d) d = 0#(c + d) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hd, h, BitVec.toNat_zero]
  have h1 := BitVec.toNat_add_of_and_eq_zero hx
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hx, BitVec.toNat_or, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at h1
  exact h1.symm

/-- Lean-only helper: the and-not `a - (a &&& b)` that `Z_land` computes
at a mixed-sign pair is a bitwise operation, `a ^^^ (a &&& b)`: the bits of
`a &&& b` are among `a`'s, so the subtraction borrows nowhere. -/
theorem nat_sub_and (a b : Nat) : a - (a &&& b) = a ^^^ (a &&& b) := by
  have h0 : (a &&& b) &&& (a ^^^ (a &&& b)) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  have h1 : (a &&& b) ||| (a ^^^ (a &&& b)) = a := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  have h2 := nat_add_eq_or _ _ h0
  omega

/-- Lean-only helper: stdlib's `Z.land_spec` for `Z_land`, at the
non-negative bit indices `Z_testbit` reads. -/
theorem Z_testbit_land (a b : Int) (n : Nat) :
    Z_testbit (Z_land a b) n = (Z_testbit a n && Z_testbit b n) := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      show (a &&& b).testBit n = (a.testBit n && b.testBit n)
      exact Nat.testBit_and a b n
    | negSucc b =>
      show (a - (a &&& b)).testBit n = (a.testBit n && !(b.testBit n))
      rw [nat_sub_and, Nat.testBit_xor, Nat.testBit_and]
      cases a.testBit n <;> cases b.testBit n <;> rfl
  | negSucc a =>
    cases b with
    | ofNat b =>
      show (b - (b &&& a)).testBit n = (!(a.testBit n) && b.testBit n)
      rw [nat_sub_and, Nat.testBit_xor, Nat.testBit_and]
      cases a.testBit n <;> cases b.testBit n <;> rfl
    | negSucc b =>
      show (!((a ||| b).testBit n)) = (!(a.testBit n) && !(b.testBit n))
      rw [Nat.testBit_or]
      cases a.testBit n <;> cases b.testBit n <;> rfl

/-- Lean-only helper: stdlib's `Z.lxor_spec` for `Z_lxor`, at the
non-negative bit indices `Z_testbit` reads. -/
theorem Z_testbit_lxor (a b : Int) (n : Nat) :
    Z_testbit (Z_lxor a b) n = (Z_testbit a n ^^ Z_testbit b n) := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      show (a ^^^ b).testBit n = (a.testBit n ^^ b.testBit n)
      exact Nat.testBit_xor a b n
    | negSucc b =>
      show (!((a ^^^ b).testBit n)) = (a.testBit n ^^ !(b.testBit n))
      rw [Nat.testBit_xor]
      cases a.testBit n <;> cases b.testBit n <;> rfl
  | negSucc a =>
    cases b with
    | ofNat b =>
      show (!((a ^^^ b).testBit n)) = (!(a.testBit n) ^^ b.testBit n)
      rw [Nat.testBit_xor]
      cases a.testBit n <;> cases b.testBit n <;> rfl
    | negSucc b =>
      show (a ^^^ b).testBit n = (!(a.testBit n) ^^ !(b.testBit n))
      rw [Nat.testBit_xor]
      cases a.testBit n <;> cases b.testBit n <;> rfl

/-- Lean-only helper: stdlib's `Z.lor_spec` for `Z_lor`, at the
non-negative bit indices `Z_testbit` reads.  No Rocq proof here cites it;
`Z_lor_unique` combines it with `Z_bits_inj` to fix `Z_lor` at every
input, where `PropExec`'s examples check it only at the points they list.
`Z_lxor_unique` gives the corresponding result for `Z_testbit_lxor`. -/
theorem Z_testbit_lor (a b : Int) (n : Nat) :
    Z_testbit (Z_lor a b) n = (Z_testbit a n || Z_testbit b n) := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      show (a ||| b).testBit n = (a.testBit n || b.testBit n)
      exact Nat.testBit_or a b n
    | negSucc b =>
      show (!((b - (b &&& a)).testBit n)) = (a.testBit n || !(b.testBit n))
      rw [nat_sub_and, Nat.testBit_xor, Nat.testBit_and]
      cases a.testBit n <;> cases b.testBit n <;> rfl
  | negSucc a =>
    cases b with
    | ofNat b =>
      show (!((a - (a &&& b)).testBit n)) = (!(a.testBit n) || b.testBit n)
      rw [nat_sub_and, Nat.testBit_xor, Nat.testBit_and]
      cases a.testBit n <;> cases b.testBit n <;> rfl
    | negSucc b =>
      show (!((a &&& b).testBit n)) = (!(a.testBit n) || !(b.testBit n))
      rw [Nat.testBit_and]
      cases a.testBit n <;> cases b.testBit n <;> rfl

/-- Lean-only helper: stdlib's `Z.shiftr_spec` for Lean's floor shift
`>>>`, at a non-negative bit index. -/
theorem Z_testbit_shiftr (a : Int) (s n : Nat) :
    Z_testbit (a >>> s) n = Z_testbit a ((s + n : Nat) : Int) := by
  cases a with
  | ofNat a =>
    show (a >>> s).testBit n = a.testBit (s + n)
    exact Nat.testBit_shiftRight a
  | negSucc a =>
    show (!((a >>> s).testBit n)) = !(a.testBit (s + n))
    rw [Nat.testBit_shiftRight]

/-- Lean-only helper: stdlib's `Z.bits_inj'` — two integers with the same
bit at every non-negative index are equal.  A non-negative and a negative
integer cannot agree: past both magnitudes the first reads `false` and the
second `true`. -/
theorem Z_bits_inj (a b : Int) (h : ∀ n : Nat, Z_testbit a n = Z_testbit b n) : a = b := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      exact congrArg Int.ofNat (Nat.eq_of_testBit_eq fun i => h i)
    | negSucc b =>
      exfalso
      have hab := h (a + b)
      change a.testBit (a + b) = !(b.testBit (a + b)) at hab
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_right a b))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_left b a)))] at hab
      exact absurd hab (by decide)
  | negSucc a =>
    cases b with
    | ofNat b =>
      exfalso
      have hab := h (a + b)
      change (!(a.testBit (a + b))) = b.testBit (a + b) at hab
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_right a b))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_left b a)))] at hab
      exact absurd hab (by decide)
    | negSucc b =>
      have hab : a = b := Nat.eq_of_testBit_eq fun i => by
        have hi := h i
        change (!(a.testBit i)) = !(b.testBit i) at hi
        revert hi
        cases a.testBit i <;> cases b.testBit i <;> decide
      rw [hab]

/-- Lean-only characterization of `Z_lor` by its non-negative bits. -/
theorem Z_lor_unique (f : Int → Int → Int)
    (hf : ∀ (a b : Int) (n : Nat), Z_testbit (f a b) n = (Z_testbit a n || Z_testbit b n)) :
    ∀ a b : Int, f a b = Z_lor a b := by
  intro a b
  apply Z_bits_inj
  intro n
  rw [hf, Z_testbit_lor]

/-- Lean-only characterization of `Z_lxor` by its non-negative bits. -/
theorem Z_lxor_unique (f : Int → Int → Int)
    (hf : ∀ (a b : Int) (n : Nat), Z_testbit (f a b) n = (Z_testbit a n ^^ Z_testbit b n)) :
    ∀ a b : Int, f a b = Z_lxor a b := by
  intro a b
  apply Z_bits_inj
  intro n
  rw [hf, Z_testbit_lxor]

/-- Lean-only helper: stdlib's `Z.shiftr_land`. -/
theorem Z_shiftr_land (a b : Int) (s : Nat) : Z_land a b >>> s = Z_land (a >>> s) (b >>> s) := by
  apply Z_bits_inj
  intro n
  rw [Z_testbit_shiftr, Z_testbit_land, Z_testbit_land, Z_testbit_shiftr, Z_testbit_shiftr]

/-- Lean-only helper: stdlib's `Z.shiftr_lxor`. -/
theorem Z_shiftr_lxor (a b : Int) (s : Nat) : Z_lxor a b >>> s = Z_lxor (a >>> s) (b >>> s) := by
  apply Z_bits_inj
  intro n
  rw [Z_testbit_shiftr, Z_testbit_lxor, Z_testbit_lxor, Z_testbit_shiftr, Z_testbit_shiftr]

/-- Lean-only helper: stdlib's `Z.land_ones` at eight bits, the step Rocq's
`zb_alt` takes after `change 255 with (Z.ones 8)`. -/
theorem Z_land_255 (y : Int) : Z_land y 255 = y % 256 := by
  cases y with
  | ofNat y =>
    have h : y &&& 255 = y % 256 := Nat.and_two_pow_sub_one_eq_mod y 8
    show Int.ofNat (y &&& 255) = Int.ofNat y % 256
    rw [h, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
    omega
  | negSucc y =>
    have h : 255 &&& y = y % 256 := by
      rw [Nat.and_comm]
      exact Nat.and_two_pow_sub_one_eq_mod y 8
    show Int.ofNat (255 - (255 &&& y)) = Int.negSucc y % 256
    rw [h, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega

/-- Lean-only helper: stdlib's `Z.land_nonneg` with a non-negative left
operand, one of the two cases the Rocq proofs use (`land_le_r`,
`v_haszero`). -/
theorem Z_land_nonneg_l (a b : Int) (ha : 0 ≤ a) : 0 ≤ Z_land a b := by
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha
  cases b with
  | ofNat b =>
    show 0 ≤ ((a' &&& b : Nat) : Int)
    omega
  | negSucc b =>
    show 0 ≤ ((a' - (a' &&& b) : Nat) : Int)
    omega

/-- Lean-only helper: stdlib's `Z.land_nonneg` with a non-negative right
operand, the other case the Rocq proofs use (`Tz_range`, `v_haszero`). -/
theorem Z_land_nonneg_r (a b : Int) (hb : 0 ≤ b) : 0 ≤ Z_land a b := by
  obtain ⟨b', rfl⟩ := Int.eq_ofNat_of_zero_le hb
  cases a with
  | ofNat a =>
    show 0 ≤ ((a &&& b' : Nat) : Int)
    omega
  | negSucc a =>
    show 0 ≤ ((b' - (b' &&& a) : Nat) : Int)
    omega

/-! ## musl's word-at-a-time zero-byte test

`haszero(x) = (x - 0x0101..01) & ~x & 0x8080..80`, proved exact over
`Int` in `HZ`: `zb x i` is byte `i` of `x` and `zdig` is the little-endian
digit sum. -/

namespace HZ

/-- byte `i` of `x` -/
def zb (x : Int) (i : Nat) : Int := (x / 2 ^ (8 * i)) % 256

def zdig : List Int → Int
  | [] => 0
  | d :: r => d + 256 * zdig r

theorem pow2_8i_pos (i : Nat) : 0 < (2 : Int) ^ (8 * i) :=
  Int.pow_pos (by decide)

theorem zb_bound (x : Int) (i : Nat) : 0 ≤ zb x i ∧ zb x i < 256 := by
  unfold zb
  omega

theorem zb_0 (i : Nat) : zb 0 i = 0 := by
  unfold zb
  rw [Int.zero_ediv]
  rfl

/-! ### Bitwise distribution -/

theorem land_land_m (a b m : Int) :
    Z_land (Z_land a b) m = Z_land (Z_land a m) (Z_land b m) := by
  apply Z_bits_inj
  intro n
  simp only [Z_testbit_land]
  cases Z_testbit a n <;> cases Z_testbit b n <;> cases Z_testbit m n <;> rfl

theorem land_lxor_m (a b m : Int) :
    Z_land (Z_lxor a b) m = Z_lxor (Z_land a m) (Z_land b m) := by
  apply Z_bits_inj
  intro n
  simp only [Z_testbit_land, Z_testbit_lxor]
  cases Z_testbit a n <;> cases Z_testbit b n <;> cases Z_testbit m n <;> rfl

theorem lxor_lt64 (a b : Int) (ha : 0 ≤ a ∧ a < 2 ^ 64) (hb : 0 ≤ b ∧ b < 2 ^ 64) :
    0 ≤ Z_lxor a b ∧ Z_lxor a b < 2 ^ 64 := by
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha.1
  obtain ⟨b', rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  have ha' : a' < 2 ^ 64 := by omega
  have hb' : b' < 2 ^ 64 := by omega
  have hx := Nat.xor_lt_two_pow ha' hb'
  show 0 ≤ ((a' ^^^ b' : Nat) : Int) ∧ ((a' ^^^ b' : Nat) : Int) < 2 ^ 64
  omega

theorem zb_alt (x : Int) (i : Nat) : zb x i = Z_land (x >>> (8 * i)) 255 := by
  rw [Z_land_255, Int.shiftRight_eq_div_pow]
  rfl

theorem zb_land (u w : Int) (i : Nat) : zb (Z_land u w) i = Z_land (zb u i) (zb w i) := by
  rw [zb_alt, zb_alt, zb_alt, Z_shiftr_land, land_land_m]

theorem zb_lxor (u w : Int) (i : Nat) : zb (Z_lxor u w) i = Z_lxor (zb u i) (zb w i) := by
  rw [zb_alt, zb_alt, zb_alt, Z_shiftr_lxor, land_lxor_m]

/-! ### Digit reconstruction -/

theorem zdig_nonneg (ds : List Int) (h : ∀ d ∈ ds, 0 ≤ d ∧ d < 256) : 0 ≤ zdig ds := by
  induction ds with
  | nil => exact Int.le_refl 0
  | cons d ds ih =>
    have hd := h d (List.mem_cons.2 (Or.inl rfl))
    have ih' := ih fun x hx => h x (List.mem_cons.2 (Or.inr hx))
    show 0 ≤ d + 256 * zdig ds
    omega

theorem zdig_lt (ds : List Int) (h : ∀ d ∈ ds, 0 ≤ d ∧ d < 256) :
    zdig ds < 2 ^ (8 * ds.length) := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    have hd := h d (List.mem_cons.2 (Or.inl rfl))
    have hds : ∀ x ∈ ds, 0 ≤ x ∧ x < 256 := fun x hx => h x (List.mem_cons.2 (Or.inr hx))
    have ih' := ih hds
    have hn := zdig_nonneg ds hds
    show d + 256 * zdig ds < 2 ^ (8 * (ds.length + 1))
    rw [show 8 * (ds.length + 1) = 8 + 8 * ds.length by omega, Int.pow_add,
      show (2 : Int) ^ 8 = 256 by decide]
    omega

/-- Lean-only helper: dividing by `2 ^ (8 * (i + 1))` is dividing by `256`,
then by `2 ^ (8 * i)` (the `Z.pow_add_r` and `Z.div_div` steps Rocq's
`zb_zdig` takes inline). -/
theorem div_pow8_succ (x : Int) (i : Nat) : x / 2 ^ (8 * (i + 1)) = x / 256 / 2 ^ (8 * i) := by
  rw [show 8 * (i + 1) = 8 + 8 * i by omega, Int.pow_add, show (2 : Int) ^ 8 = 256 by decide,
    Int.ediv_ediv_of_nonneg (by decide : (0 : Int) ≤ 256)]

/-- Lean-only helper: one step of the digit expansion — the quotient at byte
`k` is byte `k` plus 256 times the quotient at byte `k + 1`. -/
theorem zb_step (x : Int) (k : Nat) :
    x / 2 ^ (8 * k) = zb x k + 256 * (x / 2 ^ (8 * (k + 1))) := by
  rw [show 8 * (k + 1) = 8 * k + 8 by omega, Int.pow_add, show (2 : Int) ^ 8 = 256 by decide,
    ← Int.ediv_ediv_of_nonneg (Int.le_of_lt (pow2_8i_pos k))]
  unfold zb
  omega

theorem zb_zdig (ds : List Int) (h : ∀ d ∈ ds, 0 ≤ d ∧ d < 256) (i : Nat)
    (hi : i < ds.length) : zb (zdig ds) i = ds.getD i 0 := by
  induction ds generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons d ds ih =>
    have hd := h d (List.mem_cons.2 (Or.inl rfl))
    have hds : ∀ x ∈ ds, 0 ≤ x ∧ x < 256 := fun x hx => h x (List.mem_cons.2 (Or.inr hx))
    have hnn := zdig_nonneg ds hds
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      show (d + 256 * zdig ds) / 2 ^ 0 % 256 = d
      rw [Int.pow_zero, Int.ediv_one]
      omega
    | succ i =>
      have hi' : i < ds.length := by
        simp only [List.length_cons] at hi
        omega
      rw [List.getD_cons_succ, ← ih hds i hi']
      show (d + 256 * zdig ds) / 2 ^ (8 * (i + 1)) % 256 = zdig ds / 2 ^ (8 * i) % 256
      have hq : (d + 256 * zdig ds) / 256 = zdig ds := by omega
      rw [div_pow8_succ, hq]

/-- A 64-bit value equals the digit expansion of its 8 bytes. -/
theorem zdig_recon8 (x : Int) (hx : 0 ≤ x ∧ x < 2 ^ 64) :
    x = zdig [zb x 0, zb x 1, zb x 2, zb x 3, zb x 4, zb x 5, zb x 6, zb x 7] := by
  have e0 : x / 2 ^ 0 = zb x 0 + 256 * (x / 2 ^ 8) := zb_step x 0
  have e1 : x / 2 ^ 8 = zb x 1 + 256 * (x / 2 ^ 16) := zb_step x 1
  have e2 : x / 2 ^ 16 = zb x 2 + 256 * (x / 2 ^ 24) := zb_step x 2
  have e3 : x / 2 ^ 24 = zb x 3 + 256 * (x / 2 ^ 32) := zb_step x 3
  have e4 : x / 2 ^ 32 = zb x 4 + 256 * (x / 2 ^ 40) := zb_step x 4
  have e5 : x / 2 ^ 40 = zb x 5 + 256 * (x / 2 ^ 48) := zb_step x 5
  have e6 : x / 2 ^ 48 = zb x 6 + 256 * (x / 2 ^ 56) := zb_step x 6
  have e7 : x / 2 ^ 56 = zb x 7 + 256 * (x / 2 ^ 64) := zb_step x 7
  have hbot : x / 2 ^ 0 = x := by rw [Int.pow_zero, Int.ediv_one]
  have htop : x / 2 ^ 64 = 0 := Int.ediv_eq_zero_of_lt hx.1 hx.2
  simp only [zdig]
  omega

theorem zb_eq0 (x : Int) (hx : 0 ≤ x ∧ x < 2 ^ 64) (h : ∀ i : Nat, i < 8 → zb x i = 0) :
    x = 0 := by
  have hr := zdig_recon8 x hx
  simp only [zdig] at hr
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h6 := h 6 (by decide)
  have h7 := h 7 (by decide)
  omega

theorem zb_neq0 (x : Int) (i : Nat) (h : zb x i ≠ 0) : x ≠ 0 := by
  intro hc
  subst hc
  exact h (zb_0 i)

/-! ### Byte split -/

theorem zb_split (lo hi : Int) (i : Nat) (hlo : 0 ≤ lo ∧ lo < 2 ^ (8 * i)) (_hhi : 0 ≤ hi) :
    zb (lo + 2 ^ (8 * i) * hi) i = hi % 256 := by
  have hp := pow2_8i_pos i
  unfold zb
  rw [Int.add_mul_ediv_left lo hi (by omega), Int.ediv_eq_zero_of_lt hlo.1 hlo.2, Int.zero_add]

theorem zb_mod64 (y : Int) (i : Nat) (hi : i < 8) (hy : 0 ≤ y ∧ y < 2 ^ 65) :
    zb (y % 2 ^ 64) i = zb y i := by
  by_cases hlt : y < 2 ^ 64
  · rw [Int.emod_eq_of_lt hy.1 hlt]
  · have hm : y % 2 ^ 64 = y + 2 ^ (8 * i) * (-(256 * 2 ^ (56 - 8 * i))) := by
      have hd : (2 : Int) ^ 64 = 2 ^ (8 * i) * (256 * 2 ^ (56 - 8 * i)) := by
        rw [show (256 : Int) = 2 ^ 8 by decide, ← Int.pow_add, ← Int.pow_add,
          show 8 * i + (8 + (56 - 8 * i)) = 64 by omega]
      rw [Int.mul_neg, ← hd]
      omega
    have hp := pow2_8i_pos i
    unfold zb
    rw [hm, Int.add_mul_ediv_left y _ (by omega)]
    omega

/-! ### The musl has-zero-byte test -/

/-- 0xFEFEFEFEFEFEFEFF -/
def ONESNEG : Int := 18374403900871474943

/-- 0x8080808080808080 -/
def HIGHS : Int := 9259542123273814144

/-- 2^64 - 1 -/
def ALLONES : Int := 18446744073709551615

def Tz (x : Int) : Int :=
  Z_land (Z_land ((x + ONESNEG) % 2 ^ 64) (Z_lxor x ALLONES)) HIGHS

theorem land_le_r (a b : Int) (hb : 0 ≤ b) : Z_land a b ≤ b := by
  obtain ⟨b', rfl⟩ := Int.eq_ofNat_of_zero_le hb
  cases a with
  | ofNat a =>
    have h := @Nat.and_le_right a b'
    show ((a &&& b' : Nat) : Int) ≤ (b' : Int)
    omega
  | negSucc a =>
    show ((b' - (b' &&& a) : Nat) : Int) ≤ (b' : Int)
    omega

theorem land_le_l (a b : Int) (ha : 0 ≤ a) : Z_land a b ≤ a := by
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha
  cases b with
  | ofNat b =>
    have h := @Nat.and_le_left a' b
    show ((a' &&& b : Nat) : Int) ≤ (a' : Int)
    omega
  | negSucc b =>
    show ((a' - (a' &&& b) : Nat) : Int) ≤ (a' : Int)
    omega

theorem Tz_range (x : Int) : 0 ≤ Tz x ∧ Tz x < 2 ^ 64 := by
  have hH : 0 ≤ HIGHS ∧ HIGHS < 2 ^ 64 := by
    unfold HIGHS
    omega
  have h1 := Z_land_nonneg_r (Z_land ((x + ONESNEG) % 2 ^ 64) (Z_lxor x ALLONES)) HIGHS hH.1
  have h2 := land_le_r (Z_land ((x + ONESNEG) % 2 ^ 64) (Z_lxor x ALLONES)) HIGHS hH.1
  unfold Tz
  omega

theorem zb_ALLONES (i : Nat) (hi : i < 8) : zb ALLONES i = 255 := by
  rw [zb_alt]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem zb_HIGHS (i : Nat) (hi : i < 8) : zb HIGHS i = 128 := by
  rw [zb_alt]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Tz_byte (x : Int) (i : Nat) (hi : i < 8) :
    zb (Tz x) i =
      Z_land (Z_land (zb ((x + ONESNEG) % 2 ^ 64) i) (Z_lxor (zb x i) 255)) 128 := by
  unfold Tz
  rw [zb_land, zb_land, zb_lxor, zb_ALLONES i hi, zb_HIGHS i hi]

/-- The 8-bit fact behind the trick, checked by evaluation over all 255
nonzero byte values. -/
theorem byte_nozero (c : Int) (hc : 1 ≤ c ∧ c ≤ 255) :
    Z_land (Z_land (c - 1) (Z_lxor c 255)) 128 = 0 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ c)
  have hall : ∀ m : Nat, m < 256 → 1 ≤ m →
      Z_land (Z_land ((m : Int) - 1) (Z_lxor (m : Int) 255)) 128 = 0 := by
    decide +kernel
  exact hall n (by omega) (by omega)

/-- No zero byte: the test word is 0, so the loop keeps going. -/
theorem Tz_nozero (x : Int) (hx : 0 ≤ x ∧ x < 2 ^ 64) (hnz : ∀ i : Nat, i < 8 → zb x i ≠ 0) :
    Tz x = 0 := by
  have b0 := zb_bound x 0
  have b1 := zb_bound x 1
  have b2 := zb_bound x 2
  have b3 := zb_bound x 3
  have b4 := zb_bound x 4
  have b5 := zb_bound x 5
  have b6 := zb_bound x 6
  have b7 := zb_bound x 7
  have n0 := hnz 0 (by decide)
  have n1 := hnz 1 (by decide)
  have n2 := hnz 2 (by decide)
  have n3 := hnz 3 (by decide)
  have n4 := hnz 4 (by decide)
  have n5 := hnz 5 (by decide)
  have n6 := hnz 6 (by decide)
  have n7 := hnz 7 (by decide)
  have hrec := zdig_recon8 x hx
  simp only [zdig] at hrec
  have hds : ∀ d ∈ [zb x 0 - 1, zb x 1 - 1, zb x 2 - 1, zb x 3 - 1, zb x 4 - 1, zb x 5 - 1,
      zb x 6 - 1, zb x 7 - 1], 0 ≤ d ∧ d < 256 := by
    intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hy : (x + ONESNEG) % 2 ^ 64 =
      zdig [zb x 0 - 1, zb x 1 - 1, zb x 2 - 1, zb x 3 - 1, zb x 4 - 1, zb x 5 - 1,
        zb x 6 - 1, zb x 7 - 1] := by
    simp only [zdig]
    unfold ONESNEG
    omega
  apply zb_eq0 (Tz x) (Tz_range x)
  intro i hi
  rw [Tz_byte x i hi, hy, zb_zdig _ hds i (by simp only [List.length_cons, List.length_nil]; omega)]
  have hget : [zb x 0 - 1, zb x 1 - 1, zb x 2 - 1, zb x 3 - 1, zb x 4 - 1, zb x 5 - 1,
      zb x 6 - 1, zb x 7 - 1].getD i 0 = zb x i - 1 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hget]
  have hb := zb_bound x i
  have hn := hnz i hi
  exact byte_nozero (zb x i) ⟨by omega, by omega⟩

theorem zb_split_255 (v lo Q : Int) (i : Nat) (p : Int) (hp : p = 2 ^ (8 * i))
    (hv : v = lo + p * (255 + 256 * Q)) (hlo : 0 ≤ lo ∧ lo < p) (hQ : 0 ≤ Q) :
    zb v i = 255 := by
  subst hp
  subst hv
  rw [zb_split lo (255 + 256 * Q) i hlo (by omega)]
  omega

/-- Byte `i` of `x + ONESNEG` is 0xff when byte `i` of `x` is the first
zero byte: the borrow chain runs up from byte 0 and stops there. -/
theorem sum_byte_255 (x : Int) (i : Nat) (hx : 0 ≤ x ∧ x < 2 ^ 64) (hi : i < 8)
    (hz : zb x i = 0) (hlow : ∀ j : Nat, j < i → zb x j ≠ 0) :
    zb (x + ONESNEG) i = 255 := by
  have b0 := zb_bound x 0
  have b1 := zb_bound x 1
  have b2 := zb_bound x 2
  have b3 := zb_bound x 3
  have b4 := zb_bound x 4
  have b5 := zb_bound x 5
  have b6 := zb_bound x 6
  have b7 := zb_bound x 7
  have hrec := zdig_recon8 x hx
  simp only [zdig] at hrec
  unfold ONESNEG
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- byte 0
    exact zb_split_255 _ 0
      (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296
        + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0 1
      (by decide) (by omega) (by omega) (by omega)
  · -- byte 1
    have l0 := hlow 0 (by decide)
    exact zb_split_255 _ ((zb x 0 - 1) * 1)
      (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296
        + zb x 7 * 1099511627776 + 280371153272574) 1 256
      (by decide) (by omega) (by omega) (by omega)
  · -- byte 2
    have l0 := hlow 0 (by decide)
    have l1 := hlow 1 (by decide)
    exact zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256)
      (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296
        + 1095199817470) 2 65536
      (by decide) (by omega) (by omega) (by omega)
  · -- byte 3
    have l0 := hlow 0 (by decide)
    have l1 := hlow 1 (by decide)
    have l2 := hlow 2 (by decide)
    exact zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536)
      (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3 16777216
      (by decide) (by omega) (by omega) (by omega)
  · -- byte 4
    have l0 := hlow 0 (by decide)
    have l1 := hlow 1 (by decide)
    have l2 := hlow 2 (by decide)
    have l3 := hlow 3 (by decide)
    exact zb_split_255 _
      ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216)
      (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4 4294967296
      (by decide) (by omega) (by omega) (by omega)
  · -- byte 5
    have l0 := hlow 0 (by decide)
    have l1 := hlow 1 (by decide)
    have l2 := hlow 2 (by decide)
    have l3 := hlow 3 (by decide)
    have l4 := hlow 4 (by decide)
    exact zb_split_255 _
      ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216
        + (zb x 4 - 1) * 4294967296)
      (zb x 6 * 1 + zb x 7 * 256 + 65278) 5 1099511627776
      (by decide) (by omega) (by omega) (by omega)
  · -- byte 6
    have l0 := hlow 0 (by decide)
    have l1 := hlow 1 (by decide)
    have l2 := hlow 2 (by decide)
    have l3 := hlow 3 (by decide)
    have l4 := hlow 4 (by decide)
    have l5 := hlow 5 (by decide)
    exact zb_split_255 _
      ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216
        + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776)
      (zb x 7 * 1 + 254) 6 281474976710656
      (by decide) (by omega) (by omega) (by omega)
  · -- byte 7
    have l0 := hlow 0 (by decide)
    have l1 := hlow 1 (by decide)
    have l2 := hlow 2 (by decide)
    have l3 := hlow 3 (by decide)
    have l4 := hlow 4 (by decide)
    have l5 := hlow 5 (by decide)
    have l6 := hlow 6 (by decide)
    exact zb_split_255 _
      ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216
        + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776
        + (zb x 6 - 1) * 281474976710656)
      0 7 72057594037927936
      (by decide) (by omega) (by omega) (by omega)

/-- A zero byte: the test word is nonzero, so the loop stops. -/
theorem Tz_haszero (x : Int) (i : Nat) (hx : 0 ≤ x ∧ x < 2 ^ 64) (hi : i < 8)
    (hz : zb x i = 0) (hlow : ∀ j : Nat, j < i → zb x j ≠ 0) : Tz x ≠ 0 := by
  apply zb_neq0 _ i
  rw [Tz_byte x i hi, zb_mod64 (x + ONESNEG) i hi (by unfold ONESNEG; omega),
    sum_byte_255 x i hx hi hz hlow, hz]
  decide

end HZ

/-! ## Bridge: the bytes an 8-byte load returns are the bytes of the value -/

theorem u8_zero : bv_unsigned (Z_to_bv 8 0) = 0 := by
  decide

theorem lor_shiftl8 (a y : Int) (ha : 0 ≤ a ∧ a < 256) (hy : 0 ≤ y) :
    Z_lor a (Z_shiftl y 8) = a + 256 * y := by
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha.1
  obtain ⟨y', rfl⟩ := Int.eq_ofNat_of_zero_le hy
  have ha' : a' < 2 ^ 8 := by omega
  show ((a' ||| (y' <<< 8) : Nat) : Int) = (a' : Int) + 256 * (y' : Int)
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha', Nat.shiftLeft_eq]
  omega

/-- Lean-only helper: every digit of a byte list read as `Int`s is a byte
(the `Forall_map` step Rocq's bridge lemmas take inline). -/
theorem map_u8_range (bs : List byte) : ∀ d ∈ bs.map bv_unsigned, 0 ≤ d ∧ d < 256 := by
  intro d hd
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hd
  exact u8_range b

theorem bytes_le_to_Z_zdig (bs : List byte) :
    bytes_le_to_Z bs = HZ.zdig (bs.map bv_unsigned) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Z_lor (bv_unsigned b) (Z_shiftl (bytes_le_to_Z bs) 8) =
      bv_unsigned b + 256 * HZ.zdig (bs.map bv_unsigned)
    rw [ih]
    exact lor_shiftl8 _ _ (u8_range b) (HZ.zdig_nonneg _ (map_u8_range bs))

theorem zb_of_bytes (bs : List byte) (i : Nat) (hi : i < bs.length) :
    HZ.zb (bytes_le_to_Z bs) i = bv_unsigned (bs.getD i (Z_to_bv 8 0)) := by
  rw [bytes_le_to_Z_zdig, HZ.zb_zdig _ (map_u8_range bs) i (by rw [List.length_map]; exact hi),
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, Option.getD_some]

theorem bytes_le_to_Z_range (bs : List byte) (hl : bs.length = 8) :
    0 ≤ bytes_le_to_Z bs ∧ bytes_le_to_Z bs < 2 ^ 64 := by
  have h := bytes_le_to_Z_bound bs
  rw [hl] at h
  exact ⟨bytes_le_to_Z_nonneg bs, h⟩

/-- The machine's test word, as the `Int` function `HZ.Tz`. -/
theorem v_haszero (v : word) :
    bv_unsigned
        (v_and (v_and (v_add v (Z_to_bv 64 18374403900871474943)) (v_xori v (-1)))
          (Z_to_bv 64 9259542123273814144)) =
      HZ.Tz (bv_unsigned v) := by
  have hv := u64_range v
  have hc1 : bv_unsigned (Z_to_bv 64 18374403900871474943) = 18374403900871474943 :=
    u_Z2bv _ (by omega) (by omega)
  have hc2 : bv_unsigned (Z_to_bv 64 9259542123273814144) = 9259542123273814144 :=
    u_Z2bv _ (by omega) (by omega)
  have hm1 : bv_wrap 64 (-1) = 18446744073709551615 := by
    rw [bv_wrap64_mod]
    omega
  have hx := HZ.lxor_lt64 (bv_unsigned v) 18446744073709551615 hv (by omega)
  have hm : 0 ≤ (bv_unsigned v + 18374403900871474943) % 2 ^ 64 ∧
      (bv_unsigned v + 18374403900871474943) % 2 ^ 64 < 2 ^ 64 := by
    omega
  have hz0 := Z_land_nonneg_l ((bv_unsigned v + 18374403900871474943) % 2 ^ 64)
    (Z_lxor (bv_unsigned v) 18446744073709551615) hm.1
  have hz1 := HZ.land_le_l ((bv_unsigned v + 18374403900871474943) % 2 ^ 64)
    (Z_lxor (bv_unsigned v) 18446744073709551615) hm.1
  have hh0 := Z_land_nonneg_r (Z_land ((bv_unsigned v + 18374403900871474943) % 2 ^ 64)
    (Z_lxor (bv_unsigned v) 18446744073709551615)) 9259542123273814144 (by omega)
  have hh1 := HZ.land_le_r (Z_land ((bv_unsigned v + 18374403900871474943) % 2 ^ 64)
    (Z_lxor (bv_unsigned v) 18446744073709551615)) 9259542123273814144 (by omega)
  unfold v_and v_add v_xori HZ.Tz HZ.ONESNEG HZ.HIGHS HZ.ALLONES
  rw [hc1, hc2, hm1, Z_to_bv_unsigned 64 (bv_unsigned v + 18374403900871474943), bv_wrap64_mod,
    u_Z2bv (Z_lxor (bv_unsigned v) 18446744073709551615) hx.1 hx.2,
    u_Z2bv _ hz0 (by omega), u_Z2bv _ hh0 (by omega)]

/-! ## An 8-byte load anywhere inside an argv string

musl's `strlen` reads a whole aligned word, so the load can straddle the
NUL terminator.  `build_stack_bytes` puts the pad and the 16 AT_RANDOM bytes
after the string blob, so at least 16 readable bytes follow the last argv
string's NUL: `bsb_len_lower` states that bound on the image length, and
`read_word_stack` turns it into a whole 8-byte read.  See the over-read
warning in the Rocq file's header, and the caveat on it in this file's
header. -/

theorem total_arg_bytes_firstn_S (l : List (List byte)) (k : Nat) (hk : k < l.length) :
    total_arg_bytes_nat (l.take (k + 1)) =
      total_arg_bytes_nat (l.take k) + (l.getD k []).length + 1 := by
  induction l generalizing k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons s rest ih =>
    cases k with
    | zero =>
      simp only [List.take_succ_cons, List.take_zero, List.getD_cons_zero, total_arg_bytes_cons]
      omega
    | succ k =>
      have hk' : k < rest.length := by
        simp only [List.length_cons] at hk
        omega
      simp only [List.take_succ_cons, total_arg_bytes_cons, List.getD_cons_succ]
      rw [ih k hk']
      omega

theorem bsb_len_lower (ph : PhdrInfo) (sp : word) (a e : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) :
    cat_struct_size a e + total_arg_bytes_nat a + 16 ≤
      (build_stack_bytes ph sp a e uid hw rnd).length := by
  unfold build_stack_bytes cat_struct_size
  dsimp only
  rw [string_addrs_pair a]
  dsimp only
  rw [string_addrs_pair e]
  dsimp only
  simp only [List.length_append, List.length_replicate, length_flat_map_le8,
    length_string_addrs_fst, length_n_to_le_8, length_auxv_bytes, length_flatten_strings,
    length_at_random_bytes]
  omega

/-- `build_stack_bytes` split just before byte `m` of argv string `k`,
with at least 8 readable bytes left. -/
theorem bsb_word_k (ph : PhdrInfo) (sp : word) (a e : List (List byte)) (k m : Nat)
    (uid hw : word) (rnd : EntryDraw) (hk : k < a.length) (hm : m ≤ (a.getD k []).length) :
    ∃ pre post, build_stack_bytes ph sp a e uid hw rnd = pre ++ post ∧
      pre.length = cat_struct_size a e + total_arg_bytes_nat (a.take k) + m ∧
      8 ≤ post.length := by
  obtain ⟨pre0, post0, E, hlen0⟩ := bsb_byte_k ph sp a e k uid hw rnd hk
  have hlow := bsb_len_lower ph sp a e uid hw rnd
  have hmono := total_arg_bytes_firstn_le (k + 1) a
  have hstep := total_arg_bytes_firstn_S a k hk
  have hs1 : (a.getD k [] ++ [Z_to_bv 8 0]).length = (a.getD k []).length + 1 := by
    rw [List.length_append, List.length_singleton]
  generalize a.getD k [] ++ [Z_to_bv 8 0] = s1 at E hs1
  have hl : (build_stack_bytes ph sp a e uid hw rnd).length =
      pre0.length + s1.length + post0.length := by
    rw [E, List.length_append, List.length_append]
    omega
  have htake : (s1.take m).length = m := List.length_take_of_le (by omega)
  refine ⟨pre0 ++ s1.take m, s1.drop m ++ post0, ?_, ?_, ?_⟩
  · rw [E, List.append_assoc, ← List.append_assoc (s1.take m), List.take_append_drop]
  · rw [List.length_append, hlen0, htake]
  · rw [List.length_append, List.length_drop]
    omega

theorem read_word_stack (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (a e : List (List byte)) (k m : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < a.length) (hm : m ≤ (a.getD k []).length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp a e uid hw rnd).length : Int) < 2 ^ 64) :
    ∃ bs : List byte, bs.length = 8 ∧
      rdn segs (stack_to_mem sp (entry_stack_image ph sp a e uid hw rnd))
          (cat_argv_ptr sp a e k + nat_to_word m) 8 = some bs := by
  obtain ⟨pre, post, E, hlen, hpost⟩ := bsb_word_k ph sp a e k m uid hw rnd hk hm
  have htake : (post.take 8).length = 8 := List.length_take_of_le hpost
  refine ⟨post.take 8, htake, ?_⟩
  have haddr : cat_argv_ptr sp a e k + nat_to_word m = sp + nat_to_word pre.length := by
    rw [hlen, cat_argv_ptr_offset sp a e k hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge, nat_to_word_add_merge, Nat.add_assoc]
  rw [haddr]
  exact read_at_offset_image segs ph sp a e uid hw rnd pre (post.take 8) (post.drop 8) 8
    (by rw [List.take_append_drop]; exact E) htake hnw

/-- The bytes an 8-byte load returned, as far as the NUL: given ANY memory
whose single-byte reads along the string agree with `byte_at s`, byte `j`
of the loaded word is `byte_at s (m + j)`.  Stated over an abstract `mem`
and a byte-read hypothesis so an example can feed it its own
overlay-relative read lemma. -/
theorem word_bytes_nth (segs : List Segment) (mem : word → Option byte) (ptr : word)
    (s : List byte) (m : Nat) (bs : List byte) (j : Nat)
    (hr : rdn segs mem (ptr + nat_to_word m) 8 = some bs)
    (hb : ∀ i : Nat, i ≤ s.length → rdn segs mem (ptr + nat_to_word i) 1 = some [byte_at s i])
    (hj : j < 8) (hmj : m + j ≤ s.length) :
    bs.getD j (Z_to_bv 8 0) = byte_at s (m + j) := by
  have h1 := rdn_nth segs mem 8 _ bs j hr hj
  rw [nat_to_word_add_merge, hb (m + j) hmj] at h1
  exact ((List.cons.inj (Option.some.inj h1)).1).symm

/-! ## Section `ArgvWord`: readability of the strlen word load over `wrap_mem`

The Rocq section is over `(segs, ph, sp, av, ev, uid, hw, rnd)` and the four
ambient startup hypotheses, the shape of `Common/ArgvEnv`, so a per-binary
file instantiates each lemma in one step.  `rnd` is the run's entry draw,
whose `ed_random` half is laid out as the last 16 bytes of
`build_stack_bytes`.  The over-read argument needs only that a word load
past an argv NUL stays inside the image, whatever those bytes hold, so no
lemma here constrains `rnd`. -/

/-- sp-window bounds as raw hex (library copies of the per-example Rocq
lemmas `rsp_lo_num`/`rsp_hi_num`; the `mstr_` prefix keeps them apart from
`ArgvEnv`'s `sp_lo_num`/`sp_hi_num` in a file that opens both
namespaces). -/
theorem mstr_sp_lo (sp : word) (hsp_lo : sp_window_lo ≤ bv_unsigned sp) :
    0x7fff80000000 ≤ bv_unsigned sp :=
  hsp_lo

theorem mstr_sp_hi (sp : word) (hsp_hi : bv_unsigned sp ≤ sp_window_hi) :
    bv_unsigned sp ≤ 0x800000000000 :=
  hsp_hi

theorem mstr_bsb_nw (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_hi : bv_unsigned sp ≤ sp_window_hi) :
    bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 := by
  have h1 := bsb_bound ph sp av ev uid hw rnd hva hve
  have h2 := mstr_sp_hi sp hsp_hi
  omega

/-- Room for a whole word past ANY offset inside argv string `k`: the stack
image keeps at least 16 more bytes after the last argv string's NUL (the
envp strings, the pad and the 16 AT_RANDOM bytes follow it).  This is the
quantitative form of the over-read soundness argument. -/
theorem argv_ptr_room (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_lo : sp_window_lo ≤ bv_unsigned sp) (hsp_hi : bv_unsigned sp ≤ sp_window_hi)
    (k : Nat) (hk : k < av.length) :
    bv_unsigned (cat_argv_ptr sp av ev k) + ((av.getD k []).length : Int) + 17 ≤
      bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) := by
  have h1 := mstr_sp_lo sp hsp_lo
  have h2 := mstr_sp_hi sp hsp_hi
  have hnw := mstr_bsb_nw ph sp av ev uid hw rnd hva hve hsp_hi
  have hlow := bsb_len_lower ph sp av ev uid hw rnd
  have hmono := total_arg_bytes_firstn_le (k + 1) av
  have hstep := total_arg_bytes_firstn_S av k hk
  have hptr : cat_argv_ptr sp av ev k =
      sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) := by
    rw [cat_argv_ptr_offset sp av ev k hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge]
  rw [hptr, word_add_nat, u_Z2bv _ (by omega) (by omega)]
  omega

/-- Address bounds for the `k`-th argv pointer (the statement of
`ArgvEnv.argv_ptr_bounds_at` and of `source_ptr_bounds` in the Rocq
`grep_args_ns` and `alloc_join_ns` sources; restated here so this file
does not import `ArgvEnv`). -/
theorem mstr_argv_ptr_bounds (sp : word) (av ev : List (List byte)) (hva : valid_argv av)
    (hve : valid_envp ev) (hsp_hi : bv_unsigned sp ≤ sp_window_hi) (k : Nat)
    (hk : k < av.length) :
    bv_unsigned sp ≤ bv_unsigned (cat_argv_ptr sp av ev k) ∧
      bv_unsigned (cat_argv_ptr sp av ev k) + ((av.getD k []).length : Int) + 1 < 2 ^ 64 := by
  apply argv_ptr_bounds sp av ev k hva hve hk
  have h1 := mstr_sp_hi sp hsp_hi
  unfold argv_layout_slack
  omega

/-- THE load-bearing readability fact: an 8-byte load at ANY offset `m`
within argv string `k` (including `m = (av.getD k []).length`, i.e.
starting at the NUL) is total over the initial wrapped memory.  An
example lifts this to its own overlay by peeling the overlay down to
`wrap_mem` first (see the Rocq `grep_args_ns` source's `read_word_m`). -/
theorem argv_word_readable (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw) (hva : valid_argv av)
    (hve : valid_envp ev) (hsp_lo : sp_window_lo ≤ bv_unsigned sp)
    (hsp_hi : bv_unsigned sp ≤ sp_window_hi) (k m : Nat) (hk : k < av.length)
    (hm : m ≤ (av.getD k []).length) :
    ∃ bs : List byte, bs.length = 8 ∧
      rdn segs (wrap_mem ph sp av ev uid hw rnd) (cat_argv_ptr sp av ev k + nat_to_word m) 8 =
        some bs := by
  have h1 := mstr_sp_lo sp hsp_lo
  have h2 := mstr_sp_hi sp hsp_hi
  obtain ⟨hge, hup⟩ := mstr_argv_ptr_bounds sp av ev hva hve hsp_hi k hk
  have hroom := argv_ptr_room ph sp av ev uid hw rnd hva hve hsp_lo hsp_hi k hk
  have hnw := mstr_bsb_nw ph sp av ev uid hw rnd hva hve hsp_hi
  have hr := u64_range (cat_argv_ptr sp av ev k)
  have hu : bv_unsigned (cat_argv_ptr sp av ev k + nat_to_word m) =
      bv_unsigned (cat_argv_ptr sp av ev k) + (m : Int) := by
    rw [word_add_nat]
    exact u_Z2bv _ (by omega) (by omega)
  obtain ⟨bs, hl, hrd⟩ := read_word_stack ph segs sp av ev k m uid hw rnd hk hm hnw
  refine ⟨bs, hl, ?_⟩
  rw [rdn_wrap_stack_above segs ph sp av ev (cat_argv_ptr sp av ev k + nat_to_word m) 8 uid hw rnd
    (by rw [hu]; omega) (by rw [hu]; omega)]
  exact hrd

end LinuxProcessSemantics.Common.MuslStrlen
