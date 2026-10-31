import LinuxProcessSemantics.Riscv.Prelude

/-! # LinuxProcessSem.BvBase — shared bitvector helpers for the spec layer

Mirrors `theories/LinuxProcessSem/BvBase.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

Bitvector representation follows two rules:

- machine QUANTITIES (register values, addresses, syscall args and
  returns, fds, channel ids, sizes, offsets, exit codes) are
  `word = BitVec 64`; memory/file/event BYTES are `byte = BitVec 8`;
- RANGE and DISJOINTNESS arithmetic is done in `Int` over `bv_unsigned`
  (no wrap-around), so bound checks keep a precise meaning.  Only data
  that lands back in registers or memory is re-wrapped with `Z_to_bv`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.BvBase

open LinuxProcessSemantics.Riscv.Prelude

abbrev byte := BitVec 8

/-- Unsigned `<=` as a boolean (unsigned `<` is `bv_ltu`). -/
def bv_leu {n : Nat} (a b : BitVec n) : Bool := a.ule b

/-- List length as a 64-bit word (all modeled lengths are far below 2^64,
so this never wraps). -/
def len_word {A : Type} (l : List A) : word := Z_to_bv 64 (l.length : Int)

/-- Word/nat bridges for list indexing and fuel. -/
def word_to_nat (w : word) : Nat := w.toNat
def nat_to_word (n : Nat) : word := Z_to_bv 64 (n : Int)

/-- `Nat.min (word_to_nat w) bound`, spelled the way Rocq's extraction
needs it. -/
def word_to_nat_bounded (w : word) (bound : Nat) : Nat :=
  if bv_unsigned w ≤ (bound : Int) then word_to_nat w else bound

theorem word_to_nat_bounded_eq_min (w : word) (bound : Nat) :
    word_to_nat_bounded w bound = Nat.min (word_to_nat w) bound := by
  unfold word_to_nat_bounded word_to_nat bv_unsigned
  by_cases h : ((w.toNat : Int)) ≤ (bound : Int)
  · have h' : w.toNat ≤ bound := by exact_mod_cast h
    simp [h, Nat.min_eq_left h']
  · have h' : bound ≤ w.toNat := by
      have : ¬ (w.toNat ≤ bound) := fun hh => h (by exact_mod_cast hh)
      omega
    simp [h, Nat.min_eq_right h']

/-- The `Z_to_bv` round trip is the identity on `[0, 2^64)` — stdpp's
`Z_to_bv_unsigned` followed by `bv_wrap_small`, the pair the Rocq proofs of
`State.rw_count_clamp_word` and `State.iovs_total_cap_aux` rewrite with,
stated once here where every file can reach it (`Sys/Uapi/Fs.lean`'s note
on `stat_set_size_size_ok` names this file as the home of the round trip). -/
theorem bv_unsigned_Z_to_bv_small (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  have hlt : z.toNat < 2 ^ 64 := by omega
  unfold bv_unsigned Z_to_bv
  rw [← Int.toNat_of_nonneg h0, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt]

/-! ## Little-endian byte (de)composition -/

/-- The 8 little-endian bytes of a 64-bit word (index 0 = least
significant). -/
def word_le8 (v : word) : List byte :=
  [ bv_extract 0 8 v, bv_extract 8 8 v, bv_extract 16 8 v,
    bv_extract 24 8 v, bv_extract 32 8 v, bv_extract 40 8 v,
    bv_extract 48 8 v, bv_extract 56 8 v ]

/-- Little-endian assembly (`++` puts its FIRST argument in the high bits,
as `bv_concat` does). -/
def le2 (b1 b0 : byte) : BitVec 16 := b1 ++ b0
def le4 (b3 b2 b1 b0 : byte) : BitVec 32 := le2 b3 b2 ++ le2 b1 b0
def le8 (b7 b6 b5 b4 b3 b2 b1 b0 : byte) : word :=
  le4 b7 b6 b5 b4 ++ le4 b3 b2 b1 b0

/-- The value of a little-endian byte list, as an EXACT non-negative
integer: it walks the whole list and truncates nothing.  Rocq computes it
with `Z.lor`/`Z.shiftl`; the operands are non-negative, so `Nat`'s
operations give the same value. -/
def bytes_le_to_nat (bs : List byte) : Nat :=
  match bs with
  | [] => 0
  | b :: rest => b.toNat ||| (bytes_le_to_nat rest <<< 8)

def bytes_le_to_Z (bs : List byte) : Int := (bytes_le_to_nat bs : Int)

/-- The same value truncated to 64 bits; callers never pass more than
8 bytes, where the truncation does nothing. -/
def le_bytes_to_word (bs : List byte) : word :=
  Z_to_bv 64 (bytes_le_to_Z bs)

/-- The `n` little-endian bytes of `z` (index 0 = least significant) —
`bytes_le_to_Z`'s inverse, truncating `z` to `8n` bits.  `Int`'s `>>>` is
the arithmetic shift `Z.shiftr` is. -/
def Z_to_le_bytes (n : Nat) (z : Int) : List byte :=
  match n with
  | 0 => []
  | n' + 1 => Z_to_bv 8 z :: Z_to_le_bytes n' (z >>> 8)

theorem length_Z_to_le_bytes (n : Nat) (z : Int) : (Z_to_le_bytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [Z_to_le_bytes, ih]

/-- The 4 little-endian bytes of a word's low half — an `int` as the
kernel's `put_user` stores it. -/
def word_le4 (v : word) : List byte :=
  [ bv_extract 0 8 v, bv_extract 8 8 v, bv_extract 16 8 v,
    bv_extract 24 8 v ]

/-- The 2 little-endian bytes of a word's low quarter — a `short` as the
kernel's `put_user` stores it.  `ppoll`'s `revents` is the one field any
modeled syscall writes at this width. -/
def word_le2 (v : word) : List byte :=
  [ bv_extract 0 8 v, bv_extract 8 8 v ]

end LinuxProcessSemantics.LinuxProcessSem.BvBase
