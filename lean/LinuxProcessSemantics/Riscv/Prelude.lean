/-! # Prelude: bitvector helpers and the register-file map

Mirrors `theories/Riscv/Prelude.v`.

The Rocq file works over stdpp's `bv n` (a `Z` with a well-formedness
proof) and keeps its range arithmetic in `Z`.  Here `bv n` is Lean's
`BitVec n`, `Z` is `Int`, `N`/`nat` are `Nat`, and the stdpp names the
Rocq tree uses (`bv_unsigned`, `bv_signed`, `Z_to_bv`, `bv_extract`,
`bv_concat`, …) are given as definitions over `BitVec` with the same names
and argument order, so a Rocq expression transcribes token for token.

Representation differences, stated once:

- `bvmap n A` retains Rocq's raw radix tree, including empty internal
  nodes and the phantom width parameter. Equal lookup results do not imply
  equal trees. The binary-positive key uses the same unsigned-value-plus-one
  encoding as Rocq's `bv_key`.
- `bv_eqb` is `Z.eqb` on `bv_unsigned` in Rocq; here it is `BitVec`'s
  decidable equality, which agrees (`bv_eqb_eq`). -/

namespace LinuxProcessSemantics.Riscv.Prelude

abbrev word := BitVec 64
abbrev reg := BitVec 5

/-- stdpp's `bv_unsigned`: the value as a non-negative integer. -/
def bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- stdpp's `bv_signed`: the two's-complement reading. -/
def bv_signed {n : Nat} (w : BitVec n) : Int := w.toInt

/-- stdpp's `Z_to_bv n z`: wrap an integer into `n` bits (two's complement
for negative `z`). -/
def Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- stdpp's `bv_extract lo len w`. -/
def bv_extract {n : Nat} (lo len : Nat) (w : BitVec n) : BitVec len :=
  w.extractLsb' lo len

/-- stdpp's `bv_concat m hi lo`: `hi` lands in the HIGH bits.  The Rocq
form takes the result width `m` explicitly; here it is `hi.width + lo.width`,
which Lean computes, so the argument is dropped. -/
def bv_concat {a b : Nat} (hi : BitVec a) (lo : BitVec b) : BitVec (a + b) :=
  hi ++ lo

/-- stdpp's `bv_sign_extend`/`bv_zero_extend`. -/
def bv_sign_extend {n : Nat} (m : Nat) (b : BitVec n) : BitVec m := b.signExtend m
def bv_zero_extend {n : Nat} (m : Nat) (b : BitVec n) : BitVec m := b.zeroExtend m

/-- stdpp's `bv_ashiftr`: arithmetic shift right by a bitvector amount. -/
def bv_ashiftr {n : Nat} (a k : BitVec n) : BitVec n := a.sshiftRight k.toNat

/-- stdpp's truncating signed division/remainder and unsigned
division/modulus (`Z.quot`/`Z.rem` and `Z.div`/`Z.modulo` on the unsigned
reading).  Lean's `BitVec.sdiv`/`srem` round toward zero, as `Z.quot`/`Z.rem`
do. -/
def bv_quots {n : Nat} (a b : BitVec n) : BitVec n := a.sdiv b
def bv_rems {n : Nat} (a b : BitVec n) : BitVec n := a.srem b
def bv_divu {n : Nat} (a b : BitVec n) : BitVec n := a.udiv b
def bv_modu {n : Nat} (a b : BitVec n) : BitVec n := a.umod b

def bv_and {n : Nat} (a b : BitVec n) : BitVec n := a &&& b
def bv_or {n : Nat} (a b : BitVec n) : BitVec n := a ||| b
def bv_xor {n : Nat} (a b : BitVec n) : BitVec n := a ^^^ b
def bv_not {n : Nat} (a : BitVec n) : BitVec n := ~~~ a

/-- Extract bits `[lo+len-1 .. lo]` of `w` as a bitvector of width `len`. -/
def bits {n : Nat} (lo len : Nat) (w : BitVec n) : BitVec len := bv_extract lo len w

def sext {n : Nat} (m : Nat) (b : BitVec n) : BitVec m := bv_sign_extend m b
def zext {n : Nat} (m : Nat) (b : BitVec n) : BitVec m := bv_zero_extend m b

/-- Untyped bit test, for decoding. -/
def bit {n : Nat} (i : Nat) (w : BitVec n) : Bool := w.getLsbD i

/-! ## Signedness-explicit wrappers -/

def bv_lts {n : Nat} (a b : BitVec n) : Bool := a.slt b
def bv_ltu {n : Nat} (a b : BitVec n) : Bool := a.ult b

/-- Equality is signedness-independent; included for uniformity. -/
def bv_eqb {n : Nat} (a b : BitVec n) : Bool := a == b

theorem bv_eqb_eq {n : Nat} (a b : BitVec n) : bv_eqb a b = true ↔ a = b := by
  simp [bv_eqb]

/-- High `n` bits of the exact 2n-bit product, under the three signedness
readings.  `Int`'s `>>>` is an arithmetic shift, as `Z.shiftr` is. -/
def bv_mulhss {n : Nat} (a b : BitVec n) : BitVec n :=
  Z_to_bv n ((bv_signed a * bv_signed b) >>> n)
def bv_mulhsu {n : Nat} (a b : BitVec n) : BitVec n :=
  Z_to_bv n ((bv_signed a * bv_unsigned b) >>> n)
def bv_mulhuu {n : Nat} (a b : BitVec n) : BitVec n :=
  Z_to_bv n ((bv_unsigned a * bv_unsigned b) >>> n)

/-! ## The register-file map

The tree and its operations mirror `theories/Riscv/Prelude.v:54–128` at
reference commit `9a070af9e60b69831eee66067be0dd42e5ec244e`. In particular,
the representation is not quotiented by lookup equality and does not prune
empty nodes. `positive` spells out Rocq's binary-positive constructors;
the numeric bridge below justifies the key conversion. -/

inductive positive where
  | xI (p : positive)
  | xO (p : positive)
  | xH
  deriving DecidableEq

export positive (xI xO xH)

def positive.toNat : positive → Nat
  | xI p => 2 * p.toNat + 1
  | xO p => 2 * p.toNat
  | xH => 1

theorem positive.toNat_pos (p : positive) : 0 < p.toNat := by
  induction p <;> simp only [positive.toNat] <;> omega

/-- The positive part of Rocq's `Z.to_pos`: zero also maps to `xH`.
Recursing on binary digits avoids unary traversal of an address. -/
def positive.ofNat (n : Nat) : positive :=
  if n ≤ 1 then xH
  else if n % 2 = 0 then xO (positive.ofNat (n / 2))
  else xI (positive.ofNat (n / 2))
termination_by n
decreasing_by all_goals omega

theorem positive.toNat_ofNat (n : Nat) (hn : 0 < n) :
    (positive.ofNat n).toNat = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [positive.ofNat]
      split
      · simp only [positive.toNat]
        omega
      · rename_i hlarge
        have hhalf : 0 < n / 2 := by omega
        have hlt : n / 2 < n := by omega
        have hi := ih (n / 2) hlt hhalf
        split <;> simp only [positive.toNat, hi] <;> omega

theorem positive.toNat_inj {p q : positive} (h : p.toNat = q.toNat) : p = q := by
  induction p generalizing q with
  | xH =>
      cases q with
      | xH => rfl
      | xI q => have := positive.toNat_pos q; simp only [positive.toNat] at h; omega
      | xO q => have := positive.toNat_pos q; simp only [positive.toNat] at h; omega
  | xI p ih =>
      cases q with
      | xH => have := positive.toNat_pos p; simp only [positive.toNat] at h; omega
      | xI q => exact congrArg xI (ih (by simp only [positive.toNat] at h; omega))
      | xO q => simp only [positive.toNat] at h; omega
  | xO p ih =>
      cases q with
      | xH => have := positive.toNat_pos p; simp only [positive.toNat] at h; omega
      | xI q => simp only [positive.toNat] at h; omega
      | xO q => exact congrArg xO (ih (by simp only [positive.toNat] at h; omega))

@[simp] theorem positive.ofNat_toNat (p : positive) : positive.ofNat p.toNat = p := by
  apply positive.toNat_inj
  exact positive.toNat_ofNat _ (positive.toNat_pos p)

inductive tree (A : Type) where
  | TEmpty
  | TNode (l : tree A) (v : Option A) (r : tree A)
  deriving DecidableEq

export tree (TEmpty TNode)

def tget {A : Type} (p : positive) (t : tree A) : Option A :=
  match t with
  | TEmpty => none
  | TNode l v r =>
      match p with
      | xH => v
      | xO p => tget p l
      | xI p => tget p r
termination_by structural t

def tset {A : Type} (p : positive) (x : A) (t : tree A) : tree A :=
  match t with
  | TEmpty =>
      match p with
      | xH => TNode TEmpty (some x) TEmpty
      | xO p => TNode (tset p x TEmpty) none TEmpty
      | xI p => TNode TEmpty none (tset p x TEmpty)
  | TNode l v r =>
      match p with
      | xH => TNode l (some x) r
      | xO p => TNode (tset p x l) v r
      | xI p => TNode l v (tset p x r)

@[simp] theorem tget_empty {A : Type} (p : positive) : tget p (TEmpty : tree A) = none := rfl

@[simp] theorem tget_tset_same {A : Type} (p : positive) (x : A) (t : tree A) :
    tget p (tset p x t) = some x := by
  induction p generalizing t <;> cases t <;> simp_all [tget, tset]

theorem tget_tset_other {A : Type} (p q : positive) (x : A) (t : tree A) :
    p ≠ q → tget q (tset p x t) = tget q t := by
  intro hne
  induction p generalizing q t with
  | xH => cases q <;> cases t <;> simp_all [tget, tset]
  | xO p ih =>
      cases q with
      | xH => cases t <;> rfl
      | xI q => cases t <;> rfl
      | xO q =>
          have hpq : p ≠ q := fun h => hne (congrArg xO h)
          cases t with
          | TEmpty =>
              change tget q (tset p x TEmpty) = none
              exact (ih q TEmpty hpq).trans (tget_empty q)
          | TNode l v r =>
              change tget q (tset p x l) = tget q l
              exact ih q l hpq
  | xI p ih =>
      cases q with
      | xH => cases t <;> rfl
      | xO q => cases t <;> rfl
      | xI q =>
          have hpq : p ≠ q := fun h => hne (congrArg xI h)
          cases t with
          | TEmpty =>
              change tget q (tset p x TEmpty) = none
              exact (ih q TEmpty hpq).trans (tget_empty q)
          | TNode l v r =>
              change tget q (tset p x r) = tget q r
              exact ih q r hpq

@[simp] theorem tset_tset_same {A : Type} (p : positive) (x y : A) (t : tree A) :
    tset p x (tset p y t) = tset p x t := by
  induction p generalizing t <;> cases t <;> simp_all [tset]

def bv_key {n : Nat} (b : BitVec n) : positive := positive.ofNat (b.toNat + 1)

@[simp] theorem bv_key_toNat {n : Nat} (b : BitVec n) : (bv_key b).toNat = b.toNat + 1 :=
  positive.toNat_ofNat _ (by omega)

theorem bv_key_inj {n : Nat} (b₁ b₂ : BitVec n) : bv_key b₁ = bv_key b₂ → b₁ = b₂ := by
  intro h
  have hnat := congrArg positive.toNat h
  simp only [bv_key_toNat] at hnat
  apply BitVec.eq_of_toNat_eq
  omega

/-- The width is deliberately phantom, as in Rocq's definition. -/
def bvmap (_n : Nat) (A : Type) : Type := tree A

instance {n : Nat} {A : Type} [DecidableEq A] : DecidableEq (bvmap n A) :=
  inferInstanceAs (DecidableEq (tree A))

def bvmap_get {n : Nat} {A : Type} (k : BitVec n) (m : bvmap n A) : Option A :=
  tget (bv_key k) m
def bvmap_set {n : Nat} {A : Type} (k : BitVec n) (x : A) (m : bvmap n A) : bvmap n A :=
  tset (bv_key k) x m
def bvmap_empty {n : Nat} {A : Type} : bvmap n A := TEmpty

@[simp] theorem bvmap_get_empty {n : Nat} {A : Type} (k : BitVec n) :
    bvmap_get k (bvmap_empty : bvmap n A) = none := rfl

@[simp] theorem bvmap_get_set_same {n : Nat} {A : Type} (k : BitVec n) (x : A) (m : bvmap n A) :
    bvmap_get k (bvmap_set k x m) = some x := tget_tset_same _ _ _

theorem bvmap_get_set_other {n : Nat} {A : Type} (k k' : BitVec n) (x : A) (m : bvmap n A) :
    k ≠ k' → bvmap_get k' (bvmap_set k x m) = bvmap_get k' m := by
  intro h
  apply tget_tset_other
  exact fun hk => h (bv_key_inj k k' hk)

@[simp] theorem bvmap_get_set {n : Nat} {A : Type} (k k' : BitVec n) (x : A)
    (m : bvmap n A) :
    bvmap_get k' (bvmap_set k x m) = if k' = k then some x else bvmap_get k' m := by
  split
  · rename_i h
    subst k'
    exact bvmap_get_set_same k x m
  · rename_i h
    exact bvmap_get_set_other k k' x m (Ne.symm h)

@[simp] theorem bvmap_set_set_same {n : Nat} {A : Type} (k : BitVec n) (x y : A)
    (m : bvmap n A) : bvmap_set k x (bvmap_set k y m) = bvmap_set k x m :=
  tset_tset_same _ _ _ _

/- The collision that a functional encoding erased, pinned on the actual
ported datatype. Lookup equality is insufficient for raw map equality. -/
theorem empty_node_lookup {A : Type} (p : positive) :
    tget p (TNode TEmpty none TEmpty : tree A) = tget p TEmpty := by
  cases p <;> rfl

theorem empty_node_ne_empty {A : Type} :
    (TNode TEmpty none TEmpty : tree A) ≠ TEmpty := by
  intro h
  cases h

theorem lookup_extensionality_rejected :
    ¬ (∀ a b : bvmap 5 Nat, (∀ k : BitVec 5, bvmap_get k a = bvmap_get k b) → a = b) := by
  intro h
  exact empty_node_ne_empty (h (TNode TEmpty none TEmpty) TEmpty
    (fun k => empty_node_lookup (bv_key k)))

theorem key_zero : bv_key (0#5) = xH := by decide +kernel
theorem key_last_register : bv_key (31#5) = xO (xO (xO (xO (xO xH)))) := by decide +kernel

theorem key_max_word_does_not_wrap : (bv_key (0xffffffffffffffff#64)).toNat = 2 ^ 64 := by
  rw [bv_key_toNat]
  decide

theorem wrapped_key_rejected : bv_key (0xffffffffffffffff#64) ≠ bv_key (0#64) := by
  intro h
  have := bv_key_inj _ _ h
  contradiction

theorem register_one_uses_left_child :
    bvmap_set (1#5) (7 : Nat) bvmap_empty =
      TNode (TNode TEmpty (some 7) TEmpty) none TEmpty := by
  change tset (bv_key (1#5)) 7 TEmpty = _
  decide +kernel

theorem swapped_child_rejected :
    bvmap_set (1#5) (7 : Nat) bvmap_empty ≠
      TNode TEmpty none (TNode TEmpty (some 7) TEmpty) := by
  rw [register_one_uses_left_child]
  intro h
  cases h

theorem overwrite_keeps_latest :
    bvmap_get (31#5) (bvmap_set (31#5) (8 : Nat) (bvmap_set (31#5) 7 bvmap_empty)) = some 8 :=
  bvmap_get_set_same _ _ _

theorem overwritten_value_rejected :
    bvmap_get (31#5) (bvmap_set (31#5) (8 : Nat) (bvmap_set (31#5) 7 bvmap_empty)) ≠ some 7 := by
  rw [overwrite_keeps_latest]
  decide

/-- Writing a zero is distinct from leaving a slot absent. Register
reads may map both to zero, but the raw state keeps the distinction. -/
theorem present_zero_is_not_absent {n : Nat} (k : BitVec n) :
    bvmap_set k (0 : Nat) bvmap_empty ≠ bvmap_empty := by
  intro h
  have hg := congrArg (bvmap_get k) h
  rw [bvmap_get_set_same, bvmap_get_empty] at hg
  cases hg

theorem neighboring_keys_preserved :
    bvmap_get (1#5) (bvmap_set (2#5) (9 : Nat) (bvmap_set (1#5) 7 bvmap_empty)) = some 7 := by
  rw [bvmap_get_set_other (2#5) (1#5) 9 _ (by decide), bvmap_get_set_same]

theorem neighboring_key_overwrite_rejected :
    bvmap_get (1#5) (bvmap_set (2#5) (9 : Nat) (bvmap_set (1#5) 7 bvmap_empty)) ≠ some 9 := by
  rw [neighboring_keys_preserved]
  decide

end LinuxProcessSemantics.Riscv.Prelude
