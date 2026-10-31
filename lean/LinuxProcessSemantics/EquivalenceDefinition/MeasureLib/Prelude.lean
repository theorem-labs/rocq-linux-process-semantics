-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v

import LinuxProcessSemantics.EquivalenceDefinition.Measure
import LinuxProcessSemantics.EquivalenceDefinition.GatedSize
import LinuxProcessSemantics.EquivalenceDefinition.Classifier
import LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058

# EquivalenceDefinition.MeasureLib.Prelude — the arithmetic and the packaging

This file holds Rocq `theories/EquivalenceDefinition/MeasureLib.v`
lines 1256-1833: the rational facts `QArith` does not ship, powers with
a natural exponent (`Qpow`), counting as a rational (`Qnat`), decidable
equality of cores (`FinCore_eq_dec`), the author-facing record
`CoreDistribution` with its lift to records (`cd_lift`), the two sums
every bound in the library is stated on (`core_sum` and `qsum`), and
one entry's contribution (`core_indicator`) with the three counting
lemmas about it. Each combinator of the library lives in a sibling file
and imports this one.

Rocq's `Q` is core Lean's `Rat`, whose values are reduced, so each Rocq
statement over `Qeq` is a statement over `=` here; `Measure.lean`'s
header gives that reading. Rocq's `1 # 256` is written `1 / 256`.
Rocq's `List.flat_map f l` is `l.flatMap f`, and Rocq's `List.In x l`
is `x ∈ l`.

The project depends on no Mathlib, so the rational algebra below uses
core `Rat` lemmas for the order steps and core's `grind` for the ring
identities Rocq closes with `ring`.

The record fields are exported into this namespace, so a consumer reads
`cd_weight D` the way the Rocq file does, and `D.cd_weight` as well. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Measure

/-! ## Arithmetic `QArith` does not ship -/

/-- A sum of two nonnegative rationals is nonnegative. -/
theorem Qplus_nonneg (a b : Rat) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
  fun ha hb => Rat.add_nonneg ha hb

/-- Zero is at most one. Named so that the induction steps below do not
decide a numeral in the middle of an order proof. -/
theorem Qle_0_1 : (0 : Rat) ≤ 1 := by decide +kernel

/-- Zero is at most one two-hundred-fifty-sixth, the weight of one byte. -/
theorem Qle_0_inv_256 : (0 : Rat) ≤ 1 / 256 := by decide +kernel

/-- An equation read as an inequality. -/
theorem Qle_of_Qeq (a b : Rat) : a = b → a ≤ b := by
  intro h
  rw [h]
  exact Rat.le_refl

/-! ## Powers with a natural exponent -/

/-- `q` raised to a natural power, by recursion on the exponent. The
exponent is a `Nat` and not an `Int` so that the two computation rules
below hold by conversion with no side condition on the base: the base
raised to powers in this library is zero at `p_stop = 1`, which is a
member of the geometric family in good standing. -/
def Qpow (q : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => q * Qpow q n

/-- The zero power is one. -/
theorem Qpow_0 (q : Rat) : Qpow q 0 = 1 := rfl

/-- One factor peels off a successor power. -/
theorem Qpow_succ (q : Rat) (n : Nat) : Qpow q (n + 1) = q * Qpow q n := rfl

/-- Equal bases have equal powers. -/
theorem Qpow_Qeq (q1 q2 : Rat) (n : Nat) : q1 = q2 → Qpow q1 n = Qpow q2 n := by
  intro h
  rw [h]

/-- A nonnegative base has nonnegative powers. This is what makes every
geometric weight in the library nonnegative. -/
theorem Qpow_nonneg (q : Rat) (n : Nat) : 0 ≤ q → 0 ≤ Qpow q n := by
  intro hq
  induction n with
  | zero => exact Qle_0_1
  | succ n ih =>
    rw [Qpow_succ]
    exact Rat.mul_nonneg hq ih

/-- A strictly positive base has strictly positive powers. This is what
makes an omitted tail nonzero, so that a finite list falls short of the
declared mass. -/
theorem Qpow_pos (q : Rat) (n : Nat) : 0 < q → 0 < Qpow q n := by
  intro hq
  induction n with
  | zero =>
    rw [Qpow_0]
    decide +kernel
  | succ n ih =>
    rw [Qpow_succ]
    exact Rat.mul_pos hq ih

/-- Powers distribute over a product, with no side condition. This is
the step that splits a ratio into the two powers of the closed form and
recombines `256 ^ n` with `(1/256) ^ n`. -/
theorem Qpow_mult (a b : Rat) (n : Nat) : Qpow (a * b) n = Qpow a n * Qpow b n := by
  induction n with
  | zero =>
    rw [Qpow_0, Qpow_0, Qpow_0]
    grind
  | succ n ih =>
    rw [Qpow_succ, Qpow_succ, Qpow_succ, ih]
    grind

/-- Every power of one is one. -/
theorem Qpow_1 (n : Nat) : Qpow (1 : Rat) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Qpow_succ, ih]
    grind

/-! ## Counting, as a rational -/

/-- The rational named by a natural number. A counting bound multiplies
a weight by a count, so the count has to become a rational. -/
def Qnat (n : Nat) : Rat := (n : Rat)

/-- Zero counts as zero. -/
theorem Qnat_0 : Qnat 0 = 0 := by simp [Qnat]

/-- A successor count adds one. -/
theorem Qnat_succ (n : Nat) : Qnat (n + 1) = 1 + Qnat n := by
  simp only [Qnat, Rat.natCast_add, Rat.natCast_ofNat]
  grind

/-- Counting turns a product of counts into a product of rationals. -/
theorem Qnat_mult (m n : Nat) : Qnat (m * n) = Qnat m * Qnat n := by
  simp only [Qnat, Rat.natCast_mul]

/-- Every count is nonnegative. -/
theorem Qnat_nonneg (n : Nat) : 0 ≤ Qnat n := Rat.natCast_nonneg

/-- Counting is monotone: a shorter list gets the smaller bound. -/
theorem Qnat_le (m n : Nat) : m ≤ n → Qnat m ≤ Qnat n := by
  intro h
  exact Rat.natCast_le_natCast.mpr h

/-- The one numeral that matters: the count of byte values. -/
theorem Qnat_256 : Qnat 256 = 256 := by simp [Qnat]

/-- A power of the byte count, counted as a rational, is that power of
the rational `256`. -/
theorem Qnat_pow_256 (n : Nat) : Qnat (256 ^ n) = Qpow 256 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Qnat_mult, Qnat_256, ih, Qpow_succ]
    grind

/-! ## Deciding equality of cores -/

/-- `FinInput.FinCore` has decidable equality. Every combinator that
sums entries per core needs it: "the weight of `c` is the total of the
entries naming `c`" is not a definition until "naming `c`" can be
decided. Each of the four fields is built from bytes and lists, so the
decision is the conjunction of four list comparisons, and it computes
on closed cores. -/
instance FinCore_eq_dec : DecidableEq FinCore := fun a b =>
  if h : a.core_argv = b.core_argv ∧ a.core_envp = b.core_envp ∧
      a.core_fs = b.core_fs ∧ a.core_stdin = b.core_stdin then
    isTrue (by
      obtain ⟨h1, h2, h3, h4⟩ := h
      cases a
      cases b
      dsimp only at h1 h2 h3 h4
      subst h1
      subst h2
      subst h3
      subst h4
      rfl)
  else
    isFalse (fun he => h (by subst he; exact ⟨rfl, rfl, rfl, rfl⟩))

/-! ## The author-facing packaging -/

/-- A weight on cores together with the total it declares. Three fields
and no more: the weight, the declared mass that `Measure.weight_bound_T`
multiplies by `b`, and the nonnegativity the lift needs to discharge
`Measure.Distribution`'s `w_nonneg`. Nonnegativity is a field, so it
travels with the object and a would-be distribution that fails it cannot
be built. Nothing relates the mass to the weight: the mass is trusted
task metadata with no normalization obligation. -/
structure CoreDistribution where
  mkCoreDistribution ::
  cd_weight : FinCore → Rat
  cd_mass : Rat
  cd_nonneg : ∀ c, 0 ≤ cd_weight c

export CoreDistribution (cd_weight cd_mass cd_nonneg)

/-- The weight on records a `CoreDistribution` denotes: read the core,
weigh it. This is the only way a weight built in this library reaches
`Measure.Distribution`, and it is what makes core blindness a theorem
about the library rather than an obligation on each task. -/
def cd_lift (D : CoreDistribution) : FinProcInput → Rat :=
  fun f => cd_weight D (fin_core f)

/-- `Measure.Distribution`'s `w_nonneg`, for every lift. -/
theorem cd_lift_nonneg (D : CoreDistribution) (f : FinProcInput) : 0 ≤ cd_lift D f :=
  cd_nonneg D (fin_core f)

/-- `Measure.Distribution`'s `w_core_blind`, for every lift: equal cores
are the same argument to the same function. -/
theorem cd_lift_core_blind (D : CoreDistribution) (f g : FinProcInput) :
    fin_core f = fin_core g → cd_lift D f = cd_lift D g := by
  intro h
  unfold cd_lift
  rw [h]

/-! ## The sums the bounds are stated on -/

/-- `Measure.sum_weights` of a lifted weight. It is the measure layer's
own sum by conversion, so a bound proved about `core_sum` is a bound on
the quantity `Measure.weight_bound_T` compares against `b * M`. -/
def core_sum (w : FinCore → Rat) (l : List FinProcInput) : Rat :=
  sum_weights (fun f => w (fin_core f)) l

/-- The bridge to `Measure.sum_weights`, by conversion. -/
theorem core_sum_sum_weights (w : FinCore → Rat) (l : List FinProcInput) :
    core_sum w l = sum_weights (fun f => w (fin_core f)) l := rfl

/-- The bridge in the form a consumer meets it: the sum
`Measure.weight_bound_T` takes of a lifted distribution is the library's
sum of its core weight. -/
theorem core_sum_cd_lift (D : CoreDistribution) (l : List FinProcInput) :
    core_sum (cd_weight D) l = sum_weights (cd_lift D) l := rfl

/-- The predicate-indexed crossing, at the level every bound in this
library is proved at.

The three arguments are the three things a task supplies: `Fire`, the
set of cores its bound is about; the crossing, that every valid record
outside `P` has a fire core; and the bound, that fire-core lists weigh
at most `B`. The arithmetic step `B ≤ b * cd_mass D` is kept separate,
so that one proof serves every multiplier a task may declare.

A consumer holding this at `P := Classifier.accepts C` has
`Measure.weight_bound_T C (cd_lift D) (cd_mass D) b`, because
`GatedSize.weight_bound_pred_of_classifier` is an iff. -/
theorem weight_bound_pred_T_of_core_bound (D : CoreDistribution)
    (P : FinProcInput → Prop) (Fire : FinCore → Prop) (B b : Rat) :
    (∀ f, valid_fin_input f → ¬ P f → Fire (fin_core f)) →
    (∀ l : List FinProcInput,
      (l.map fin_core).Nodup →
      (∀ f, f ∈ l → Fire (fin_core f)) →
      core_sum (cd_weight D) l ≤ B) →
    B ≤ b * cd_mass D →
    GatedSize.weight_bound_pred_T P (cd_lift D) (cd_mass D) b := by
  intro Hfire Hbound Hb l Hnd Hall
  rw [← core_sum_cd_lift]
  exact Rat.le_trans
    (Hbound l Hnd (fun f hf => Hfire f (Hall f hf).1 (Hall f hf).2)) Hb

/-- The empty list weighs nothing. -/
theorem core_sum_nil (w : FinCore → Rat) : core_sum w [] = 0 := rfl

/-- A head record contributes the weight of its core. -/
theorem core_sum_cons (w : FinCore → Rat) (f : FinProcInput) (l : List FinProcInput) :
    core_sum w (f :: l) = w (fin_core f) + core_sum w l := rfl

/-! ## Sums over a list of anything -/

/-- The sum every bound in the library is stated on: a right fold of a
weight over a list, at whatever element type the list has. One sum and
not two: the counting arguments run over lists of cores, while the
varying-environment families sum over byte lists and over lists of byte
lists. The two lemmas that need decidable equality on the element type
keep `core` in their names and stay at `FinInput.FinCore`. -/
def qsum {A : Type} (w : A → Rat) (l : List A) : Rat :=
  List.foldr (fun x acc => w x + acc) 0 l

/-- The empty list sums to zero. -/
theorem qsum_nil {A : Type} (w : A → Rat) : qsum w ([] : List A) = 0 := rfl

/-- A head element contributes its own weight. -/
theorem qsum_cons {A : Type} (w : A → Rat) (x : A) (l : List A) :
    qsum w (x :: l) = w x + qsum w l := rfl

/-- Appending lists adds their sums. -/
theorem qsum_app {A : Type} (w : A → Rat) (l1 l2 : List A) :
    qsum w (l1 ++ l2) = qsum w l1 + qsum w l2 := by
  induction l1 with
  | nil => rw [List.nil_append, qsum_nil, Rat.zero_add]
  | cons x l1 ih =>
    rw [List.cons_append, qsum_cons, qsum_cons, ih, Rat.add_assoc]

/-- A weight nonnegative on the list has a nonnegative sum. -/
theorem qsum_nonneg {A : Type} (w : A → Rat) (l : List A) :
    (∀ x ∈ l, 0 ≤ w x) → 0 ≤ qsum w l := by
  induction l with
  | nil =>
    intro _
    exact Rat.le_refl
  | cons x l ih =>
    intro hw
    rw [qsum_cons]
    exact Qplus_nonneg _ _ (hw x List.mem_cons_self)
      (ih (fun y hy => hw y (List.mem_cons_of_mem x hy)))

/-- Weights that agree on the list sum equally. The hypothesis is
membership in the list and not agreement everywhere, which is what every
restriction argument has: a weight agrees with another on the cores
being summed, and nothing is known about it elsewhere. -/
theorem qsum_ext {A : Type} (w1 w2 : A → Rat) (l : List A) :
    (∀ x ∈ l, w1 x = w2 x) → qsum w1 l = qsum w2 l := by
  induction l with
  | nil =>
    intro _
    rfl
  | cons x l ih =>
    intro hext
    rw [qsum_cons, qsum_cons, hext x List.mem_cons_self,
      ih (fun y hy => hext y (List.mem_cons_of_mem x hy))]

/-- A pointwise smaller weight on the list has a smaller sum. -/
theorem qsum_mono {A : Type} (w1 w2 : A → Rat) (l : List A) :
    (∀ x ∈ l, w1 x ≤ w2 x) → qsum w1 l ≤ qsum w2 l := by
  induction l with
  | nil =>
    intro _
    exact Rat.le_refl
  | cons x l ih =>
    intro hle
    rw [qsum_cons, qsum_cons]
    exact Rat.le_trans
      (Rat.add_le_add_right.mpr (hle x List.mem_cons_self))
      (Rat.add_le_add_left.mpr (ih (fun y hy => hle y (List.mem_cons_of_mem x hy))))

/-- A constant factor comes out of the sum. -/
theorem qsum_scale {A : Type} (c : Rat) (w : A → Rat) (l : List A) :
    qsum (fun x => c * w x) l = c * qsum w l := by
  induction l with
  | nil =>
    rw [qsum_nil, qsum_nil]
    grind
  | cons x l ih =>
    rw [qsum_cons, qsum_cons, ih]
    grind

/-- Summing over a mapped list is summing the composed weight. -/
theorem qsum_map {A B : Type} (w : B → Rat) (f : A → B) (l : List A) :
    qsum w (l.map f) = qsum (fun x => w (f x)) l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, qsum_cons, qsum_cons, ih]

/-- A flattened map is the sum of its blocks exactly, not merely up to a
uniform bound. Charging every block the same constant is right for the
256 continuations of a standard-input cylinder and wrong for an envp
enumeration, where a block is charged by the entry's own length. -/
theorem qsum_flat_map {A B : Type} (w : B → Rat) (f : A → List B) (l : List A) :
    qsum w (l.flatMap f) = qsum (fun x => qsum w (f x)) l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, qsum_app, ih, qsum_cons]

/-- The per-block inequality that the identity above gives. -/
theorem qsum_flat_map_le {A B : Type} (w : B → Rat) (f : A → List B) (g : A → Rat)
    (l : List A) :
    (∀ x ∈ l, qsum w (f x) ≤ g x) → qsum w (l.flatMap f) ≤ qsum g l := by
  intro hb
  rw [qsum_flat_map]
  exact qsum_mono _ _ l hb

/-- A map commutes past a flattened map. -/
theorem map_flat_map_comm (A B C : Type) (f : B → C) (g : A → List B) (l : List A) :
    (l.flatMap g).map f = l.flatMap (fun x => (g x).map f) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons]

/-- Summing a lifted weight over records is summing the weight over
their cores: both folds add the same rationals in the same order. -/
theorem core_sum_map_fin_core (w : FinCore → Rat) (l : List FinProcInput) :
    core_sum w l = qsum w (l.map fin_core) := by
  induction l with
  | nil => rfl
  | cons f l ih => rw [core_sum_cons, ih, List.map_cons, qsum_cons]

/-- The zero weight sums to zero. -/
theorem qsum_zero {A : Type} (cs : List A) : qsum (fun _ : A => (0 : Rat)) cs = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [qsum_cons, ih]
    grind

/-- Sums add pointwise. This splits an entry list's weight into the head
entry plus the rest without touching the list being summed over. -/
theorem qsum_plus {A : Type} (w1 w2 : A → Rat) (cs : List A) :
    qsum (fun c => w1 c + w2 c) cs = qsum w1 cs + qsum w2 cs := by
  induction cs with
  | nil =>
    rw [qsum_nil, qsum_nil, qsum_nil]
    grind
  | cons c cs ih =>
    rw [qsum_cons, qsum_cons, qsum_cons, ih]
    grind

/-! ## One entry's contribution -/

/-- The weight a single entry assigns: `q` at its own core, zero
everywhere else. Every finite-support weight is a sum of these. -/
def core_indicator (c0 : FinCore) (q : Rat) (c : FinCore) : Rat :=
  if c0 = c then q else 0

/-- At its own core the entry gives its weight. -/
theorem core_indicator_hit (c0 : FinCore) (q : Rat) : core_indicator c0 q c0 = q := by
  simp [core_indicator]

/-- At any other core it gives zero. -/
theorem core_indicator_miss (c0 : FinCore) (q : Rat) (c : FinCore) :
    c0 ≠ c → core_indicator c0 q c = 0 := by
  intro hne
  simp [core_indicator, hne]

/-- Over a list that does not mention the entry's core, the entry
contributes nothing. -/
theorem qsum_indicator_absent (c0 : FinCore) (q : Rat) (cs : List FinCore) :
    c0 ∉ cs → qsum (core_indicator c0 q) cs = 0 := by
  induction cs with
  | nil =>
    intro _
    rfl
  | cons c cs ih =>
    intro hnin
    rw [qsum_cons,
      core_indicator_miss c0 q c (fun heq => hnin (heq ▸ List.mem_cons_self)),
      ih (fun hin => hnin (List.mem_cons_of_mem c hin))]
    grind

/-- Over a duplicate-free list that does mention it, the entry
contributes exactly its weight, once. This is why
`Measure.weight_bound_T` carries the duplicate-freedom hypothesis. -/
theorem qsum_indicator_present (c0 : FinCore) (q : Rat) (cs : List FinCore) :
    cs.Nodup → c0 ∈ cs → qsum (core_indicator c0 q) cs = q := by
  induction cs with
  | nil =>
    intro _ hin
    exact absurd hin List.not_mem_nil
  | cons c cs ih =>
    intro hnd hin
    obtain ⟨hnin, hnd'⟩ := List.nodup_cons.mp hnd
    rw [qsum_cons]
    by_cases heq : c0 = c
    · subst heq
      rw [core_indicator_hit, qsum_indicator_absent c0 q cs hnin]
      grind
    · rw [core_indicator_miss c0 q c heq]
      rcases List.mem_cons.mp hin with h | h
      · exact absurd h heq
      · rw [ih hnd' h]
        grind

/-- Either way, a nonnegative entry contributes at most its weight over
a duplicate-free list: it is counted once or not at all. -/
theorem qsum_indicator_le (c0 : FinCore) (q : Rat) (cs : List FinCore) :
    0 ≤ q → cs.Nodup → qsum (core_indicator c0 q) cs ≤ q := by
  intro hq hnd
  by_cases hin : c0 ∈ cs
  · rw [qsum_indicator_present c0 q cs hnd hin]
    exact Rat.le_refl
  · rw [qsum_indicator_absent c0 q cs hin]
    exact hq

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
