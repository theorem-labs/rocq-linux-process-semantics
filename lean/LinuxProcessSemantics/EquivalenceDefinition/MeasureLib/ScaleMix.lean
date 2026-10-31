-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-!

# EquivalenceDefinition.MeasureLib.ScaleMix — scaling and mixture

Holds `theories/EquivalenceDefinition/MeasureLib.v:3659-5259`: the two
composition combinators (scaling a distribution by a nonnegative factor,
and adding two distributions pointwise), the `n`-ary fold of the second,
the proofs that upper and lower bounds survive both, the arithmetic of
how fast a power of a proper fraction shrinks, the length-`< k` prefix
family of standard inputs and what it weighs, the lower certificate for
`stdin_geometric` with the proof that its declared mass is a supremum and
not a maximum, one worked distribution (named cores over a geometric
background) with its `Measure.Distribution` and the recipe for
discharging `Measure.weight_bound_T` and
`GatedSize.weight_bound_pred_T` with it, and the three standard-input
enumerations read off the cores.

Rocq `Qeq` is `=` here, as `Measure.lean`'s header says.  Rocq `ring` on
`Q` becomes `grind`, which normalizes commutative-ring and linear-order
goals over `Rat` in Lean 4.34 core; Rocq's `vm_compute` on closed
rational literals becomes `decide +kernel`, as in `Measure.lean`.
Rocq's `Module Worked_D <: DISTRIBUTION` becomes the term `Worked_D` of
the structure `Measure.Distribution`, so `Worked_D.w` and `Worked_D.M`
keep their Rocq names as field projections.

The one `private` declaration, `exists_nodup_cover`, stands for the
`List.nodup` call Rocq makes inside one proof: Lean core's
`List.eraseDups` carries no duplicate-freedom lemma, so the covering list
is built by induction here.  It is private so that no sibling file in
this namespace can collide with the name. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.EquivalenceDefinition.Measure

/-! ## Combinators: scaling and mixture -/

/-- Scaling a distribution by a nonnegative factor: every weight and the
declared mass multiplied together, so the relation the certificates
report between them is preserved rather than true by luck.  `0 ≤ q` is a
constructor argument because `cd_nonneg` is a field and a scaling that
returned a `CoreDistribution` without a proof would have to invent it; at
a negative `q` there is nothing to invent, which
`cd_scale_negative_no_core_distribution` records. -/
def cd_scale (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution) : CoreDistribution :=
  CoreDistribution.mkCoreDistribution (fun c => q * cd_weight D c) (q * cd_mass D)
    (fun c => Rat.mul_nonneg Hq (cd_nonneg D c))

/-- The mixture of two distributions: the weights add, pointwise, and the
declared masses add with them.  Nothing is normalized and nothing is
halved; a probabilist's mixture is this combinator applied to two
`cd_scale`s.  Supports may overlap, and on a shared core the weights add
like everywhere else — `cd_mix2_overlap_weights_add` pins the arithmetic
and `cd_mix2_bound_is_not_the_max` pins the consequence. -/
def cd_mix2 (D1 D2 : CoreDistribution) : CoreDistribution :=
  CoreDistribution.mkCoreDistribution (fun c => cd_weight D1 c + cd_weight D2 c)
    (cd_mass D1 + cd_mass D2)
    (fun c => Qplus_nonneg _ _ (cd_nonneg D1 c) (cd_nonneg D2 c))

/-- The empty mixture: weight zero everywhere, declared mass zero.  It is
the unit the `n`-ary fold folds against, and every bound holds of it. -/
def cd_zero : CoreDistribution :=
  CoreDistribution.mkCoreDistribution (fun _ => 0) 0 (fun _ => Rat.le_refl)

/-- The `n`-ary mixture, as the fold of `cd_mix2` over `cd_zero`.  Written
as a recursion rather than a `foldr` with a `CoreDistribution`
accumulator so that the weight of a cons reduces to a sum of a weight and
a recursive call by conversion, which is what `cd_mix_bound` wants. -/
def cd_mix : List CoreDistribution → CoreDistribution
  | [] => cd_zero
  | D :: rest => cd_mix2 D (cd_mix rest)

/-- The total a list of per-component numbers declares.  Its own
definition so that the `n`-ary bound and the `n`-ary mass are the same
fold at two different arguments; `cd_mix_mass` is that identification. -/
def cd_sum_over (B : CoreDistribution → Rat) (Ds : List CoreDistribution) : Rat :=
  Ds.foldr (fun D acc => B D + acc) 0

/-- The mixture's declared mass is the total of the components': both
sides are the same fold, so this is an equality and not merely an
equality of values. -/
theorem cd_mix_mass (Ds : List CoreDistribution) :
    cd_mass (cd_mix Ds) = cd_sum_over cd_mass Ds := by
  induction Ds with
  | nil => rfl
  | cons D Ds IH =>
    show cd_mass D + cd_mass (cd_mix Ds) = cd_mass D + cd_sum_over cd_mass Ds
    rw [IH]

/-! ## The bounds compose -/

/-- Scaling: a bound for `D` scales to a bound for the scaling.  `B` is
any bound whatever, not necessarily the declared mass, so this applies to
a cylinder bound and a length-slice bound as well.  Nonnegativity of `q`
is the constructor's own argument, so a consumer never supplies it
twice. -/
theorem cd_scale_bound (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput) (B : Rat) :
    core_sum (cd_weight D) l ≤ B →
    core_sum (cd_weight (cd_scale q Hq D)) l ≤ q * B := by
  intro Hb
  show core_sum (fun c => q * cd_weight D c) l ≤ q * B
  rw [core_sum_scale]
  exact Rat.mul_le_mul_of_nonneg_left Hb Hq

/-- ... and the declared mass scales with it, by conversion, so the mass
certificate survives scaling. -/
theorem cd_scale_mass (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution) :
    cd_mass (cd_scale q Hq D) = q * cd_mass D := rfl

/-- The mass certificate of a scaling, as the instance of
`cd_scale_bound` at the declared mass. -/
theorem cd_scale_bound_mass (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput) :
    core_sum (cd_weight D) l ≤ cd_mass D →
    core_sum (cd_weight (cd_scale q Hq D)) l ≤ cd_mass (cd_scale q Hq D) := by
  intro Hb
  exact cd_scale_bound q Hq D l (cd_mass D) Hb

/-- ... and so does the sign of the mass, which is what
`Measure.Distribution`'s `M_nonneg` asks about.  The `0 ≤ q` here is
`cd_scale`'s own argument, not a new hypothesis. -/
theorem cd_scale_mass_nonneg (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution) :
    0 ≤ cd_mass D → 0 ≤ cd_mass (cd_scale q Hq D) := by
  intro HD
  rw [cd_scale_mass]
  exact Rat.mul_nonneg Hq HD

/-- Mixture: bounds for the two components add to a bound for the
mixture, on the same list.  That the list is shared is the whole content;
no rearrangement and no duplicate-freedom argument happens here. -/
theorem cd_mix2_bound (D1 D2 : CoreDistribution) (l : List FinProcInput) (B1 B2 : Rat) :
    core_sum (cd_weight D1) l ≤ B1 →
    core_sum (cd_weight D2) l ≤ B2 →
    core_sum (cd_weight (cd_mix2 D1 D2)) l ≤ B1 + B2 := by
  intro H1 H2
  show core_sum (fun c => cd_weight D1 c + cd_weight D2 c) l ≤ B1 + B2
  rw [core_sum_plus]
  exact Rat.le_trans (Rat.add_le_add_right.mpr H1) (Rat.add_le_add_left.mpr H2)

/-- The mixture's declared mass is the sum of the components', by
conversion. -/
theorem cd_mix2_mass (D1 D2 : CoreDistribution) :
    cd_mass (cd_mix2 D1 D2) = cd_mass D1 + cd_mass D2 := rfl

/-- The mass certificate of a mixture, as the instance of `cd_mix2_bound`
at the two declared masses. -/
theorem cd_mix2_bound_mass (D1 D2 : CoreDistribution) (l : List FinProcInput) :
    core_sum (cd_weight D1) l ≤ cd_mass D1 →
    core_sum (cd_weight D2) l ≤ cd_mass D2 →
    core_sum (cd_weight (cd_mix2 D1 D2)) l ≤ cd_mass (cd_mix2 D1 D2) := by
  intro H1 H2
  exact cd_mix2_bound D1 D2 l (cd_mass D1) (cd_mass D2) H1 H2

/-- The mixture's mass is nonnegative when both components' are, by the
same fact that makes `cd_mix2`'s nonnegativity field composable.  With
`cd_scale_mass_nonneg` this closes `Measure.Distribution`'s `M_nonneg`
under the two combinators a probabilist's mixture is written with. -/
theorem cd_mix2_mass_nonneg (D1 D2 : CoreDistribution) :
    0 ≤ cd_mass D1 → 0 ≤ cd_mass D2 → 0 ≤ cd_mass (cd_mix2 D1 D2) := by
  intro H1 H2
  rw [cd_mix2_mass]
  exact Qplus_nonneg _ _ H1 H2

/-- The `n`-ary form: a bound for every component gives the total of
those bounds for the mixture.  The bounds are a function of the component
rather than a parallel list, so nothing has to line up two lists, and
`cd_sum_over` is then literally the same fold as `cd_mix`'s mass. -/
theorem cd_mix_bound (B : CoreDistribution → Rat) (Ds : List CoreDistribution)
    (l : List FinProcInput) :
    (∀ D, D ∈ Ds → core_sum (cd_weight D) l ≤ B D) →
    core_sum (cd_weight (cd_mix Ds)) l ≤ cd_sum_over B Ds := by
  induction Ds with
  | nil =>
    intro _
    show core_sum (fun _ => (0 : Rat)) l ≤ 0
    rw [core_sum_zero]
    exact Rat.le_refl
  | cons D Ds IH =>
    intro Hb
    show core_sum (cd_weight (cd_mix2 D (cd_mix Ds))) l ≤ B D + cd_sum_over B Ds
    exact cd_mix2_bound D (cd_mix Ds) l (B D) (cd_sum_over B Ds)
      (Hb D (List.mem_cons.mpr (Or.inl rfl)))
      (IH (fun D' HD' => Hb D' (List.mem_cons.mpr (Or.inr HD'))))

/-- ... and at the components' declared masses that is the mixture's own
mass certificate, which is what a task author building a
background-plus-foreground distribution consumes. -/
theorem cd_mix_bound_mass (Ds : List CoreDistribution) (l : List FinProcInput) :
    (∀ D, D ∈ Ds → core_sum (cd_weight D) l ≤ cd_mass D) →
    core_sum (cd_weight (cd_mix Ds)) l ≤ cd_mass (cd_mix Ds) := by
  intro Hb
  rw [cd_mix_mass]
  exact cd_mix_bound cd_mass Ds l Hb

/-! ## The certificates compose too -/

/-- The lower half survives scaling.  It is worth stating apart from the
upper half because the two travel differently: component upper bounds may
be proved on lists chosen independently, while an attaining list has to be
one list that attains both, hence the shared `l` below.  The generic-`B`
form comes first because it is the only one a geometric component can
use: such a family never attains its declared mass. -/
theorem cd_scale_bound_lower (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput) (B : Rat) :
    B ≤ core_sum (cd_weight D) l →
    q * B ≤ core_sum (cd_weight (cd_scale q Hq D)) l := by
  intro Hb
  show q * B ≤ core_sum (fun c => q * cd_weight D c) l
  rw [core_sum_scale]
  exact Rat.mul_le_mul_of_nonneg_left Hb Hq

/-- The lower half survives mixing, on the one shared list. -/
theorem cd_mix2_bound_lower (D1 D2 : CoreDistribution) (l : List FinProcInput)
    (B1 B2 : Rat) :
    B1 ≤ core_sum (cd_weight D1) l →
    B2 ≤ core_sum (cd_weight D2) l →
    B1 + B2 ≤ core_sum (cd_weight (cd_mix2 D1 D2)) l := by
  intro H1 H2
  show B1 + B2 ≤ core_sum (fun c => cd_weight D1 c + cd_weight D2 c) l
  rw [core_sum_plus]
  exact Rat.le_trans (Rat.add_le_add_right.mpr H1) (Rat.add_le_add_left.mpr H2)

/-- The scaling form of the lower half at the declared mass. -/
theorem cd_scale_mass_lower (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput) :
    cd_mass D ≤ core_sum (cd_weight D) l →
    cd_mass (cd_scale q Hq D) ≤ core_sum (cd_weight (cd_scale q Hq D)) l := by
  intro Hlow
  exact cd_scale_bound_lower q Hq D l (cd_mass D) Hlow

/-- The mixture form of the lower half at the two declared masses. -/
theorem cd_mix2_mass_lower (D1 D2 : CoreDistribution) (l : List FinProcInput) :
    cd_mass D1 ≤ core_sum (cd_weight D1) l →
    cd_mass D2 ≤ core_sum (cd_weight D2) l →
    cd_mass (cd_mix2 D1 D2) ≤ core_sum (cd_weight (cd_mix2 D1 D2)) l := by
  intro H1 H2
  exact cd_mix2_bound_lower D1 D2 l (cd_mass D1) (cd_mass D2) H1 H2

/-- Some duplicate-free list of cores covers a given list of cores.  Rocq
builds it with `List.nodup`; Lean core's `List.eraseDups` carries no
duplicate-freedom lemma, so the covering list is built here by induction.
Private: it is not a declaration of the Rocq file. -/
private theorem exists_nodup_cover (cs : List FinCore) :
    ∃ ds : List FinCore, ds.Nodup ∧ ∀ c, c ∈ cs → c ∈ ds := by
  induction cs with
  | nil => exact ⟨[], List.nodup_nil, fun c h => absurd h List.not_mem_nil⟩
  | cons c cs IH =>
    obtain ⟨ds, Hnd, Hcov⟩ := IH
    by_cases hc : c ∈ ds
    · refine ⟨ds, Hnd, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact Hcov x hx
    · refine ⟨c :: ds, List.nodup_cons.mpr ⟨hc, Hnd⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (Hcov x hx))

/-- A mixture of two finite supports has its mass attained, which is the
case a task actually meets.  The canonical list of one component covers
its own entries and says nothing about the other's, so the list used here
is the cores of both entry lists with duplicates removed; it covers each
component because each entry list sits in their concatenation.
`cd_mix2_mass_lower` then adds the two attainments, `cd_mix2_bound_mass`
adds the two bounds, and the equality is antisymmetry on those, never a
computation. -/
theorem cd_mix2_finite_support_mass_exact (e1 e2 : List (FinCore × Rat))
    (H1 : ∀ e, e ∈ e1 → 0 ≤ e.2) (H2 : ∀ e, e ∈ e2 → 0 ≤ e.2) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ core_sum (cd_weight (cd_mix2 (finite_support e1 H1) (finite_support e2 H2))) l
          = cd_mass (cd_mix2 (finite_support e1 H1) (finite_support e2 H2)) := by
  obtain ⟨cs, Hnd, Hcov⟩ := exists_nodup_cover ((e1 ++ e2).map Prod.fst)
  have Hndm : ((cs.map core_input).map fin_core).Nodup := by
    rw [map_fin_core_core_input]
    exact Hnd
  refine ⟨cs.map core_input, Hndm, ?_⟩
  apply Rat.le_antisymm
  · exact cd_mix2_bound_mass _ _ _
      (finite_support_bound e1 H1 _ Hndm) (finite_support_bound e2 H2 _ Hndm)
  · exact cd_mix2_mass_lower _ _ _
      (finite_support_mass_lower_on e1 H1 cs Hnd
        (fun e He => Hcov e.1 (List.mem_map.mpr ⟨e, List.mem_append.mpr (Or.inl He), rfl⟩)))
      (finite_support_mass_lower_on e2 H2 cs Hnd
        (fun e He => Hcov e.1 (List.mem_map.mpr ⟨e, List.mem_append.mpr (Or.inr He), rfl⟩)))

/-! ## Non-vacuity: what scaling and mixing do, pinned -/

/-- Scaling by zero gives the zero distribution, pointwise and in the
declared mass.  Worth pinning because it is the one input at which the
constructor's `0 ≤ q` is tight, and because a reader should see that
scaling has not quietly been given a normalizing reading. -/
theorem cd_scale_zero (D : CoreDistribution) :
    (∀ c, cd_weight (cd_scale 0 Rat.le_refl D) c = cd_weight cd_zero c)
    ∧ cd_mass (cd_scale 0 Rat.le_refl D) = cd_mass cd_zero := by
  refine ⟨fun c => ?_, ?_⟩
  · show (0 : Rat) * cd_weight D c = 0
    exact Rat.zero_mul _
  · show (0 : Rat) * cd_mass D = 0
    exact Rat.zero_mul _

/-- A negative scaling admits no `CoreDistribution` at all, which is what
makes `cd_scale`'s proof argument a refusal rather than an inconvenience:
no record whose weight agrees pointwise with `-1` times `example_cd`'s
can exist, because the nonnegativity field refutes it at the core where
`example_cd` puts a half.  A distribution with no positive weight
anywhere would survive a negative scaling, which is why the statement
names a concrete `example_cd`. -/
theorem cd_scale_negative_no_core_distribution (D : CoreDistribution) :
    ¬ (∀ c, cd_weight D c = (-1) * cd_weight example_cd c) := by
  intro Hagree
  have H := cd_nonneg D example_core_empty
  rw [Hagree example_core_empty] at H
  exact absurd H (by decide +kernel)

/-- Half the weight on the empty core: the left half of an overlapping
pair. -/
def overlap_entries_l : List (FinCore × Rat) := [(example_core_empty, 1/2)]

/-- A quarter on the empty core and an eighth on "A": the right half of
the overlapping pair.  Both entry lists weigh the empty core, which is
the overlap the three facts below are about. -/
def overlap_entries_r : List (FinCore × Rat) :=
  [(example_core_empty, 1/4), (example_core_a, 1/8)]

/-- The left distribution of the overlapping pair. -/
def overlap_cd_l : CoreDistribution :=
  finite_support overlap_entries_l
    (entries_nonneg_of_forallb overlap_entries_l (by decide +kernel))

/-- The right distribution of the overlapping pair. -/
def overlap_cd_r : CoreDistribution :=
  finite_support overlap_entries_r
    (entries_nonneg_of_forallb overlap_entries_r (by decide +kernel))

/-- Their mixture, the subject of the three pins below. -/
def overlap_mix : CoreDistribution := cd_mix2 overlap_cd_l overlap_cd_r

/-- The overlap bite: on the shared core the weights add — a half and a
quarter make three quarters, not a half and not three eighths — the core
only one of them names keeps its own weight, and the declared mass is the
sum of the two declared masses.  Nothing is double-counted, because
nothing was counted once to begin with. -/
theorem cd_mix2_overlap_weights_add :
    cd_weight overlap_mix example_core_empty = 3/4
    ∧ cd_weight overlap_mix example_core_a = 1/8
    ∧ cd_mass overlap_mix = 7/8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- ... and the mixture's bound is not the largest of the components'.
The one-element list over the shared core already weighs three quarters
under the mixture, past both components' declared masses, so no rule of
the form "a mixture is bounded by the largest of its parts" can hold and
`cd_mix2_bound`'s sum is not an over-approximation a sharper lemma could
replace by a maximum.  Stated as two refutations because the two
components' masses are the only candidate readings of "the largest". -/
theorem cd_mix2_bound_is_not_the_max :
    core_sum (cd_weight overlap_mix) [core_input example_core_empty] = 3/4
    ∧ ¬ (core_sum (cd_weight overlap_mix) [core_input example_core_empty]
          ≤ cd_mass overlap_cd_l)
    ∧ ¬ (core_sum (cd_weight overlap_mix) [core_input example_core_empty]
          ≤ cd_mass overlap_cd_r) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The `n`-ary fold agrees with the binary combinator and with its own
unit: the empty mixture declares zero, and the two-element mixture
declares and weighs what `cd_mix2` does.  Without the first conjunct the
fold could be anything on the empty list; without the other two, `cd_mix`
could disagree with `cd_mix2` and every lemma above would still hold of
each of them separately. -/
theorem cd_mix_nary_agrees :
    cd_mass (cd_mix []) = 0
    ∧ cd_mass (cd_mix [overlap_cd_l, overlap_cd_r]) = cd_mass overlap_mix
    ∧ cd_weight (cd_mix [overlap_cd_l, overlap_cd_r]) example_core_empty
        = cd_weight overlap_mix example_core_empty := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## How fast a power of a proper fraction shrinks -/

/-- A power of a number in the unit interval stays in the unit
interval. -/
theorem Qpow_le_1 (x : Rat) (k : Nat) : 0 ≤ x → x ≤ 1 → Qpow x k ≤ 1 := by
  intro Hx0 Hx1
  induction k with
  | zero =>
    rw [Qpow_0]
    exact Rat.le_refl
  | succ k IH =>
    rw [Qpow_succ]
    have h := Rat.mul_le_mul_of_nonneg_left IH Hx0
    grind

/-- The induction step of the shrinking bound, as arithmetic on its own.
With `P` for the power and `n` for the exponent: if `P * (1 + n * p)` is
at most one, so is the same expression one step on.  Expand: the first
summand is at most `1 - p` by the hypothesis, the second is at most
`(1 - p) * p` because `P ≤ 1`, and their total is `1 - p * p`, which is
at most one because a square is nonnegative.  That last inequality is
where the slack lives. -/
theorem geo_gap_step (p P n : Rat) :
    0 ≤ p → p ≤ 1 → 0 ≤ P → P ≤ 1 →
    P * (1 + n * p) ≤ 1 →
    (1 - p) * P * (1 + (1 + n) * p) ≤ 1 := by
  intro Hp0 Hp1 HP0 HP1 HIH
  have H1p : (0 : Rat) ≤ 1 - p := by grind
  have Hpp : (0 : Rat) ≤ p * p := Rat.mul_nonneg Hp0 Hp0
  have H1pp : (0 : Rat) ≤ (1 - p) * p := Rat.mul_nonneg H1p Hp0
  have HA : (1 - p) * (P * (1 + n * p)) ≤ 1 - p := by
    have h := Rat.mul_le_mul_of_nonneg_left HIH H1p
    grind
  have HB : (1 - p) * P * p ≤ (1 - p) * p := by
    have h := Rat.mul_le_mul_of_nonneg_right HP1 H1pp
    grind
  grind

/-- The shrinking bound: the `k`-th power of `1 - p` times `1 + k * p` is
at most one, for every `k` and every `p` in the unit interval.  Written
multiplied out rather than as a division, which would need `1 + k * p`
non-zero as a side condition.  No strict hypothesis appears: at `p = 0`
it says one is at most one, truthfully and uselessly, which is how the
degenerate member behaves. -/
theorem geo_gap_bound (p : Rat) (k : Nat) :
    0 ≤ p → p ≤ 1 → Qpow (1 - p) k * (1 + Qnat k * p) ≤ 1 := by
  intro Hp0 Hp1
  have H1p : (0 : Rat) ≤ 1 - p := by grind
  have H1p1 : (1 : Rat) - p ≤ 1 := by grind
  induction k with
  | zero =>
    rw [Qpow_0, Qnat_0]
    grind
  | succ k IH =>
    rw [Qpow_succ, Qnat_succ]
    exact geo_gap_step p (Qpow (1 - p) k) (Qnat k) Hp0 Hp1
      (Qpow_nonneg (1 - p) k H1p) (Qpow_le_1 (1 - p) k H1p H1p1) IH

/-- The Archimedean step, in the only form this file needs: no rational
bounds every natural.  The ceiling of the rational, carried to a natural
by `Int.toNat`, is past it. -/
theorem Qnat_unbounded (q : Rat) : ∃ k : Nat, q ≤ Qnat k := by
  refine ⟨q.ceil.toNat, Rat.le_trans Rat.le_ceil ?_⟩
  have h : (q.ceil : Int) ≤ ((q.ceil.toNat : Nat) : Int) := Int.self_le_toNat q.ceil
  have h2 : ((q.ceil : Int) : Rat) ≤ (((q.ceil.toNat : Nat) : Int) : Rat) :=
    Rat.intCast_le_intCast.mpr h
  rwa [Rat.intCast_natCast] at h2

/-- ... and so the gap can be made as small as asked, which is what
`0 < p` is for and the first place a strict inequality is load-bearing.
Take `k` past the inverse of `eps * p` — legitimate only because that
product is non-zero, which is where both strictnesses are spent — and the
shrinking bound does the rest.  At `p = 0` the choice is unavailable and
the conclusion is false, the degeneracy
`stdin_geometric_mass_lower_needs_positive` pins at the level of the
distribution. -/
theorem geo_gap_small (p eps : Rat) :
    0 < p → p ≤ 1 → 0 < eps → ∃ k : Nat, Qpow (1 - p) k ≤ eps := by
  intro Hp0 Hp1 Heps
  have Hpne : p ≠ 0 := by grind
  have Hene : eps ≠ 0 := by grind
  obtain ⟨k, Hk⟩ := Qnat_unbounded (eps * p)⁻¹
  refine ⟨k, ?_⟩
  have H1p : (0 : Rat) ≤ 1 - p := by grind
  have Hpow0 : 0 ≤ Qpow (1 - p) k := Qpow_nonneg (1 - p) k H1p
  have hid : (eps * p)⁻¹ * p = eps⁻¹ := by
    rw [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm eps⁻¹ p, ← Rat.mul_assoc,
      Rat.inv_mul_cancel p Hpne, Rat.one_mul]
  have Hstep : eps⁻¹ ≤ Qnat k * p := by
    have h := Rat.mul_le_mul_of_nonneg_right Hk (Rat.le_of_lt Hp0)
    rw [hid] at h
    exact h
  have HA : eps⁻¹ ≤ 1 + Qnat k * p := by grind
  have Hmul : Qpow (1 - p) k * eps⁻¹ ≤ 1 :=
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_left HA Hpow0)
      (geo_gap_bound p k (Rat.le_of_lt Hp0) Hp1)
  have hfin : Qpow (1 - p) k * eps⁻¹ * eps = Qpow (1 - p) k := by
    rw [Rat.mul_assoc, Rat.inv_mul_cancel eps Hene, Rat.mul_one]
  have h2 := Rat.mul_le_mul_of_nonneg_right Hmul (Rat.le_of_lt Heps)
  rw [hfin] at h2
  grind

/-- A tail only shrinks as the exponent grows. -/
theorem Qpow_le_exp (x : Rat) (n m : Nat) :
    0 ≤ x → x ≤ 1 → n ≤ m → Qpow x m ≤ Qpow x n := by
  intro Hx0 Hx1 Hnm
  induction Hnm with
  | refl => exact Rat.le_refl
  | @step m _ IH =>
    rw [Qpow_succ]
    have h1 := Rat.mul_le_mul_of_nonneg_right Hx1 (Qpow_nonneg x m Hx0)
    grind

/-- ... and so the depth the gap bound produces can be pushed as far out
as asked, which is what a certificate needs when something other than the
margin also has a say in how deep to go: replacing the `k` of
`geo_gap_small` by the larger of `k` and a floor keeps the bound and
clears the floor. -/
theorem geo_gap_small_above (p eps : Rat) (k0 : Nat) :
    0 < p → p ≤ 1 → 0 < eps → ∃ k : Nat, k0 ≤ k ∧ Qpow (1 - p) k ≤ eps := by
  intro Hp0 Hp1 Heps
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hp0 Hp1 Heps
  refine ⟨max k0 k, Nat.le_max_left k0 k, ?_⟩
  refine Rat.le_trans ?_ Hk
  exact Qpow_le_exp (1 - p) k (max k0 k) (by grind) (by grind) (Nat.le_max_right k0 k)

/-! ## The length-`< k` prefix family, and what it weighs -/

/-- Every standard input shorter than `k`: the length-`k'` slice, then
everything shorter.  The recursion is preferred to a flattened map over a
range because the sum below is then an induction on `k` with the
append law for `qsum` at each step. -/
def short_inputs : Nat → List (List byte)
  | 0 => []
  | k + 1 => byte_lists k ++ short_inputs k

/-- Its members have the lengths claimed. -/
theorem short_inputs_In_length (k : Nat) (s : List byte) :
    s ∈ short_inputs k → s.length < k := by
  induction k with
  | zero =>
    intro Hs
    exact absurd Hs List.not_mem_nil
  | succ k IH =>
    intro Hs
    rcases List.mem_append.mp Hs with Hs | Hs
    · have h := byte_lists_In_length k s Hs
      omega
    · have h := IH Hs
      omega

/-- ... and conversely it misses nothing shorter than `k`.  The witness
family does not need this — a witness only has to be admissible and to
weigh what is claimed — but `stdin_geometric_mass_not_attained` does: to
show a finite list falls short of the mass one has to place that list
inside the family. -/
theorem short_inputs_complete (k : Nat) (s : List byte) :
    s.length < k → s ∈ short_inputs k := by
  induction k with
  | zero =>
    intro Hlen
    exact absurd Hlen (Nat.not_lt_zero s.length)
  | succ k IH =>
    intro Hlen
    show s ∈ byte_lists k ++ short_inputs k
    refine List.mem_append.mpr ?_
    by_cases Heq : s.length = k
    · exact Or.inl (Heq ▸ byte_lists_complete s)
    · exact Or.inr (IH (by omega))

/-- ... and it repeats nothing: the two halves are duplicate-free
already, and they are disjoint because a member of the first has length
exactly `k'` while a member of the second is shorter. -/
theorem short_inputs_nodup (k : Nat) : (short_inputs k).Nodup := by
  induction k with
  | zero => exact List.nodup_nil
  | succ k IH =>
    show (byte_lists k ++ short_inputs k).Nodup
    refine List.nodup_append.mpr ⟨byte_lists_nodup k, IH, ?_⟩
    intro a Ha b Hb Heq
    subst Heq
    have h1 := byte_lists_In_length k a Ha
    have h2 := short_inputs_In_length k a Hb
    omega

/-- The witness family: over a fixed launch-time environment, one record
per standard input shorter than `k`.  Records rather than cores, because
the certificate is about the lists `Measure.weight_bound_T` quantifies
over; these records are not claimed valid and not claimed rejected by
anything. -/
def geo_lower_witness (argv envp : List (List byte)) (fs : Fs.Fs) (k : Nat) :
    List FinProcInput :=
  (short_inputs k).map (fun s => core_input (FinCore.mkFinCore argv envp fs s))

/-- The family's cores are the family's standard inputs under the fixed
environment. -/
theorem map_fin_core_geo_lower_witness (argv envp : List (List byte)) (fs : Fs.Fs)
    (k : Nat) :
    (geo_lower_witness argv envp fs k).map fin_core
      = (short_inputs k).map (FinCore.mkFinCore argv envp fs) := by
  simp only [geo_lower_witness, List.map_map]
  refine List.map_congr_left ?_
  intro s _
  exact fin_core_core_input (FinCore.mkFinCore argv envp fs s)

/-- The family is admissible: its cores repeat nothing, because the
standard inputs repeat nothing and the core determines its own standard
input. -/
theorem geo_lower_witness_nodup (argv envp : List (List byte)) (fs : Fs.Fs) (k : Nat) :
    ((geo_lower_witness argv envp fs k).map fin_core).Nodup := by
  rw [map_fin_core_geo_lower_witness]
  refine NoDup_map_inj _ _ ?_ (short_inputs_nodup k)
  intro x y _ _ Heq
  exact congrArg FinCore.core_stdin Heq

/-- The partial sum of the geometric series over lengths, as a recursion,
so that it is a rational a task can write down and not a limit. -/
def geo_prefix_sum (p : Rat) : Nat → Rat
  | 0 => 0
  | k + 1 => p * Qpow (1 - p) k + geo_prefix_sum p k

/-- The telescoping identity, with no side condition on `p`: the
arithmetic of the geometric sum is unconditional, and every hypothesis
the lower certificate attaches is attached for the other reason, choosing
a `k`. -/
theorem geo_prefix_sum_closed (p : Rat) (k : Nat) :
    geo_prefix_sum p k = 1 - Qpow (1 - p) k := by
  induction k with
  | zero =>
    show (0 : Rat) = 1 - Qpow (1 - p) 0
    rw [Qpow_0]
    grind
  | succ k IH =>
    show p * Qpow (1 - p) k + geo_prefix_sum p k = 1 - Qpow (1 - p) (k + 1)
    rw [IH, Qpow_succ]
    grind

/-- A full length-`n` slice weighs exactly `p * (1 - p) ^ n`: every core
in a slice weighs the same, and the count against the power of a
two-hundred-and-fifty-sixth cancels. -/
theorem qsum_full_slice (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (n : Nat) :
    qsum (geo_weight p argv envp fs)
        ((byte_lists n).map (FinCore.mkFinCore argv envp fs))
      = p * Qpow (1 - p) n := by
  have hc : ∀ c, c ∈ (byte_lists n).map (FinCore.mkFinCore argv envp fs) →
      geo_weight p argv envp fs c = geo_point p n := by
    intro c Hc
    rcases List.mem_map.mp Hc with ⟨s, Hin, rfl⟩
    rw [geo_weight_match, byte_lists_In_length n s Hin]
  rw [qsum_const _ _ _ hc, List.length_map, byte_lists_length]
  exact geo_slice_total p n

/-- ... and so the whole prefix family weighs the partial sum, block by
block.  Nothing is approximated here; the only inequality in the
certificate below is the choice of `k`. -/
theorem qsum_short_inputs (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (k : Nat) :
    qsum (geo_weight p argv envp fs)
        ((short_inputs k).map (FinCore.mkFinCore argv envp fs))
      = geo_prefix_sum p k := by
  induction k with
  | zero => rfl
  | succ k IH =>
    show qsum (geo_weight p argv envp fs)
        ((byte_lists k ++ short_inputs k).map (FinCore.mkFinCore argv envp fs))
      = p * Qpow (1 - p) k + geo_prefix_sum p k
    rw [List.map_append, qsum_app, IH, qsum_full_slice]

/-! ## The lower certificate for `stdin_geometric` -/

/-- The witness, at each `k`: an admissible list weighing exactly
`1 - (1 - p) ^ k`.  The target is not the declared mass because the mass
is not available — for `p < 1` the space holds infinitely many cores of
positive weight and every admissible list is finite.  What a list can do
is omit only the tail past length `k`, and that power is exactly that
tail.  No hypothesis beyond the constructor's own is needed: the equality
is unconditional arithmetic. -/
theorem stdin_geometric_mass_lower_witness (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ((geo_lower_witness argv envp fs k).map fin_core).Nodup
    ∧ core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
        (geo_lower_witness argv envp fs k) = 1 - Qpow (1 - p) k := by
  refine ⟨geo_lower_witness_nodup argv envp fs k, ?_⟩
  show core_sum (geo_weight p argv envp fs) (geo_lower_witness argv envp fs k)
    = 1 - Qpow (1 - p) k
  rw [core_sum_map_fin_core, map_fin_core_geo_lower_witness, qsum_short_inputs,
    geo_prefix_sum_closed]

/-- The same fact in the shape the certificate vocabulary uses: some
admissible list weighs the target.  Both forms are exported because they
are consumed differently. -/
theorem stdin_geometric_mass_lower_prefix (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
          = 1 - Qpow (1 - p) k :=
  ⟨geo_lower_witness argv envp fs k,
   stdin_geometric_mass_lower_witness p argv envp fs Hp0 Hp1 k⟩

/-- The lower certificate: for every margin there is an admissible list
weighing at least the declared mass minus that margin.  With the upper
certificate this is the honest pair: the declared one is the least upper
bound of the admissible partial sums, approached but never met.  `0 < p`
is a hypothesis of this lemma and not a tightening of the constructor —
moving it into `stdin_geometric` would invalidate every degenerate
distribution a consumer may already have built, and everything above this
lemma holds at `p = 0`.  Here it is used exactly once, inside
`geo_gap_small`, to choose the `k` whose tail is under the margin. -/
theorem stdin_geometric_mass_lower_certificate (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat) :
    0 < p → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) - eps
          ≤ core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l := by
  intro Hpos Heps
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hpos Hp1 Heps
  obtain ⟨l, Hnd, Hsum⟩ := stdin_geometric_mass_lower_prefix p argv envp fs Hp0 Hp1 k
  refine ⟨l, Hnd, ?_⟩
  have hM : cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) = 1 := rfl
  rw [Hsum, hM]
  grind

/-! ## ... and the mass is a supremum and not a maximum -/

/-- A list confined to standard inputs of length at most `n` weighs at
most the partial sum at its own horizon: it misses the tail, and the tail
is the whole point.  The proof reads the witness family in the other
direction — the cores of such a list, once the ones missing the fixed
launch-time environment are filtered away because they weigh nothing, all
lie in the length-`< n + 1` family.  Duplicate-freedom is where the
hypothesis is spent: without it a list may name one core repeatedly and
outweigh any enumeration of distinct cores. -/
theorem stdin_geometric_bound_by_max_length (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → f.fin_stdin.length ≤ n) →
    core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
      ≤ 1 - Qpow (1 - p) (n + 1) := by
  intro Hnd Hlen
  show core_sum (geo_weight p argv envp fs) l ≤ 1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  rw [qsum_filter (geo_weight p argv envp fs) (matches_env argv envp fs) (l.map fin_core)
      (fun c Hc => geo_weight_mismatch p argv envp fs c
        (matches_env_false argv envp fs c Hc))]
  refine Rat.le_trans
    (qsum_core_incl_le (geo_weight p argv envp fs) _
      ((short_inputs (n + 1)).map (FinCore.mkFinCore argv envp fs))
      (geo_weight_nonneg p argv envp fs Hp0 Hp1)
      (List.Nodup.sublist List.filter_sublist Hnd) ?_)
    ?_
  · intro c Hc
    rcases List.mem_filter.mp Hc with ⟨Hin, Hm⟩
    rcases List.mem_map.mp Hin with ⟨f, Hinl, Hf⟩
    subst Hf
    refine List.mem_map.mpr ⟨(fin_core f).core_stdin, ?_, ?_⟩
    · exact short_inputs_complete (n + 1) (fin_core f).core_stdin
        (Nat.lt_succ_of_le (Hlen f Hinl))
    · exact (matches_env_true argv envp fs (fin_core f) Hm).symm
  · rw [qsum_short_inputs, geo_prefix_sum_closed]
    exact Rat.le_refl

/-- ... and that bound is exactly tight, which makes the strictness below
a fact about the distribution and not an artefact of a lossy estimate:
the witness family at the horizon is a list of standard inputs of length
at most `n`, and it weighs the bound exactly. -/
theorem stdin_geometric_bound_by_max_length_attained (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    (∀ f, f ∈ geo_lower_witness argv envp fs (n + 1) → f.fin_stdin.length ≤ n)
    ∧ core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
        (geo_lower_witness argv envp fs (n + 1)) = 1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (stdin_geometric_mass_lower_witness p argv envp fs Hp0 Hp1 (n + 1)).2⟩
  intro f Hf
  simp only [geo_lower_witness] at Hf
  rcases List.mem_map.mp Hf with ⟨s, Hin, rfl⟩
  have h := short_inputs_In_length (n + 1) s Hin
  show s.length ≤ n
  omega

/-- The claim the certificate's shape rests on, mechanized: for `p < 1`
no admissible list weighs the declared mass — every one of them weighs
strictly less.  Read against the upper certificate and the lower one,
this is what makes the declared mass a supremum and not a maximum.  The
horizon is the list's own longest standard input, and the finiteness of
the lists `Measure.weight_bound_T` quantifies over is the only thing
needed: a list may be as long as it likes, but not infinite, so it has a
horizon, and beyond that horizon sits a positive tail it does not
collect. -/
theorem stdin_geometric_mass_not_attained (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
        < cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) := by
  intro Hlt l Hnd
  have hM : cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) = 1 := rfl
  rw [hM]
  have hlen : ∀ f, f ∈ l →
      f.fin_stdin.length ≤ list_max (l.map (fun g => g.fin_stdin.length)) := by
    intro f Hf
    exact list_max_ge (l.map (fun g => g.fin_stdin.length)) f.fin_stdin.length
      (List.mem_map.mpr ⟨f, Hf, rfl⟩)
  have hup := stdin_geometric_bound_by_max_length p argv envp fs Hp0 Hp1
    (list_max (l.map (fun g => g.fin_stdin.length))) l Hnd hlen
  have hpos : 0 < Qpow (1 - p)
      (list_max (l.map (fun g => g.fin_stdin.length)) + 1) :=
    Qpow_pos (1 - p) _ (by grind)
  grind

/-- The same fact under the name a reader looks for: the declared mass is
not attained.  Stated because "no admissible list weighs the mass" is how
the claim is used, and a consumer should not have to convert. -/
theorem stdin_geometric_mass_supremum_not_maximum (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      ¬ (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
          = cd_mass (stdin_geometric p argv envp fs Hp0 Hp1)) := by
  intro Hlt l Hnd
  exact Rat.ne_of_lt (stdin_geometric_mass_not_attained p argv envp fs Hp0 Hp1 Hlt l Hnd)

/-! ## Non-vacuity: the family, and why the certificate asks for a
positive stop weight -/

/-- The family at `k = 1` is the single stopping core over the empty
standard input, by conversion. -/
theorem geo_lower_witness_at_one (argv envp : List (List byte)) (fs : Fs.Fs) :
    geo_lower_witness argv envp fs 1
      = [core_input (FinCore.mkFinCore argv envp fs [])] := rfl

/-- ... and it weighs the stop weight exactly, which is what the abstract
form says at `k = 1`: this one core already carries that much of the
mass, and longer prefixes carry the rest. -/
theorem geo_lower_witness_at_one_weighs (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
        (geo_lower_witness argv envp fs 1) = p := by
  have h1 : Qpow (1 - p) 1 = (1 - p) * Qpow (1 - p) 0 := Qpow_succ (1 - p) 0
  rw [(stdin_geometric_mass_lower_witness p argv envp fs Hp0 Hp1 1).2, h1, Qpow_0]
  grind

/-- At stop weight zero every weight is zero: the degenerate member the
constructor deliberately still admits. -/
theorem geo_weight_zero_at_zero_p (argv envp : List (List byte)) (fs : Fs.Fs)
    (c : FinCore) : geo_weight 0 argv envp fs c = 0 := by
  unfold geo_weight
  split
  · unfold geo_point
    exact Rat.zero_mul _
  · rfl

/-- The strictness is load-bearing.  At stop weight zero every admissible
list weighs zero — not merely the witness family, which is why the first
conjunct quantifies over all of them — and the declared mass is still
one, so no list comes within a half of it.  The lower certificate is
therefore false there, and its hypothesis is not inherited caution.  The
upper certificate remains true, and that asymmetry is the honest content
of the pair. -/
theorem stdin_geometric_mass_lower_needs_positive (argv envp : List (List byte))
    (fs : Fs.Fs) :
    (∀ l : List FinProcInput,
        core_sum (cd_weight (stdin_geometric 0 argv envp fs Rat.le_refl Qle_0_1)) l = 0)
    ∧ ¬ (cd_mass (stdin_geometric 0 argv envp fs Rat.le_refl Qle_0_1) - 1/2 ≤ 0) := by
  constructor
  · intro l
    exact core_sum_zero_weight (geo_weight 0 argv envp fs) l
      (fun c => geo_weight_zero_at_zero_p argv envp fs c)
  · have hM : cd_mass (stdin_geometric 0 argv envp fs Rat.le_refl Qle_0_1) = 1 := rfl
    rw [hM]
    decide +kernel

/-! ## A worked distribution: named cores over a geometric background -/

/-- The worked task's argv: a program invoked as "wc".  Only argv is
given anything to look at, which makes it visible that these three are a
choice; they are the components `stdin_geometric` holds fixed, so their
content is irrelevant to every number below. -/
def worked_argv : List (List byte) := [[Z_to_bv 8 119, Z_to_bv 8 99]]

/-- The worked task's environment: empty. -/
def worked_envp : List (List byte) := []

/-- The worked task's file system: empty. -/
def worked_fs : Fs.Fs := []

/-- A core of this family: the fixed environment, and a standard input.
Every core named below goes through it, which puts the named cores inside
the geometric background's support rather than beside it. -/
def worked_core (s : List byte) : FinCore :=
  FinCore.mkFinCore worked_argv worked_envp worked_fs s

/-- The NUL byte. -/
def worked_nul : byte := Z_to_bv 8 0

/-- The byte "A". -/
def worked_byte_A : byte := Z_to_bv 8 65

/-- The empty standard input, as a core. -/
def worked_core_empty : FinCore := worked_core []

/-- The one-byte NUL standard input, as a core. -/
def worked_core_nul : FinCore := worked_core [worked_nul]

/-- NUL then "A", as a core.  It and `worked_core_nul` are what the fire
set will be, and they share the prefix the cylinder bound charges
against. -/
def worked_core_nul_a : FinCore := worked_core [worked_nul, worked_byte_A]

/-- Half the foreground on the empty input, a quarter on each
NUL-prefixed one: a declared foreground mass of one. -/
def worked_entries : List (FinCore × Rat) :=
  [(worked_core_empty, 1/2), (worked_core_nul, 1/4), (worked_core_nul_a, 1/4)]

/-- The entries are nonnegative, by the boolean scan. -/
theorem worked_entries_nonneg : ∀ e, e ∈ worked_entries → 0 ≤ e.2 :=
  entries_nonneg_of_forallb worked_entries (by decide +kernel)

/-- The foreground: the finite support on those three entries. -/
def worked_foreground : CoreDistribution :=
  finite_support worked_entries worked_entries_nonneg

/-- The background's stop weight.  An eighth is an authored choice: it
makes a typical standard input a few bytes long, and it is far enough
from both zero and one that neither degenerate case is exercised by
accident. -/
def worked_p : Rat := 1/8

/-- The stop weight is nonnegative. -/
theorem worked_p_nonneg : 0 ≤ worked_p := by decide +kernel

/-- The stop weight is at most one. -/
theorem worked_p_le_1 : worked_p ≤ 1 := by decide +kernel

/-- The background: the geometric standard input over the fixed
launch-time environment. -/
def worked_background : CoreDistribution :=
  stdin_geometric worked_p worked_argv worked_envp worked_fs worked_p_nonneg worked_p_le_1

/-- The named share, as a named fact: `cd_scale` takes the proof as an
argument, and a task author reading this sees what that costs. -/
theorem worked_share_named_nonneg : (0 : Rat) ≤ 1/4 := by decide +kernel

/-- The background share, likewise. -/
theorem worked_share_background_nonneg : (0 : Rat) ≤ 3/4 := by decide +kernel

/-- The distribution: a quarter on the named cores, three quarters on the
geometric background.  This is the probabilist's mixture written as two
scalings and one mixture, with how much of each and what to do with the
sum kept as separate, visible decisions. -/
def worked_cd : CoreDistribution :=
  cd_mix2 (cd_scale (1/4) worked_share_named_nonneg worked_foreground)
          (cd_scale (3/4) worked_share_background_nonneg worked_background)

/-- The foreground's declared mass is one: the three entries as
written. -/
theorem worked_foreground_mass : cd_mass worked_foreground = 1 := by decide +kernel

/-- The background's is one by `stdin_geometric`'s own declaration, since
the constructor writes the numeral. -/
theorem worked_background_mass : cd_mass worked_background = 1 := rfl

/-- ... so the mixture declares one, and the shares are what make it come
out that way.  The product of the multiplier and the total is therefore
the multiplier, which is why the demonstrations below quote a multiplier
and a bound as one number. -/
theorem worked_mass_is_one : cd_mass worked_cd = 1 := by
  show (1/4 : Rat) * cd_mass worked_foreground + 3/4 * cd_mass worked_background = 1
  rw [worked_foreground_mass, worked_background_mass]
  decide +kernel

/-- The distribution, over three combinators instead of one: the two
weight obligations are still discharged by the library's two lemmas, and
the nonnegativity of the total by composing the mass lemmas of exactly
the combinators the distribution was assembled from, with no arithmetic
written here.  Rocq ascribes a module to `DISTRIBUTION`; here the term
inhabits `Measure.Distribution`, so `Worked_D.w` and `Worked_D.M` are
field projections with the Rocq names. -/
def Worked_D : Measure.Distribution where
  w := cd_lift worked_cd
  M := cd_mass worked_cd
  w_nonneg := cd_lift_nonneg worked_cd
  M_nonneg :=
    cd_mix2_mass_nonneg _ _
      (cd_scale_mass_nonneg _ _ _
        (finite_support_mass_nonneg worked_entries worked_entries_nonneg))
      (cd_scale_mass_nonneg _ _ _
        (stdin_geometric_mass_nonneg worked_p worked_argv worked_envp worked_fs
          worked_p_nonneg worked_p_le_1))
  w_core_blind := cd_lift_core_blind worked_cd

/-! ## ... and the recipe for discharging the weight bound with it -/

/-- The fire set, as a predicate on cores.  Two cores named explicitly,
because the restriction has to compute and these two are what the entry
list names.  A larger support would use a predicate that describes the
set rather than listing it. -/
def worked_is_fire (c : FinCore) : Bool :=
  if c = worked_core_nul then true
  else if c = worked_core_nul_a then true else false

/-- The refinement's payoff, computed: the fire entries declare half
between them, against the support's own one.  Charging the fire set the
whole declared mass would double the foreground half of the bound for
nothing. -/
theorem worked_restricted_mass :
    entries_mass (entries_restrict worked_is_fire worked_entries) = 1/2 := by
  decide +kernel

/-- The ceiling, as an exact rational.  The two component bounds are a
restricted mass and a cylinder mass over the one-byte NUL prefix; scaled
by the two shares and added, they come to this number.  Stated before it
is used, so the number in the demonstrations is visibly what the
composition yields and not a convenient rounding of it. -/
theorem worked_fire_ceiling :
    (1/4 : Rat) * entries_mass (entries_restrict worked_is_fire worked_entries)
      + 3/4 * stdin_geometric_cylinder_mass worked_p [worked_nul] = 1045/8192 := by
  decide +kernel

/-- The recipe, steps two and three: every admissible list drawn from the
fire set weighs at most the ceiling.  Read the proof as the pattern to
copy — one mixture bound, one scaling bound per component, one library
bound under each.  Neither component bound is at a declared mass: the
foreground is charged the restricted mass and the background a cylinder
mass, and they compose anyway, because the two composition lemmas are
stated over arbitrary numbers.  The two side conditions are where the
fire set is spent: a fire core satisfies the boolean predicate, and a
fire core lies in the cylinder over the NUL prefix. -/
theorem worked_fire_bound (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) →
    core_sum (cd_weight worked_cd) l ≤ 1045/8192 := by
  intro Hnd Hfire
  rw [← worked_fire_ceiling]
  unfold worked_cd
  refine cd_mix2_bound _ _ l _ _ ?_ ?_
  · refine cd_scale_bound _ _ _ l _ ?_
    unfold worked_foreground
    refine finite_support_bound_subset worked_is_fire worked_entries
      worked_entries_nonneg l Hnd ?_
    intro f Hf
    rcases Hfire f Hf with Hc | Hc <;> rw [Hc] <;> decide +kernel
  · refine cd_scale_bound _ _ _ l _ ?_
    unfold worked_background
    refine stdin_geometric_bound worked_p worked_argv worked_envp worked_fs
      worked_p_nonneg worked_p_le_1 [worked_nul] l Hnd ?_
    intro f Hf
    rcases Hfire f Hf with Hc | Hc
    · exact ⟨[], Hc⟩
    · exact ⟨[worked_byte_A], Hc⟩

/-- The recipe, step four: from the library's bound to
`Measure.weight_bound_T` itself, at any multiplier the ceiling fits
under.  The bridge from the measure layer's sum to the library's is an
equality by conversion; the classifier hypothesis is spent turning "every
record in the list is rejected" into fire-set membership; and
`worked_mass_is_one` turns the product of multiplier and total into the
multiplier.  Quantifying over the multiplier rather than fixing one makes
the two demonstrations below a single proof, and puts the ceiling where a
reader can see it. -/
theorem worked_weight_bound_T_of (C : Image) (b : Rat) :
    (∀ f, rejects C f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) →
    1045/8192 ≤ b →
    weight_bound_T C Worked_D.w Worked_D.M b := by
  intro Hfire Hb l Hnd Hrej
  have H : core_sum (cd_weight worked_cd) l ≤ 1045/8192 :=
    worked_fire_bound l Hnd (fun f Hf => Hfire f (Hrej f Hf))
  have Hgoal : core_sum (cd_weight worked_cd) l ≤ b * cd_mass worked_cd := by
    rw [worked_mass_is_one]
    refine Rat.le_trans H ?_
    grind
  exact Hgoal

/-- Demonstration one, at a round multiplier a task would plausibly
declare: a classifier whose reject set is this fire set carries at most a
quarter of the distribution's mass. -/
theorem worked_weight_bound_T_quarter (C : Image) :
    (∀ f, rejects C f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) →
    weight_bound_T C Worked_D.w Worked_D.M (1/4) := by
  intro Hfire
  exact worked_weight_bound_T_of C (1/4) Hfire (by decide +kernel)

/-- Demonstration two, at the tightest multiplier these bounds reach.
The same recipe, and the arithmetic step has become reflexivity, which is
the honest way to say there is nothing left to give away here.  Where the
remaining slack is, and why it is not zero, is `worked_ceiling_slack`. -/
theorem worked_weight_bound_T_ceiling (C : Image) :
    (∀ f, rejects C f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) →
    weight_bound_T C Worked_D.w Worked_D.M (1045/8192) := by
  intro Hfire
  exact worked_weight_bound_T_of C (1045/8192) Hfire Rat.le_refl

/-- The fire set as an admissible list: one canonical record per fire
core.  As everywhere else in this file these records are not claimed
valid and not claimed rejected by anything. -/
def worked_fire_list : List FinProcInput :=
  [worked_core_nul, worked_core_nul_a].map core_input

/-- How much of the ceiling is real.  The fire set's own two records form
an admissible list and weigh a shade over ninety-eight per cent of what
the composition charges, strictly under it.  Three conjuncts, each
load-bearing: the list is admissible, so the comparison is between
comparable things; the weight is exact, on literals this file wrote; and
the ceiling is not attained, so the route does carry slack.  All of that
slack is in the background half — the cylinder over the NUL prefix holds
every core whose standard input begins with a NUL byte, the fire set
names two of them, and every other continuation is charged for and
absent.  This measures the route's slack, which is a property of the
proof and not of the distribution. -/
theorem worked_ceiling_slack :
    (worked_fire_list.map fin_core).Nodup
    ∧ core_sum (cd_weight worked_cd) worked_fire_list = 16820371/134217728
    ∧ ¬ ((1045 : Rat)/8192 ≤ 16820371/134217728) := by
  refine ⟨?_, ?_, ?_⟩
  · show (([worked_core_nul, worked_core_nul_a].map core_input).map fin_core).Nodup
    rw [map_fin_core_core_input]
    decide +kernel
  · decide +kernel
  · decide +kernel

/-! ## The same recipe, indexed by a predicate instead of a classifier -/

/-- The predicate twin of `worked_weight_bound_T_of`, and the whole of
what changes: the classifier's reject set becomes validity together with
falling outside the predicate.  Nothing else in the recipe moves, because
the classifier never entered the arithmetic — it entered as one
hypothesis, and this is that hypothesis rewritten.  Its use is the gated
size measure's per-slice bound, where a slice is a predicate on records
and not a classifier's reject set. -/
theorem worked_weight_bound_pred_T_of (P : FinProcInput → Prop) (b : Rat) :
    (∀ f, valid_fin_input f → ¬ P f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) →
    1045/8192 ≤ b →
    GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M b := by
  intro Hfire Hb
  have H : GatedSize.weight_bound_pred_T P (cd_lift worked_cd) (cd_mass worked_cd) b := by
    refine weight_bound_pred_T_of_core_bound worked_cd P
      (fun c => c = worked_core_nul ∨ c = worked_core_nul_a) (1045/8192) b Hfire
      (fun l Hnd Hall => worked_fire_bound l Hnd Hall) ?_
    rw [worked_mass_is_one]
    grind
  exact H

/-- The predicate twin of `worked_weight_bound_T_quarter`: the same round
multiplier, over a slice predicate instead of a classifier. -/
theorem worked_weight_bound_pred_T_quarter (P : FinProcInput → Prop) :
    (∀ f, valid_fin_input f → ¬ P f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) →
    GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M (1/4) := by
  intro Hfire
  exact worked_weight_bound_pred_T_of P (1/4) Hfire (by decide +kernel)

/-- A core the fire set does not name: the standard input "A", which does
not begin with a NUL byte and is not one of the entries.  Together with
the empty-input core, which the entries do name and the fire set still
leaves out, it is what the pin below is built from. -/
def worked_core_a : FinCore := worked_core [worked_byte_A]

/-- Two records whose cores are outside the fire set, as an admissible
list.  As at `worked_fire_list`, these are not claimed valid and not
claimed outside anything. -/
def worked_off_fire_list : List FinProcInput :=
  [worked_core_empty, worked_core_a].map core_input

/-- The fire-set hypothesis is load-bearing.  Three conjuncts: the list
is admissible, so it is one of the lists the obligation quantifies over;
neither core is a fire core, computed through the predicate itself rather
than argued in prose; and the two together weigh more than the ceiling.
So dropping the hypothesis makes the conclusion false at the ceiling.
This is the negative half the classifier-indexed recipe never had, and it
is available here because a predicate's complement is something a reader
can name two members of. -/
theorem worked_off_fire_exceeds_the_ceiling :
    (worked_off_fire_list.map fin_core).Nodup
    ∧ (worked_is_fire worked_core_empty = false ∧ worked_is_fire worked_core_a = false)
    ∧ ¬ (core_sum (cd_weight worked_cd) worked_off_fire_list ≤ 1045/8192) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · show (([worked_core_empty, worked_core_a].map core_input).map fin_core).Nodup
    rw [map_fin_core_core_input]
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- ... and the pin cashed in as a refutation of the twin's conclusion.
Two valid records outside the predicate whose cores are the two the fire
set leaves out refute the bound at the ceiling, so the twin's hypothesis
is not free: a predicate whose complement reaches either core cannot
satisfy it.  Validity is a hypothesis rather than a claim about the
canonical record, because nothing here asserts that a fabricated record
is a launch a kernel could have performed, and a refutation naming an
invalid record would refute nothing. -/
theorem worked_weight_bound_pred_T_needs_the_fire_set (P : FinProcInput → Prop)
    (f1 f2 : FinProcInput) :
    valid_fin_input f1 → ¬ P f1 → fin_core f1 = worked_core_empty →
    valid_fin_input f2 → ¬ P f2 → fin_core f2 = worked_core_a →
    ¬ GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M (1045/8192) := by
  intro Hv1 Hnp1 Hc1 Hv2 Hnp2 Hc2 Hbound
  have Hnd : ([f1, f2].map fin_core).Nodup := by
    show [fin_core f1, fin_core f2].Nodup
    rw [Hc1, Hc2]
    decide +kernel
  have Hall : ∀ f, f ∈ [f1, f2] → valid_fin_input f ∧ ¬ P f := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨Hv1, Hnp1⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨Hv2, Hnp2⟩
      · exact absurd hf List.not_mem_nil
  have H : sum_weights (cd_lift worked_cd) [f1, f2] ≤ 1045/8192 * cd_mass worked_cd :=
    Hbound [f1, f2] Hnd Hall
  rw [← core_sum_cd_lift, core_sum_cons, core_sum_cons, core_sum_nil, Hc1, Hc2,
    worked_mass_is_one] at H
  exact absurd H (by decide +kernel)

/-! ## The standard-input enumerations, read off the cores -/

/-- The cylinder enumeration with the launch-time environment forgotten:
the standard inputs that extend `bs` by at most `N` bytes, as byte lists.
The environment-varying family cannot use the core enumeration directly,
because a core there is a pair of an environment and a standard input and
the two coordinates have to be enumerated apart.  What is deliberately
not done here is to prove the cancellation a second time. -/
def bytes_cyl : List byte → Nat → List (List byte)
  | bs, 0 => [bs]
  | bs, N + 1 => bs :: all_bytes.flatMap (fun b => bytes_cyl (bs ++ [b]) N)

/-- The two enumerations are the same list under the core
constructor. -/
theorem cyl_enum_bytes_cyl (argv envp : List (List byte)) (fs : Fs.Fs) (N : Nat)
    (bs : List byte) :
    cyl_enum argv envp fs bs N
      = (bytes_cyl bs N).map (FinCore.mkFinCore argv envp fs) := by
  induction N generalizing bs with
  | zero => rfl
  | succ N IH =>
    have h : (fun b => cyl_enum argv envp fs (bs ++ [b]) N)
        = (fun b => (bytes_cyl (bs ++ [b]) N).map (FinCore.mkFinCore argv envp fs)) :=
      funext (fun b => IH (bs ++ [b]))
    simp only [cyl_enum, bytes_cyl, List.map_cons, map_flat_map_comm, h]

/-- The byte-list enumeration misses nothing within its depth. -/
theorem bytes_cyl_In (N : Nat) (bs ext : List byte) :
    ext.length ≤ N → (bs ++ ext) ∈ bytes_cyl bs N := by
  intro Hlen
  have Hin := cyl_enum_complete [] [] [] N bs ext Hlen
  rw [cyl_enum_bytes_cyl] at Hin
  rcases List.mem_map.mp Hin with ⟨s, Hins, Hs⟩
  have hs : s = bs ++ ext := congrArg FinCore.core_stdin Hs
  rw [← hs]
  exact Hins

/-- The cylinder sum, transported off the cores: the enumeration is a map
of the core constructor, the map law strips it off, and the weight turns
back into the point weight it was built from. -/
theorem bytes_cyl_sum_le (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (N : Nat)
    (bs : List byte) :
    qsum (fun s => geo_point p s.length) (bytes_cyl bs N) ≤ geo_mass p bs.length := by
  refine Rat.le_trans (Qle_of_Qeq _ _ ?_) (cyl_enum_sum_le p [] [] [] Hp0 Hp1 N bs)
  rw [cyl_enum_bytes_cyl, qsum_map]
  exact qsum_ext _ _ _ (fun s _ => (geo_weight_match p [] [] [] s).symm)

/-- The length-`< k` prefix family's sum, transported the same way. -/
theorem short_inputs_sum (p : Rat) (k : Nat) :
    qsum (fun s => geo_point p s.length) (short_inputs k) = geo_prefix_sum p k := by
  rw [← qsum_short_inputs p [] [] [] k, qsum_map]
  exact qsum_ext _ _ _ (fun s _ => (geo_weight_match p [] [] [] s).symm)

/-- One full length slice's sum, transported the same way. -/
theorem byte_lists_sum (p : Rat) (n : Nat) :
    qsum (fun s => geo_point p s.length) (byte_lists n) = p * Qpow (1 - p) n := by
  rw [← qsum_full_slice p [] [] [] n, qsum_map]
  exact qsum_ext _ _ _ (fun s _ => (geo_weight_match p [] [] [] s).symm)

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
