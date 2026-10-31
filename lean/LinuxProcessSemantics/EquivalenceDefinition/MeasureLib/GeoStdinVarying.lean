-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058

# EquivalenceDefinition.MeasureLib.GeoStdinVarying

Holds Rocq `theories/EquivalenceDefinition/MeasureLib.v` lines 5260-7100:
the combinator for geometric standard input over a VARYING launch-time
environment.  The environment carries mass here, so a core whose envp is
not the canonical one still weighs something; that is the gap this family
closes against `stdin_geometric`, which weighs such a core zero.  The span
contains the weight and its distribution, the two-coordinate cylinder
bound and the exports built on it, the environment witness family with its
margin arithmetic and lower certificate, and the non-vacuity blocks at
Rocq lines 6727-6842 and 6843-7100 that pin where each side condition is
spent. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Measure

/-- Two factors multiplied, each between its own bounds.  Rocq spends
`QArith`'s `Qmult_le_compat_nonneg` here; core Lean has no such lemma, so
it is assembled from the two one-sided monotonicity rules.  Private: every
span that needs it assembles its own, and one name in the shared namespace
would be two declarations. -/
private theorem mul_le_mul_nonneg {a b c d : Rat} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) : a * c ≤ b * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hcd ha)
    (Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans hc hcd))

/-! ## The per-entry and per-environment weights -/

/-- The per-entry half of the weight: the product, over the environment's
entries, of the byte-geometric weight of each entry's own length. -/
def entries_geo_product (q : Rat) : List (List byte) → Rat
  | [] => 1
  | e :: es' => geo_point q e.length * entries_geo_product q es'

/-- The mass of the environments extending a given list of entries.
Continuing past an entry costs `1 - r` and the entry itself costs its
byte-geometric weight, so this is the running product of those. -/
def envp_factor (r q : Rat) : List (List byte) → Rat
  | [] => 1
  | e :: es' => (1 - r) * geo_point q e.length * envp_factor r q es'

/-- The weight of the environment that stops at `es`: `r` times the mass
of the environments extending it, the `r` being the weight of stopping. -/
def envp_point (r q : Rat) (es : List (List byte)) : Rat :=
  r * envp_factor r q es

/-- The factor as a power of `1 - r` times the per-entry product. -/
theorem envp_factor_closed_form (r q : Rat) (es : List (List byte)) :
    envp_factor r q es = Qpow (1 - r) es.length * entries_geo_product q es := by
  induction es with
  | nil =>
    simp only [envp_factor, entries_geo_product, List.length_nil, Qpow_0]
    grind
  | cons e es ih =>
    simp only [envp_factor, entries_geo_product, List.length_cons, Qpow_succ, ih]
    grind

/-- The three-factor form the family is specified with:
`r * (1 - r) ^ k * Prod_i geo_point q |e_i|`. -/
theorem envp_point_closed_form (r q : Rat) (es : List (List byte)) :
    envp_point r q es = r * Qpow (1 - r) es.length * entries_geo_product q es := by
  unfold envp_point
  rw [envp_factor_closed_form]
  grind

/-- Extending the prefix multiplies the factor. -/
theorem envp_factor_app (r q : Rat) (es es' : List (List byte)) :
    envp_factor r q (es ++ es') = envp_factor r q es * envp_factor r q es' := by
  induction es with
  | nil => simp only [List.nil_append, envp_factor]; grind
  | cons e es ih => simp only [List.cons_append, envp_factor, ih]; grind

/-- One entry's factor, written out. -/
theorem envp_factor_one (r q : Rat) (e : List byte) :
    envp_factor r q [e] = (1 - r) * geo_point q e.length := by
  simp only [envp_factor]
  grind

/-- Nonnegativity: `r ≤ 1` makes the continuation factor nonnegative, and
`0 ≤ q ≤ 1` is what the per-entry weight asks. -/
theorem envp_factor_nonneg (r q : Rat) : r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ es : List (List byte), 0 ≤ envp_factor r q es := by
  intro Hr1 Hq0 Hq1 es
  induction es with
  | nil => simp only [envp_factor]; exact Qle_0_1
  | cons e es ih =>
    simp only [envp_factor]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by grind) (geo_point_nonneg q e.length Hq0 Hq1)) ih

/-- The stopping weight is nonnegative too. -/
theorem envp_point_nonneg (r q : Rat) : 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ es : List (List byte), 0 ≤ envp_point r q es := by
  intro Hr0 Hr1 Hq0 Hq1 es
  unfold envp_point
  exact Rat.mul_nonneg Hr0 (envp_factor_nonneg r q Hr1 Hq0 Hq1 es)

/-- One environment weighs at most the mass of the environments extending
it, because `r ≤ 1`. -/
theorem envp_point_le_factor (r q : Rat) : r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ es : List (List byte), envp_point r q es ≤ envp_factor r q es := by
  intro Hr1 Hq0 Hq1 es
  have hF : 0 ≤ envp_factor r q es := envp_factor_nonneg r q Hr1 Hq0 Hq1 es
  have h : r * envp_factor r q es ≤ 1 * envp_factor r q es :=
    Rat.mul_le_mul_of_nonneg_right Hr1 hF
  unfold envp_point
  grind

/-! ## The weight and its distribution -/

/-- THE WEIGHT.  Zero unless the core's argv and file system are the fixed
ones; otherwise the environment's weight times the standard-input weight
of its own length.  `geo_weight` fixes envp too and therefore weighs zero
at every core whose launch-time environment differs; here the environment
carries mass. -/
def envp_geo_weight (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (c : FinCore) : Rat :=
  if c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin then
    envp_point r q c.core_envp * geo_point p c.core_stdin.length
  else 0

/-- Its value at a core of the family. -/
theorem envp_geo_weight_match (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (es : List (List byte)) (s : List byte) :
    envp_geo_weight p r q argv fs (FinCore.mkFinCore argv es fs s)
      = envp_point r q es * geo_point p s.length := by
  unfold envp_geo_weight
  split
  · rfl
  · next h => exact absurd rfl h

/-- Its value off the fixed argv and file system. -/
theorem envp_geo_weight_mismatch (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (c : FinCore) :
    c ≠ FinCore.mkFinCore argv c.core_envp fs c.core_stdin →
    envp_geo_weight p r q argv fs c = 0 := by
  intro h
  unfold envp_geo_weight
  split
  · next h' => exact absurd h' h
  · rfl

/-- The family's formula, all six factors visible at once: entry-count
geometric in `r`, per-entry byte-geometric in `q`, and the standard-input
geometric in `p`. -/
theorem envp_geo_weight_closed_form (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (es : List (List byte)) (s : List byte) :
    envp_geo_weight p r q argv fs (FinCore.mkFinCore argv es fs s)
      = r * Qpow (1 - r) es.length * entries_geo_product q es
        * (p * Qpow (1 - p) s.length * Qpow (1 / 256) s.length) := by
  rw [envp_geo_weight_match, envp_point_closed_form, geo_point_closed_form]

/-- The weight is nonnegative at every core, given the six bounds. -/
theorem envp_geo_weight_nonneg (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs) :
    0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ c, 0 ≤ envp_geo_weight p r q argv fs c := by
  intro Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 c
  unfold envp_geo_weight
  split
  · exact Rat.mul_nonneg (envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 _)
      (geo_point_nonneg p _ Hp0 Hp1)
  · exact Rat.le_refl

/-- THE DISTRIBUTION.  Mass `1` is declared, as everywhere in this
library; `stdin_envp_geometric_mass_upper` below is the proof that owes
something to it.  None of the three strict inequalities is demanded: the
lower certificate that needs them asks for them in its own statement. -/
def stdin_envp_geometric (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) : CoreDistribution :=
  CoreDistribution.mkCoreDistribution (envp_geo_weight p r q argv fs) 1
    (envp_geo_weight_nonneg p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)

/-! ## The envp cylinder, and the enumeration that bounds it -/

/-- Every environment extending `es` by at most `M` further entries, each
of them shorter than `L`.  It is `cyl_enum` one level up: the stopping
environment, then for each admissible entry the environments one entry
deeper.  `short_inputs L` is the same length-bounded enumeration of byte
lists the geometric lower certificate already uses. -/
def envp_enum : List (List byte) → Nat → Nat → List (List (List byte))
  | es, 0, _ => [es]
  | es, M + 1, L => es :: (short_inputs L).flatMap (fun e => envp_enum (es ++ [e]) M L)

/-- It misses nothing within its two depths. -/
theorem envp_enum_complete (M L : Nat) (es rest : List (List byte)) :
    rest.length ≤ M → (∀ e ∈ rest, e.length < L) →
    (es ++ rest) ∈ envp_enum es M L := by
  induction M generalizing es rest with
  | zero =>
    intro Hlen _
    cases rest with
    | nil => simp [envp_enum]
    | cons e rest => simp only [List.length_cons] at Hlen; omega
  | succ M ih =>
    intro Hlen Hent
    cases rest with
    | nil => simp [envp_enum]
    | cons e rest =>
      refine List.mem_cons_of_mem _ ?_
      rw [List.mem_flatMap]
      refine ⟨e, short_inputs_complete L e (Hent e (by simp)), ?_⟩
      have happ : es ++ e :: rest = (es ++ [e]) ++ rest := by simp
      rw [happ]
      refine ih (es ++ [e]) rest ?_ ?_
      · simp only [List.length_cons] at Hlen; omega
      · intro x hx; exact Hent x (List.mem_cons_of_mem _ hx)

/-- ONE STEP OF THE ENVP CANCELLATION, as an exact identity: the
environments one entry deeper than `es` carry, between them, the factor of
`es` times `1 - r` times what the entry enumeration itself weighs. -/
theorem qsum_envp_factor_step (r q : Rat) (es : List (List byte)) (L : Nat) :
    qsum (fun e => envp_factor r q (es ++ [e])) (short_inputs L)
      = envp_factor r q es * (1 - r) * (1 - Qpow (1 - q) L) := by
  rw [qsum_ext (fun e => envp_factor r q (es ++ [e]))
        (fun e => envp_factor r q es * (1 - r) * geo_point q e.length)
        (short_inputs L)
        (by intro e _; rw [envp_factor_app, envp_factor_one]; grind)]
  rw [qsum_scale (envp_factor r q es * (1 - r)) (fun e => geo_point q e.length)
        (short_inputs L)]
  rw [short_inputs_sum, geo_prefix_sum_closed]

/-- THE CANCELLATION on the envp coordinate: the whole enumeration weighs
no more than the mass of the environments extending `es`.  The
continuations are charged what their own entry costs and their total is
`1 - (1 - q) ^ L`, which is under `1` rather than equal to it: an entry
longer than `L` is a continuation the enumeration omits. -/
theorem envp_enum_sum_le (r q : Rat) : 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ (M L : Nat) (es : List (List byte)),
      qsum (envp_point r q) (envp_enum es M L) ≤ envp_factor r q es := by
  intro Hr0 Hr1 Hq0 Hq1 M L
  induction M with
  | zero =>
    intro es
    have h := envp_point_le_factor r q Hr1 Hq0 Hq1 es
    simp only [envp_enum, qsum_cons, qsum_nil]
    grind
  | succ M ih =>
    intro es
    have hstep : qsum (envp_point r q)
        ((short_inputs L).flatMap (fun e => envp_enum (es ++ [e]) M L))
        ≤ envp_factor r q es * (1 - r) * (1 - Qpow (1 - q) L) := by
      rw [← qsum_envp_factor_step r q es L]
      exact qsum_flat_map_le (envp_point r q) (fun e => envp_enum (es ++ [e]) M L)
        (fun e => envp_factor r q (es ++ [e])) (short_inputs L)
        (fun e _ => ih (es ++ [e]))
    have hFnn : 0 ≤ envp_factor r q es := envp_factor_nonneg r q Hr1 Hq0 Hq1 es
    have hFr : 0 ≤ envp_factor r q es * (1 - r) := Rat.mul_nonneg hFnn (by grind)
    have hXnn : 0 ≤ Qpow (1 - q) L := Qpow_nonneg (1 - q) L (by grind)
    have hX : (1 : Rat) - Qpow (1 - q) L ≤ 1 := by grind
    have h2 : envp_factor r q es * (1 - r) * (1 - Qpow (1 - q) L)
        ≤ envp_factor r q es * (1 - r) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hX hFr
    have hp : envp_point r q es = r * envp_factor r q es := rfl
    simp only [envp_enum, qsum_cons]
    grind

/-! ## The two coordinates, recombined -/

/-- Every core over the fixed argv and file system whose environment comes
from `A` and whose standard input comes from `B`.  A core of this family is
a pair, and the weight is one factor per coordinate, so the enumeration is
the product of the two coordinates' enumerations. -/
def envp_stdin_product (argv : List (List byte)) (fs : Fs.Fs)
    (A : List (List (List byte))) (B : List (List byte)) : List FinCore :=
  A.flatMap (fun es => B.map (FinCore.mkFinCore argv es fs))

/-- A pair drawn from the two coordinates is in the product. -/
theorem In_envp_stdin_product (argv : List (List byte)) (fs : Fs.Fs)
    (A : List (List (List byte))) (B : List (List byte))
    (es : List (List byte)) (s : List byte) :
    es ∈ A → s ∈ B →
    FinCore.mkFinCore argv es fs s ∈ envp_stdin_product argv fs A B := by
  intro HA HB
  unfold envp_stdin_product
  rw [List.mem_flatMap]
  exact ⟨es, HA, List.mem_map_of_mem HB⟩

/-- One block of the product: the standard inputs under a fixed
environment weigh what they weigh, scaled by the environment's weight. -/
theorem qsum_envp_geo_block (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (es : List (List byte)) (B : List (List byte)) :
    qsum (envp_geo_weight p r q argv fs) (B.map (FinCore.mkFinCore argv es fs))
      = qsum (fun s => geo_point p s.length) B * envp_point r q es := by
  rw [qsum_map]
  rw [qsum_ext (fun s => envp_geo_weight p r q argv fs (FinCore.mkFinCore argv es fs s))
        (fun s => envp_point r q es * geo_point p s.length) B
        (fun s _ => envp_geo_weight_match p r q argv fs es s)]
  rw [qsum_scale (envp_point r q es) (fun s => geo_point p s.length) B]
  grind

/-- The sum over the product is the product of the two coordinates' sums.
That identity is what lets every bound below be assembled from an envp
bound and a standard-input bound proved apart. -/
theorem qsum_envp_stdin_product (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (A : List (List (List byte))) (B : List (List byte)) :
    qsum (envp_geo_weight p r q argv fs) (envp_stdin_product argv fs A B)
      = qsum (envp_point r q) A * qsum (fun s => geo_point p s.length) B := by
  unfold envp_stdin_product
  rw [qsum_flat_map]
  rw [qsum_ext
        (fun es => qsum (envp_geo_weight p r q argv fs)
                     (B.map (FinCore.mkFinCore argv es fs)))
        (fun es => qsum (fun s => geo_point p s.length) B * envp_point r q es) A
        (fun es _ => qsum_envp_geo_block p r q argv fs es B)]
  rw [qsum_scale (qsum (fun s => geo_point p s.length) B) (envp_point r q) A]
  grind

/-- The product of two duplicate-free enumerations repeats nothing: a core
determines its standard input inside a block and its environment across
blocks. -/
theorem NoDup_envp_stdin_product (argv : List (List byte)) (fs : Fs.Fs)
    (A : List (List (List byte))) (B : List (List byte)) :
    A.Nodup → B.Nodup → (envp_stdin_product argv fs A B).Nodup := by
  intro HA HB
  unfold envp_stdin_product
  refine NoDup_flat_map _ _ HA ?_ ?_
  · intro es _
    refine NoDup_map_inj _ _ ?_ HB
    intro x y _ _ Heq
    exact congrArg FinCore.core_stdin Heq
  · intro es1 es2 c _ _ H1 H2
    obtain ⟨s1, _, Hs1⟩ := List.mem_map.mp H1
    obtain ⟨s2, _, Hs2⟩ := List.mem_map.mp H2
    exact congrArg FinCore.core_envp (Hs1.trans Hs2.symm)

/-! ## The three depths, read off the task's own list -/

/-- How many entries the longest environment in the list has. -/
def cores_envp_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => c.core_envp.length))

/-- One past the longest entry in any environment in the list.  It is a
successor because `short_inputs` enumerates the byte lists STRICTLY
shorter than its argument. -/
def cores_entry_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => list_max (c.core_envp.map (fun e => e.length)))) + 1

/-- How long the longest standard input in the list is. -/
def cores_stdin_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => c.core_stdin.length))

/-- Every member's environment is within the entry-count depth. -/
theorem cores_envp_depth_ge (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_envp.length ≤ cores_envp_depth cs := by
  intro Hc
  exact list_max_ge _ _ (List.mem_map_of_mem Hc)

/-- Every member's entries are shorter than the entry depth. -/
theorem cores_entry_depth_gt (cs : List FinCore) (c : FinCore) (e : List byte) :
    c ∈ cs → e ∈ c.core_envp → e.length < cores_entry_depth cs := by
  intro Hc He
  unfold cores_entry_depth
  have Hinner : e.length ≤ list_max (c.core_envp.map (fun x => x.length)) :=
    list_max_ge _ _ (List.mem_map_of_mem He)
  have Houter : list_max (c.core_envp.map (fun x => x.length))
      ≤ list_max (cs.map (fun c0 => list_max (c0.core_envp.map (fun x => x.length)))) :=
    list_max_ge _ _ (List.mem_map_of_mem Hc)
  omega

/-- Every member's standard input is within the standard-input depth. -/
theorem cores_stdin_depth_ge (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_stdin.length ≤ cores_stdin_depth cs := by
  intro Hc
  exact list_max_ge _ _ (List.mem_map_of_mem Hc)

/-! ## The cylinder bound over cores -/

/-- The cores this bound is about: the fixed argv and file system, an
environment extending `es` and a standard input extending `bs`. -/
def in_envp_stdin_cylinder (argv : List (List byte)) (fs : Fs.Fs)
    (es : List (List byte)) (bs : List byte) (c : FinCore) : Prop :=
  ∃ eext ext, c = FinCore.mkFinCore argv (es ++ eext) fs (bs ++ ext)

/-- The cylinder's mass: the product of what the two coordinates
contribute. -/
def stdin_envp_geometric_cylinder_mass (p r q : Rat)
    (es : List (List byte)) (bs : List byte) : Rat :=
  envp_factor r q es * geo_mass p bs.length

/-- The cylinder mass written out as the four powers the specification
quotes. -/
theorem stdin_envp_geometric_cylinder_mass_closed_form (p r q : Rat)
    (es : List (List byte)) (bs : List byte) :
    stdin_envp_geometric_cylinder_mass p r q es bs
      = Qpow (1 - r) es.length * entries_geo_product q es
        * (Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length) := by
  unfold stdin_envp_geometric_cylinder_mass
  rw [envp_factor_closed_form, geo_mass_closed_form]

/-- THE BOUND OVER CORES: any duplicate-free list of cores lying in the
cylinder weighs at most the cylinder's mass.  Three enumeration depths are
read off the list, the product of the two coordinates' enumerations
contains it, and each factor has its own bound already. -/
theorem envp_geo_weight_cylinder_bound (p r q : Rat) (argv : List (List byte))
    (fs : Fs.Fs) :
    0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ (es : List (List byte)) (bs : List byte) (cs : List FinCore),
      cs.Nodup →
      (∀ c ∈ cs, in_envp_stdin_cylinder argv fs es bs c) →
      qsum (envp_geo_weight p r q argv fs) cs
        ≤ stdin_envp_geometric_cylinder_mass p r q es bs := by
  intro Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs cs Hnd Hcyl
  have hincl : cs ⊆ envp_stdin_product argv fs
      (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
      (bytes_cyl bs (cores_stdin_depth cs)) := by
    intro c Hc
    obtain ⟨eext, ext, Heq⟩ := Hcyl c Hc
    have Henvp := cores_envp_depth_ge cs c Hc
    have Hstdin := cores_stdin_depth_ge cs c Hc
    rw [Heq] at Henvp Hstdin
    simp only [List.length_append] at Henvp Hstdin
    rw [Heq]
    refine In_envp_stdin_product argv fs _ _ (es ++ eext) (bs ++ ext) ?_ ?_
    · refine envp_enum_complete _ _ es eext (by omega) ?_
      intro e he
      refine cores_entry_depth_gt cs c e Hc ?_
      rw [Heq]
      exact List.mem_append_right _ he
    · exact bytes_cyl_In _ bs ext (by omega)
  have hprod := qsum_core_incl_le (envp_geo_weight p r q argv fs) cs _
    (envp_geo_weight_nonneg p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd hincl
  rw [qsum_envp_stdin_product] at hprod
  have hA0 : 0 ≤ qsum (envp_point r q)
      (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs)) :=
    qsum_nonneg _ _ (fun x _ => envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 x)
  have hB0 : 0 ≤ qsum (fun s => geo_point p s.length)
      (bytes_cyl bs (cores_stdin_depth cs)) :=
    qsum_nonneg _ _ (fun x _ => geo_point_nonneg p x.length Hp0 Hp1)
  have hmul := mul_le_mul_nonneg hA0
    (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ es) hB0
    (bytes_cyl_sum_le p Hp0 Hp1 _ bs)
  unfold stdin_envp_geometric_cylinder_mass
  exact Rat.le_trans hprod hmul

/-! ## The envp-varying family's exports -/

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in
the cylinder over an environment prefix and a standard-input prefix,
weighs at most that cylinder's mass.  A fire set described by "the
environment begins with these entries and standard input begins with these
bytes" is charged a number that depends on the environment. -/
theorem stdin_envp_geometric_bound (p r q : Rat) (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (es : List (List byte)) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_envp_stdin_cylinder argv fs es bs (fin_core f)) →
    core_sum (cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ stdin_envp_geometric_cylinder_mass p r q es bs := by
  intro Hnd Hcyl
  have hw : cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = envp_geo_weight p r q argv fs := rfl
  rw [hw, core_sum_map_fin_core]
  refine envp_geo_weight_cylinder_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    es bs _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hc
  subst hfc
  exact Hcyl f Hf

/-- The launch-time test as a boolean, so that `List.filter` can use it.
It is `matches_env` with the environment left free: this family fixes argv
and the file system and nothing else. -/
def matches_argv_fs (argv : List (List byte)) (fs : Fs.Fs) (c : FinCore) : Bool :=
  if c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin then true else false

/-- A core the test rejects is not the template with its own fields
plugged in. -/
theorem matches_argv_fs_false (argv : List (List byte)) (fs : Fs.Fs) (c : FinCore) :
    matches_argv_fs argv fs c = false →
    c ≠ FinCore.mkFinCore argv c.core_envp fs c.core_stdin := by
  intro h
  unfold matches_argv_fs at h
  split at h
  · exact absurd h (by simp)
  · assumption

/-- A core the test accepts is that template. -/
theorem matches_argv_fs_true (argv : List (List byte)) (fs : Fs.Fs) (c : FinCore) :
    matches_argv_fs argv fs c = true →
    c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin := by
  intro h
  unfold matches_argv_fs at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE: each record is
in the cylinder OR its core misses the fixed argv or file system and
therefore weighs nothing.  Both forms stay; neither weakens the other. -/
theorem stdin_envp_geometric_bound_or_off_environment (p r q : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (es : List (List byte)) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_envp_stdin_cylinder argv fs es bs (fin_core f)
       ∨ matches_argv_fs argv fs (fin_core f) = false) →
    core_sum (cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ stdin_envp_geometric_cylinder_mass p r q es bs := by
  intro Hnd Hor
  have hw : cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = envp_geo_weight p r q argv fs := rfl
  rw [hw, core_sum_map_fin_core]
  rw [qsum_filter (envp_geo_weight p r q argv fs) (matches_argv_fs argv fs)
        (l.map fin_core)
        (fun c hc => envp_geo_weight_mismatch p r q argv fs c
          (matches_argv_fs_false argv fs c hc))]
  refine envp_geo_weight_cylinder_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    es bs _ (List.filter_sublist.nodup Hnd) ?_
  intro c Hc
  obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
  obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
  subst hfc
  rcases Hor f Hf with Hcyl | Hoff
  · exact Hcyl
  · rw [Hoff] at Hm
    exact absurd Hm (by simp)

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared
mass `1`.  It is the disjunctive bound at the empty environment prefix and
the empty standard-input prefix, where the disjunction is exhaustive. -/
theorem stdin_envp_geometric_mass_upper (p r q : Rat) (argv : List (List byte))
    (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ cd_mass (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) := by
  intro Hnd
  have hm : cd_mass (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = 1 := rfl
  rw [hm]
  refine Rat.le_trans (stdin_envp_geometric_bound_or_off_environment p r q argv fs
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 [] [] l Hnd ?_) ?_
  · intro f _
    by_cases hmf : matches_argv_fs argv fs (fin_core f) = true
    · exact Or.inl ⟨(fin_core f).core_envp, (fin_core f).core_stdin,
        matches_argv_fs_true argv fs (fin_core f) hmf⟩
    · exact Or.inr (Bool.eq_false_iff.mpr hmf)
  · unfold stdin_envp_geometric_cylinder_mass geo_mass
    simp only [envp_factor, List.length_nil, Qpow_0]
    grind

/-! ## Bounds that charge the environment nothing -/

/-- A list whose cores match the fixed argv and file system and whose
standard inputs all come from `B` weighs at most what `B` weighs: the
environment coordinate is charged `1`, its whole declared mass.  Mixing an
envp-varying component in must not make a stdin-only argument worse, and
this is that claim. -/
theorem envp_geo_weight_stdin_family_bound (p r q : Rat) (argv : List (List byte))
    (fs : Fs.Fs) :
    0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ (B : List (List byte)) (SB : Rat) (cs : List FinCore),
      qsum (fun s => geo_point p s.length) B ≤ SB →
      cs.Nodup →
      (∀ c ∈ cs, c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin
         ∧ c.core_stdin ∈ B) →
      qsum (envp_geo_weight p r q argv fs) cs ≤ SB := by
  intro Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 B SB cs HB Hnd Hall
  have hincl : cs ⊆ envp_stdin_product argv fs
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) B := by
    intro c Hc
    obtain ⟨Hmatch, Hstdin⟩ := Hall c Hc
    have Hins := envp_enum_complete (cores_envp_depth cs) (cores_entry_depth cs)
      [] c.core_envp (cores_envp_depth_ge cs c Hc)
      (fun e he => cores_entry_depth_gt cs c e Hc he)
    simp only [List.nil_append] at Hins
    have hp := In_envp_stdin_product argv fs
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) B
      c.core_envp c.core_stdin Hins Hstdin
    rw [← Hmatch] at hp
    exact hp
  have hprod := qsum_core_incl_le (envp_geo_weight p r q argv fs) cs _
    (envp_geo_weight_nonneg p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd hincl
  rw [qsum_envp_stdin_product] at hprod
  have hA0 : 0 ≤ qsum (envp_point r q)
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) :=
    qsum_nonneg _ _ (fun x _ => envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 x)
  have hA1 : qsum (envp_point r q)
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) ≤ 1 := by
    have h := envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 (cores_envp_depth cs)
      (cores_entry_depth cs) []
    have h1 : envp_factor r q [] = 1 := rfl
    rw [h1] at h
    exact h
  have hB0 : 0 ≤ qsum (fun s => geo_point p s.length) B :=
    qsum_nonneg _ _ (fun x _ => geo_point_nonneg p x.length Hp0 Hp1)
  have hmul := mul_le_mul_nonneg hA0 hA1 hB0 HB
  grind

/-- THE LENGTH SLICE: a list drawn from one standard-input length slice
weighs at most `p * (1 - p) ^ n`, with nothing charged for the
environment.  The records may carry any envp at all.  The constant is not
claimed attained here: the slice over a fixed standard-input length still
holds one core per environment, of which there are infinitely many
carrying positive weight whenever `r < 1`. -/
theorem stdin_envp_geometric_slice_bound (p r q : Rat) (argv : List (List byte))
    (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, fin_core f = FinCore.mkFinCore argv f.fin_envp fs f.fin_stdin
       ∧ f.fin_stdin.length = n) →
    core_sum (cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ p * Qpow (1 - p) n := by
  intro Hnd Hall
  have hw : cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = envp_geo_weight p r q argv fs := rfl
  rw [hw, core_sum_map_fin_core]
  refine envp_geo_weight_stdin_family_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    (byte_lists n) (p * Qpow (1 - p) n) _ (Qle_of_Qeq _ _ (byte_lists_sum p n)) Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hc
  subst hfc
  obtain ⟨Henv, Hlen⟩ := Hall f Hf
  refine ⟨Henv, ?_⟩
  have hb := byte_lists_complete f.fin_stdin
  rw [Hlen] at hb
  exact hb

/-- A list confined to standard inputs of length at most `n` weighs at
most `1 - (1 - p) ^ (n + 1)` — the partial sum at its own horizon, with
the environment again charged nothing.  It misses the tail. -/
theorem stdin_envp_geometric_bound_by_max_length (p r q : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, f.fin_stdin.length ≤ n) →
    core_sum (cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ 1 - Qpow (1 - p) (n + 1) := by
  intro Hnd Hlen
  have hw : cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = envp_geo_weight p r q argv fs := rfl
  rw [hw, core_sum_map_fin_core]
  rw [qsum_filter (envp_geo_weight p r q argv fs) (matches_argv_fs argv fs)
        (l.map fin_core)
        (fun c hc => envp_geo_weight_mismatch p r q argv fs c
          (matches_argv_fs_false argv fs c hc))]
  refine envp_geo_weight_stdin_family_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    (short_inputs (n + 1)) (1 - Qpow (1 - p) (n + 1)) _
    (Qle_of_Qeq _ _ (by rw [short_inputs_sum, geo_prefix_sum_closed]))
    (List.filter_sublist.nodup Hnd) ?_
  intro c Hc
  obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
  obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
  subst hfc
  refine ⟨matches_argv_fs_true argv fs _ Hm, ?_⟩
  refine short_inputs_complete (n + 1) _ ?_
  have hle := Hlen f Hf
  simp only [fin_core]
  omega

/-! ## The mass is a supremum and not a maximum here too -/

/-- For `p < 1` no admissible list weighs the declared mass.  The list's
own longest standard input is a horizon, and beyond it sits a positive
tail the list does not collect.  The environment coordinate needs no
hypothesis: the shortfall is already there on the standard-input axis. -/
theorem stdin_envp_geometric_mass_not_attained (p r q : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                             Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
        < cd_mass (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) := by
  intro Hlt l Hnd
  have hm : cd_mass (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = 1 := rfl
  rw [hm]
  have hbound := stdin_envp_geometric_bound_by_max_length p r q argv fs
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 (list_max (l.map (fun f => f.fin_stdin.length))) l Hnd
    (fun f Hf => list_max_ge _ _ (List.mem_map_of_mem Hf))
  have htail : 0 < Qpow (1 - p) (list_max (l.map (fun f => f.fin_stdin.length)) + 1) :=
    Qpow_pos _ _ (by grind)
  grind

/-- The same fact under the name a reader looks for: the declared mass is
not attained. -/
theorem stdin_envp_geometric_mass_supremum_not_maximum (p r q : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      ¬ (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                                Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
           = cd_mass (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) := by
  intro Hlt l Hnd heq
  have h := stdin_envp_geometric_mass_not_attained p r q argv fs
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hlt l Hnd
  rw [heq] at h
  exact Rat.lt_irrefl h

/-! ## Two elementary inequalities the envp lower certificate runs on -/

/-- BERNOULLI, in the one direction this file needs, multiplied out so it
carries no side condition beyond `0 ≤ x ≤ 1`.  It turns "each entry slot
misses at most `x`" into "the environment misses at most `m * x`". -/
theorem Qpow_one_minus_lower (x : Rat) (m : Nat) : 0 ≤ x → x ≤ 1 →
    1 - Qnat m * x ≤ Qpow (1 - x) m := by
  intro Hx0 Hx1
  have H1x : (0 : Rat) ≤ 1 - x := by grind
  induction m with
  | zero => rw [Qpow_0, Qnat_0]; grind
  | succ m ih =>
    rw [Qpow_succ, Qnat_succ]
    have hsq : 0 ≤ Qnat m * x * x :=
      Rat.mul_nonneg (Rat.mul_nonneg (Qnat_nonneg m) Hx0) Hx0
    have step1 : 1 - (1 + Qnat m) * x ≤ (1 - Qnat m * x) * (1 - x) := by grind
    have step2 : (1 - Qnat m * x) * (1 - x) ≤ Qpow (1 - x) m * (1 - x) :=
      Rat.mul_le_mul_of_nonneg_right ih H1x
    grind

/-- THREE MARGINS COMPOSE: if three factors fall short of `1` by `a`, `b`
and `c`, their product falls short by at most `a + b + c`.  The difference
is `a * b * (1 - c) + c * (a + b)`, nonnegative term by term. -/
theorem Qmargins_three (a b c : Rat) : 0 ≤ a → 0 ≤ b → 0 ≤ c → c ≤ 1 →
    1 - (a + b + c) ≤ (1 - a) * (1 - b) * (1 - c) := by
  intro Ha Hb Hc Hc1
  have H1c : (0 : Rat) ≤ 1 - c := by grind
  have h1 : 0 ≤ a * b * (1 - c) := Rat.mul_nonneg (Rat.mul_nonneg Ha Hb) H1c
  have h2 : 0 ≤ c * (a + b) := Rat.mul_nonneg Hc (Rat.add_nonneg Ha Hb)
  grind

/-! ## The environment witness family, and what it weighs -/

/-- Every environment of exactly `m` entries, each entry shorter than `L`.
`envp_enum` is not reused: the certificate needs a duplicate-free list and
`envp_enum` names the stopping environment at every depth it passes. -/
def envps_len (L : Nat) : Nat → List (List (List byte))
  | 0 => [[]]
  | m + 1 => (short_inputs L).flatMap (fun e => (envps_len L m).map (fun es => e :: es))

/-- Every environment of fewer than `M` entries, each shorter than `L`. -/
def envps_upto (L : Nat) : Nat → List (List (List byte))
  | 0 => []
  | M + 1 => envps_len L M ++ envps_upto L M

/-- Its members have exactly `m` entries. -/
theorem envps_len_In_length (L m : Nat) (es : List (List byte)) :
    es ∈ envps_len L m → es.length = m := by
  induction m generalizing es with
  | zero =>
    intro h
    simp only [envps_len, List.mem_singleton] at h
    subst h
    rfl
  | succ m ih =>
    intro h
    simp only [envps_len, List.mem_flatMap] at h
    obtain ⟨e, _, hin⟩ := h
    obtain ⟨es', hin', hcons⟩ := List.mem_map.mp hin
    subst hcons
    simp only [List.length_cons, ih es' hin']

/-- Its members' entries are shorter than `L`. -/
theorem envps_len_In_entry (L m : Nat) (es : List (List byte)) (e : List byte) :
    es ∈ envps_len L m → e ∈ es → e.length < L := by
  induction m generalizing es with
  | zero =>
    intro h he
    simp only [envps_len, List.mem_singleton] at h
    subst h
    exact absurd he (by simp)
  | succ m ih =>
    intro h he
    simp only [envps_len, List.mem_flatMap] at h
    obtain ⟨e0, he0, hin⟩ := h
    obtain ⟨es', hin', hcons⟩ := List.mem_map.mp hin
    subst hcons
    rcases List.mem_cons.mp he with hhd | htl
    · subst hhd
      exact short_inputs_In_length L e he0
    · exact ih es' hin' htl

/-- ... and it repeats nothing: distinct first entries give disjoint
blocks, and within a block consing a fixed entry is injective. -/
theorem envps_len_nodup (L m : Nat) : (envps_len L m).Nodup := by
  induction m with
  | zero => simp [envps_len]
  | succ m ih =>
    simp only [envps_len]
    refine NoDup_flat_map _ _ (short_inputs_nodup L) ?_ ?_
    · intro e _
      refine NoDup_map_inj _ _ ?_ ih
      intro x y _ _ Heq
      exact congrArg List.tail Heq
    · intro e1 e2 es _ _ H1 H2
      obtain ⟨x1, _, Hx1⟩ := List.mem_map.mp H1
      obtain ⟨x2, _, Hx2⟩ := List.mem_map.mp H2
      exact congrArg (fun l => l.headD []) (Hx1.trans Hx2.symm)

/-- Its members have fewer than `M` entries. -/
theorem envps_upto_In_length (L M : Nat) (es : List (List byte)) :
    es ∈ envps_upto L M → es.length < M := by
  induction M generalizing es with
  | zero => intro h; exact absurd h (by simp [envps_upto])
  | succ M ih =>
    intro h
    simp only [envps_upto, List.mem_append] at h
    rcases h with h | h
    · have := envps_len_In_length L M es h; omega
    · have := ih es h; omega

/-- ... and it repeats nothing: the two halves are duplicate-free and are
separated by their entry count. -/
theorem envps_upto_nodup (L M : Nat) : (envps_upto L M).Nodup := by
  induction M with
  | zero => simp [envps_upto]
  | succ M ih =>
    simp only [envps_upto]
    rw [List.nodup_append]
    refine ⟨envps_len_nodup L M, ih, ?_⟩
    intro a ha b hb heq
    have h1 := envps_len_In_length L M a ha
    rw [heq] at h1
    have h2 := envps_upto_In_length L M b hb
    omega

/-- The entry-length half of what `envps_upto` promises, at the same level
as its entry-count half. -/
theorem envps_upto_In_entry (L M : Nat) (es : List (List byte)) (e : List byte) :
    es ∈ envps_upto L M → e ∈ es → e.length < L := by
  induction M generalizing es with
  | zero => intro h _; exact absurd h (by simp [envps_upto])
  | succ M ih =>
    intro h he
    simp only [envps_upto, List.mem_append] at h
    rcases h with h | h
    · exact envps_len_In_entry L M es e h he
    · exact ih es h he

/-- ... and conversely the enumeration misses no environment inside its
two depths.  This is the containment a shared witness turns on: a task's
canonical environment is in there as soon as `M` exceeds its entry count
and `L` its longest entry. -/
theorem envps_len_complete (L : Nat) (es : List (List byte)) :
    (∀ e ∈ es, e.length < L) → es ∈ envps_len L es.length := by
  induction es with
  | nil => intro _; simp [envps_len]
  | cons e es ih =>
    intro Hlen
    simp only [List.length_cons, envps_len, List.mem_flatMap]
    refine ⟨e, short_inputs_complete L e (Hlen e (by simp)), ?_⟩
    exact List.mem_map_of_mem (ih (fun e' he' => Hlen e' (List.mem_cons_of_mem _ he')))

/-- The same, for the union over entry counts below `M`. -/
theorem envps_upto_complete (L M : Nat) (es : List (List byte)) :
    es.length < M → (∀ e ∈ es, e.length < L) → es ∈ envps_upto L M := by
  induction M generalizing es with
  | zero => intro h _; omega
  | succ M ih =>
    intro Hlt Hlen
    simp only [envps_upto, List.mem_append]
    by_cases heq : es.length = M
    · left
      rw [← heq]
      exact envps_len_complete L es Hlen
    · right
      exact ih es (by omega) Hlen

/-- ONE FULL ENTRY-COUNT SLICE weighs a power: the `m` entry slots are
independent, each collects what the entry enumeration collects, and the
total is that number to the `m`-th. -/
theorem qsum_entries_geo_product_envps_len (q : Rat) (L m : Nat) :
    qsum (entries_geo_product q) (envps_len L m)
      = Qpow (1 - Qpow (1 - q) L) m := by
  induction m with
  | zero =>
    simp only [envps_len, qsum_cons, qsum_nil, entries_geo_product, Qpow_0]
    grind
  | succ m ih =>
    have hblock : ∀ e ∈ short_inputs L,
        qsum (entries_geo_product q) ((envps_len L m).map (fun es => e :: es))
          = Qpow (1 - Qpow (1 - q) L) m * geo_point q e.length := by
      intro e _
      rw [qsum_map]
      rw [qsum_ext (fun es => entries_geo_product q (e :: es))
            (fun es => geo_point q e.length * entries_geo_product q es)
            (envps_len L m) (fun es _ => rfl)]
      rw [qsum_scale (geo_point q e.length) (entries_geo_product q) (envps_len L m), ih]
      grind
    simp only [envps_len]
    rw [qsum_flat_map]
    rw [qsum_ext
          (fun e => qsum (entries_geo_product q)
                      ((envps_len L m).map (fun es => e :: es)))
          (fun e => Qpow (1 - Qpow (1 - q) L) m * geo_point q e.length)
          (short_inputs L) hblock]
    rw [qsum_scale (Qpow (1 - Qpow (1 - q) L) m) (fun e => geo_point q e.length)
          (short_inputs L)]
    rw [short_inputs_sum, geo_prefix_sum_closed, Qpow_succ]
    grind

/-- The same slice under the stopping weight. -/
theorem qsum_envp_point_envps_len (r q : Rat) (L m : Nat) :
    qsum (envp_point r q) (envps_len L m)
      = r * Qpow (1 - r) m * Qpow (1 - Qpow (1 - q) L) m := by
  rw [qsum_ext (envp_point r q)
        (fun es => r * Qpow (1 - r) m * entries_geo_product q es) (envps_len L m)
        (by intro es Hes
            rw [envp_point_closed_form, envps_len_In_length L m es Hes])]
  rw [qsum_scale (r * Qpow (1 - r) m) (entries_geo_product q) (envps_len L m)]
  rw [qsum_entries_geo_product_envps_len]

/-- The partial sum of the environment series over entry counts.  Its
ratio is `(1 - r) * G` rather than `1 - r`, because an environment that
continues must also fill the slot it opened and the slot collects `G`.  No
closed form is stated: the certificate needs a lower bound, and
`envp_prefix_sum_lower` gives one with no side condition. -/
def envp_prefix_sum (r G : Rat) : Nat → Rat
  | 0 => 0
  | M + 1 => r * Qpow (1 - r) M * Qpow G M + envp_prefix_sum r G M

/-- The union over entry counts weighs the partial sum. -/
theorem qsum_envp_point_envps_upto (r q : Rat) (L M : Nat) :
    qsum (envp_point r q) (envps_upto L M)
      = envp_prefix_sum r (1 - Qpow (1 - q) L) M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [envps_upto, envp_prefix_sum]
    rw [qsum_app, ih, qsum_envp_point_envps_len]

/-- THE LOWER ESTIMATE: the partial sum is at least `G ^ M` times what the
entry-count geometric alone would have collected.  Both factors go to `1`
as their parameters grow, which is why `L` is chosen after `M`. -/
theorem envp_prefix_sum_lower (r G : Rat) (M : Nat) : 0 ≤ r → r ≤ 1 → 0 ≤ G → G ≤ 1 →
    Qpow G M * (1 - Qpow (1 - r) M) ≤ envp_prefix_sum r G M := by
  intro Hr0 Hr1 HG0 HG1
  have H1r : (0 : Rat) ≤ 1 - r := by grind
  have H1r1 : (1 : Rat) - r ≤ 1 := by grind
  induction M with
  | zero => simp only [envp_prefix_sum, Qpow_0]; grind
  | succ M ih =>
    have HX : (0 : Rat) ≤ 1 - Qpow (1 - r) (M + 1) := by
      have := Qpow_le_1 (1 - r) (M + 1) H1r H1r1
      grind
    have hGM : 0 ≤ Qpow G M := Qpow_nonneg G M HG0
    have hG : G * Qpow G M ≤ 1 * Qpow G M :=
      Rat.mul_le_mul_of_nonneg_right HG1 hGM
    have step1 : Qpow G (M + 1) * (1 - Qpow (1 - r) (M + 1))
        ≤ Qpow G M * (1 - Qpow (1 - r) (M + 1)) := by
      rw [Qpow_succ]
      refine Rat.mul_le_mul_of_nonneg_right ?_ HX
      grind
    have step2 : Qpow G M * (1 - Qpow (1 - r) (M + 1))
        ≤ r * Qpow (1 - r) M * Qpow G M + Qpow G M * (1 - Qpow (1 - r) M) := by
      rw [Qpow_succ]
      grind
    simp only [envp_prefix_sum]
    grind

/-! ## The lower certificate for `stdin_envp_geometric` -/

/-- THE WITNESS FAMILY: one record per environment-and-standard-input pair
drawn from the two prefix families.  As everywhere in this library these
records are not claimed valid and not claimed rejected by anything. -/
def envp_geo_lower_witness (argv : List (List byte)) (fs : Fs.Fs) (M L k : Nat) :
    List FinProcInput :=
  (envp_stdin_product argv fs (envps_upto L M) (short_inputs k)).map core_input

/-- Its cores are exactly the product of the two prefix families. -/
theorem map_fin_core_envp_geo_lower_witness (argv : List (List byte)) (fs : Fs.Fs)
    (M L k : Nat) :
    (envp_geo_lower_witness argv fs M L k).map fin_core
      = envp_stdin_product argv fs (envps_upto L M) (short_inputs k) :=
  map_fin_core_core_input _

/-- The witness is admissible: both coordinates are duplicate-free. -/
theorem envp_geo_lower_witness_nodup (argv : List (List byte)) (fs : Fs.Fs)
    (M L k : Nat) :
    ((envp_geo_lower_witness argv fs M L k).map fin_core).Nodup := by
  rw [map_fin_core_envp_geo_lower_witness]
  exact NoDup_envp_stdin_product argv fs _ _ (envps_upto_nodup L M) (short_inputs_nodup k)

/-- THE WITNESS, at each triple of depths: an admissible list weighing
exactly the product of the two coordinates' partial sums.  The equality is
unconditional arithmetic; the three strictnesses enter one lemma later,
where the depths have to be chosen to meet a target. -/
theorem stdin_envp_geometric_mass_lower_witness (p r q : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (M L k : Nat) :
    ((envp_geo_lower_witness argv fs M L k).map fin_core).Nodup
    ∧ core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                             Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))
        (envp_geo_lower_witness argv fs M L k)
        = envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k) := by
  refine ⟨envp_geo_lower_witness_nodup argv fs M L k, ?_⟩
  have hw : cd_weight (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = envp_geo_weight p r q argv fs := rfl
  rw [hw, core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness]
  rw [qsum_envp_stdin_product, qsum_envp_point_envps_upto, short_inputs_sum,
    geo_prefix_sum_closed]

/-- THE MARGIN ARITHMETIC, WITH THE DEPTHS STILL FREE.  Given three depths
whose three tails together come in under `eps`, the witness's partial sum
is within `eps` of `1`.  The entry-count tail is `(1 - r) ^ M`, the
standard-input tail is `(1 - p) ^ k`, and the entry-length shortfall is
`M` slots each missing `(1 - q) ^ L`, which is where the `Qnat M` factor
comes from.  No strict hypothesis appears: strictness is spent choosing
depths, never in the arithmetic that uses them. -/
theorem envp_stdin_margin_at_depths (p r q eps : Rat) (M L k : Nat) :
    0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    Qnat M * Qpow (1 - q) L + Qpow (1 - r) M + Qpow (1 - p) k ≤ eps →
    1 - eps ≤ envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k) := by
  intro Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum
  have Hx0 : 0 ≤ Qpow (1 - q) L := Qpow_nonneg _ _ (by grind)
  have Hx1 : Qpow (1 - q) L ≤ 1 := Qpow_le_1 _ _ (by grind) (by grind)
  have Hb0 : 0 ≤ Qpow (1 - r) M := Qpow_nonneg _ _ (by grind)
  have Hb1 : Qpow (1 - r) M ≤ 1 := Qpow_le_1 _ _ (by grind) (by grind)
  have Hc0 : 0 ≤ Qpow (1 - p) k := Qpow_nonneg _ _ (by grind)
  have Hc1 : Qpow (1 - p) k ≤ 1 := Qpow_le_1 _ _ (by grind) (by grind)
  have Ha0 : 0 ≤ Qnat M * Qpow (1 - q) L := Rat.mul_nonneg (Qnat_nonneg M) Hx0
  have HG0 : (0 : Rat) ≤ 1 - Qpow (1 - q) L := by grind
  have HG1 : (1 : Rat) - Qpow (1 - q) L ≤ 1 := by grind
  have hmar := Qmargins_three (Qnat M * Qpow (1 - q) L) (Qpow (1 - r) M)
    (Qpow (1 - p) k) Ha0 Hb0 Hc0 Hc1
  have hpow := Qpow_one_minus_lower (Qpow (1 - q) L) M Hx0 Hx1
  have hlow := envp_prefix_sum_lower r (1 - Qpow (1 - q) L) M Hr0 Hr1 HG0 HG1
  have hB : (0 : Rat) ≤ 1 - Qpow (1 - r) M := by grind
  have hC : (0 : Rat) ≤ 1 - Qpow (1 - p) k := by grind
  have hstep1 : (1 - Qnat M * Qpow (1 - q) L) * (1 - Qpow (1 - r) M)
      ≤ Qpow (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - r) M) :=
    Rat.mul_le_mul_of_nonneg_right hpow hB
  have hfin : (1 - Qnat M * Qpow (1 - q) L) * (1 - Qpow (1 - r) M)
        * (1 - Qpow (1 - p) k)
      ≤ envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k) :=
    Rat.mul_le_mul_of_nonneg_right (Rat.le_trans hstep1 hlow) hC
  grind

/-- ... AND THE DEPTHS THAT MEET IT, above any floors asked for.  Each
strictness buys one depth and the order matters: an entry count `M`, then
a standard-input length `k`, then LAST an entry length `L` whose bound
mentions `M`, so that all `M` entry slots together miss at most a third of
the margin.  `M0` and `L0` are the floors a mixture passes when it must
also reach one fixed environment. -/
theorem envp_stdin_depths_above (p r q eps : Rat) (M0 L0 : Nat) :
    0 < p → p ≤ 1 → 0 < r → r ≤ 1 → 0 < q → q ≤ 1 → 0 < eps →
    ∃ M L k : Nat,
      M0 ≤ M ∧ L0 ≤ L
      ∧ (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M + Qpow (1 - p) k ≤ eps)
      ∧ Qpow (1 - p) k ≤ eps := by
  intro Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps
  have h3 : (0 : Rat) < 1 / 3 := by decide +kernel
  have h31 : (1 : Rat) / 3 ≤ 1 := by decide +kernel
  have Heps3 : 0 < eps * (1 / 3) := Rat.mul_pos Heps h3
  have Hthird : eps * (1 / 3) ≤ eps := by
    have := Rat.mul_le_mul_of_nonneg_left h31 (Rat.le_of_lt Heps)
    grind
  obtain ⟨M, HM0, HM⟩ := geo_gap_small_above r (eps * (1 / 3)) M0 Hrpos Hr1 Heps3
  obtain ⟨k, Hk⟩ := geo_gap_small p (eps * (1 / 3)) Hppos Hp1 Heps3
  have HD : (0 : Rat) < Qnat M + 1 := by
    have := Qnat_nonneg M
    grind
  have Hinv : (0 : Rat) < (Qnat M + 1)⁻¹ := Rat.inv_pos.mpr HD
  have Hbnd : 0 < eps * (1 / 3) * (Qnat M + 1)⁻¹ := Rat.mul_pos Heps3 Hinv
  obtain ⟨L, HL0, HL⟩ :=
    geo_gap_small_above q (eps * (1 / 3) * (Qnat M + 1)⁻¹) L0 Hqpos Hq1 Hbnd
  refine ⟨M, L, k, HM0, HL0, ?_, Rat.le_trans Hk Hthird⟩
  have Hcancel : (Qnat M + 1) * (Qnat M + 1)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ (Rat.ne_of_gt HD)
  have HMD : Qnat M * (Qnat M + 1)⁻¹ ≤ 1 := by
    have h1 : Qnat M ≤ Qnat M + 1 := by have := Qle_0_1; grind
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt Hinv)
    grind
  have h1 : Qpow (1 - q) L * Qnat M ≤ eps * (1 / 3) * (Qnat M + 1)⁻¹ * Qnat M :=
    Rat.mul_le_mul_of_nonneg_right HL (Qnat_nonneg M)
  have h2 : Qnat M * (Qnat M + 1)⁻¹ * (eps * (1 / 3)) ≤ 1 * (eps * (1 / 3)) :=
    Rat.mul_le_mul_of_nonneg_right HMD (Rat.le_of_lt Heps3)
  have Ha : Qnat M * Qpow (1 - q) L ≤ eps * (1 / 3) := by grind
  grind

/-- THE LOWER CERTIFICATE: for every margin there is an admissible list
weighing at least the declared mass minus that margin.  With
`stdin_envp_geometric_mass_upper` above it the declared `1` is the least
upper bound of the admissible partial sums, and by
`stdin_envp_geometric_mass_not_attained` it is never met.  All three
strict inequalities are hypotheses here rather than tightenings of the
constructor: everything above this lemma holds at the degenerate
parameters. -/
theorem stdin_envp_geometric_mass_lower_certificate (p r q : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (eps : Rat) :
    0 < p → 0 < r → 0 < q → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) - eps
          ≤ core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                                   Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l := by
  intro Hppos Hrpos Hqpos Heps
  obtain ⟨M, L, k, _, _, Hsum, _⟩ :=
    envp_stdin_depths_above p r q eps 0 0 Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps
  refine ⟨envp_geo_lower_witness argv fs M L k,
    envp_geo_lower_witness_nodup argv fs M L k, ?_⟩
  rw [(stdin_envp_geometric_mass_lower_witness p r q argv fs
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k).2]
  have hm : cd_mass (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = 1 := rfl
  rw [hm]
  exact envp_stdin_margin_at_depths p r q eps M L k Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum

/-! ## Non-vacuity: the environment really carries mass -/

/-- `geo_weight`'s envp instance, stated because the bite below needs it
and `GeoStdin` has only the argv one. -/
theorem geo_weight_off_envp_zero (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (c : FinCore) : c.core_envp ≠ envp → geo_weight p argv envp fs c = 0 := by
  intro Hne
  refine geo_weight_mismatch p argv envp fs c ?_
  intro Heq
  exact Hne (congrArg FinCore.core_envp Heq)

/-- A standard input of any length weighs something, at a non-degenerate
member of the family. -/
theorem geo_point_pos (q : Rat) (n : Nat) : 0 < q → q < 1 → 0 < geo_point q n := by
  intro Hq0 Hq1
  unfold geo_point geo_mass
  refine Rat.mul_pos Hq0 (Qpow_pos _ _ ?_)
  exact Rat.mul_pos (by grind) (by decide +kernel)

/-- An environment of ANY length weighs something, because every factor
in the running product does.  This is where the family's point becomes
arithmetic. -/
theorem envp_point_pos (r q : Rat) (es : List (List byte)) :
    0 < r → r < 1 → 0 < q → q < 1 → 0 < envp_point r q es := by
  intro Hr0 Hr1 Hq0 Hq1
  unfold envp_point
  refine Rat.mul_pos Hr0 ?_
  induction es with
  | nil => simp only [envp_factor]; decide +kernel
  | cons e es ih =>
    simp only [envp_factor]
    exact Rat.mul_pos (Rat.mul_pos (by grind) (geo_point_pos q e.length Hq0 Hq1)) ih

/-- A core over a non-canonical launch-time environment: one entry, the
single byte `A`.  As at `geo_example_core` it is not claimed valid. -/
def envp_example_named : FinCore := FinCore.mkFinCore [] [[Z_to_bv 8 65]] [] []

/-- THE BITE THE FAMILY EXISTS FOR, both halves on one core.
`stdin_geometric` over the empty environment weighs this core exactly
zero, while `stdin_envp_geometric` weighs it strictly positively.  Under a
distribution built from `stdin_geometric` alone a fire set living at cores
like this one lies in a null set, so a bound about it says nothing; under
this family the core carries weight.  It does NOT say that any particular
task's bound is thereby sharper. -/
theorem stdin_envp_geometric_envp_bites (p r q : Rat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 < p → p < 1 → 0 < r → r < 1 → 0 < q → q < 1 →
    cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) envp_example_named = 0
    ∧ 0 < cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
            envp_example_named := by
  intro Hppos Hplt Hrpos Hrlt Hqpos Hqlt
  constructor
  · have hw : cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) = geo_weight p [] [] [] := rfl
    rw [hw]
    refine geo_weight_off_envp_zero p [] [] [] envp_example_named ?_
    simp [envp_example_named]
  · have hw : cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
        = envp_geo_weight p r q [] [] := rfl
    rw [hw]
    unfold envp_example_named
    rw [envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q _ Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p _ Hppos Hplt)

/-- ... and the family is still not constant: a core whose argv misses the
fixed one weighs exactly zero. -/
theorem envp_geo_weight_off_argv_zero (p r q : Rat) (argv : List (List byte))
    (fs : Fs.Fs) (c : FinCore) :
    c.core_argv ≠ argv → envp_geo_weight p r q argv fs c = 0 := by
  intro Hne
  refine envp_geo_weight_mismatch p r q argv fs c ?_
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- THE BITE, both ways: the distribution is not the zero distribution,
and it is not a constant either. -/
theorem stdin_envp_geometric_bites (p r q : Rat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 < p → p < 1 → 0 < r → r < 1 → 0 < q → q < 1 →
    0 < cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
          geo_example_core
    ∧ cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
        geo_example_other = 0 := by
  intro Hppos Hplt Hrpos Hrlt Hqpos Hqlt
  have hw : cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = envp_geo_weight p r q [] [] := rfl
  constructor
  · rw [hw]
    unfold geo_example_core
    rw [envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q _ Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p _ Hppos Hplt)
  · rw [hw]
    refine envp_geo_weight_off_argv_zero p r q [] [] geo_example_other ?_
    simp [geo_example_other]

/-! ## Non-vacuity: `List.Nodup` is load-bearing here too -/

/-- The member of the family at `p = r = q = 1`: stop immediately on every
axis.  It is the point mass on the core with no environment and no
standard input, and it is what makes the refutation below closed
arithmetic instead of open terms. -/
def envp_point_cd : CoreDistribution :=
  stdin_envp_geometric 1 1 1 [] []
    Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl

/-- THE `List.Nodup` HYPOTHESIS IS LOAD-BEARING for this family's cylinder
bound: offer the same core twice and the sum is `2` against a cylinder
mass of `1`.  The second conjunct says the list really does satisfy the
cylinder hypothesis, the third that the bound fails on it, and the first
names what excludes it. -/
theorem stdin_envp_geometric_bound_needs_nodup :
    ¬ (([geo_empty_input, geo_empty_input].map fin_core).Nodup)
    ∧ (∀ f ∈ [geo_empty_input, geo_empty_input],
         in_envp_stdin_cylinder [] [] [] [] (fin_core f))
    ∧ ¬ (core_sum (cd_weight envp_point_cd) [geo_empty_input, geo_empty_input]
           ≤ stdin_envp_geometric_cylinder_mass 1 1 1 [] []) := by
  have hc : fin_core geo_empty_input = FinCore.mkFinCore [] [] [] [] :=
    fin_core_core_input geo_example_core
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    simp only [List.map_cons, List.map_nil, List.nodup_cons] at Hnd
    exact Hnd.1 (by simp)
  · intro f Hf
    have hf : f = geo_empty_input := by
      rcases List.mem_cons.mp Hf with h | h
      · exact h
      · exact List.mem_singleton.mp h
    subst hf
    exact ⟨[], [], hc⟩
  · intro Hle
    have hw : cd_weight envp_point_cd (fin_core geo_empty_input) = 1 := by
      show envp_geo_weight 1 1 1 [] [] (fin_core geo_empty_input) = 1
      rw [hc, envp_geo_weight_match]
      decide +kernel
    rw [core_sum_cons, core_sum_cons, core_sum_nil, hw] at Hle
    unfold stdin_envp_geometric_cylinder_mass geo_mass at Hle
    simp only [envp_factor, List.length_nil, Qpow_0] at Hle
    exact (by decide +kernel : ¬ ((1 : Rat) + (1 + 0) ≤ 1 * 1)) Hle

/-! ## The five degenerate members -/

/-- At `p = 0` the weight vanishes identically. -/
theorem envp_geo_weight_zero_at_zero_p (r q : Rat) (argv : List (List byte))
    (fs : Fs.Fs) (c : FinCore) : envp_geo_weight 0 r q argv fs c = 0 := by
  unfold envp_geo_weight
  split
  · unfold geo_point
    grind
  · rfl

/-- At `r = 0` the weight vanishes identically too. -/
theorem envp_geo_weight_zero_at_zero_r (p q : Rat) (argv : List (List byte))
    (fs : Fs.Fs) (c : FinCore) : envp_geo_weight p 0 q argv fs c = 0 := by
  unfold envp_geo_weight
  split
  · unfold envp_point
    grind
  · rfl

/-- At `q = 0` the weight does NOT vanish, but every core with a non-empty
environment weighs zero: the family collapses towards `stdin_geometric`
and is as blind to the launch-time environment as it is. -/
theorem envp_geo_weight_zero_at_zero_q (p r : Rat) (argv : List (List byte))
    (fs : Fs.Fs) (c : FinCore) :
    c.core_envp ≠ [] → envp_geo_weight p r 0 argv fs c = 0 := by
  intro Hne
  unfold envp_geo_weight
  split
  · cases h : c.core_envp with
    | nil => exact absurd h Hne
    | cons e es =>
      unfold envp_point
      simp only [envp_factor]
      unfold geo_point
      grind
  · rfl

/-- At `r = 1` the running product's `1 - r` factor is zero, so the family
IS `stdin_geometric` over the empty launch-time environment, weight for
weight and at every core.  `r < 1` is therefore genuinely asked for by
`envp_point_pos`, and this is where it is pinned. -/
theorem envp_geo_weight_collapses_at_one_r (p q : Rat) (argv : List (List byte))
    (fs : Fs.Fs) (c : FinCore) :
    envp_geo_weight p 1 q argv fs c = geo_weight p argv [] fs c := by
  unfold envp_geo_weight geo_weight
  split
  · next Hm =>
    split
    · next He =>
      have Henv : c.core_envp = [] := congrArg FinCore.core_envp He
      rw [Henv]
      unfold envp_point
      simp only [envp_factor]
      grind
    · next Hne =>
      cases h : c.core_envp with
      | nil => exact absurd (by rw [← h]; exact Hm) Hne
      | cons e es =>
        unfold envp_point
        simp only [envp_factor]
        grind
  · next Hnm =>
    split
    · next He =>
      exact absurd (by rw [congrArg FinCore.core_envp He]; exact He) Hnm
    · rfl

/-- The collapse read off the distribution. -/
theorem stdin_envp_geometric_collapses_at_one_r (p q : Rat) (argv : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    cd_weight (stdin_envp_geometric p 1 q argv fs Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1) c
      = cd_weight (stdin_geometric p argv [] fs Hp0 Hp1) c :=
  envp_geo_weight_collapses_at_one_r p q argv fs c

/-- ... and so the blindness: at `r = 1` every core with a non-empty
environment weighs zero. -/
theorem stdin_envp_geometric_envp_needs_r_below_one (p q : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    c.core_envp ≠ [] →
    cd_weight (stdin_envp_geometric p 1 q argv fs Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1) c
      = 0 := by
  intro Hne
  rw [stdin_envp_geometric_collapses_at_one_r]
  have hw : cd_weight (stdin_geometric p argv [] fs Hp0 Hp1) = geo_weight p argv [] fs :=
    rfl
  rw [hw]
  exact geo_weight_off_envp_zero p argv [] fs c Hne

/-- THE STRICTNESS IS LOAD-BEARING: at `p = 0` every admissible list
weighs zero while the declared mass is still `1`, so no list comes within
`1/2` of it and the lower certificate is false there. -/
theorem stdin_envp_geometric_mass_lower_needs_positive (argv : List (List byte))
    (fs : Fs.Fs) (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    (∀ l : List FinProcInput,
       core_sum (cd_weight (stdin_envp_geometric 0 r q argv fs
                              Rat.le_refl Qle_0_1 Hr0 Hr1 Hq0 Hq1)) l = 0)
    ∧ ¬ (cd_mass (stdin_envp_geometric 0 r q argv fs
                    Rat.le_refl Qle_0_1 Hr0 Hr1 Hq0 Hq1) - 1 / 2 ≤ 0) := by
  constructor
  · intro l
    refine core_sum_zero_weight _ l ?_
    intro c
    exact envp_geo_weight_zero_at_zero_p r q argv fs c
  · have hm : cd_mass (stdin_envp_geometric 0 r q argv fs
        Rat.le_refl Qle_0_1 Hr0 Hr1 Hq0 Hq1) = 1 := rfl
    rw [hm]
    decide +kernel

/-- The blindness at `q = 0`, read off the distribution. -/
theorem stdin_envp_geometric_envp_needs_positive_q (p r : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore) :
    c.core_envp ≠ [] →
    cd_weight (stdin_envp_geometric p r 0 argv fs Hp0 Hp1 Hr0 Hr1 Rat.le_refl Qle_0_1) c
      = 0 := by
  intro Hne
  exact envp_geo_weight_zero_at_zero_q p r argv fs c Hne

/-- THE FIFTH DEGENERATE MEMBER, `q = 1`: at it `geo_point 1 m` is zero
for every `m ≥ 1`, so an environment holding any non-empty entry weighs
nothing while environments made only of empty entries keep their weight.
A real environment entry is a `NAME=value` string, so the family is blind
to every environment a program will actually see and has not gone quiet.
The hypothesis names a non-empty ENTRY, not a non-empty environment: the
environment `[[]]` weighs a positive amount at `q = 1`. -/
theorem envp_factor_zero_at_one_q (r : Rat) (es : List (List byte)) (e : List byte) :
    e ∈ es → e ≠ [] → envp_factor r 1 es = 0 := by
  induction es with
  | nil => intro h _; exact absurd h (by simp)
  | cons e0 es ih =>
    intro Hin Hne
    simp only [envp_factor]
    rcases List.mem_cons.mp Hin with heq | hin
    · subst heq
      cases e with
      | nil => exact absurd rfl Hne
      | cons b e' =>
        unfold geo_point geo_mass
        simp only [List.length_cons, Qpow_succ]
        grind
    · rw [ih hin Hne]
      grind

/-- ... and so the weight is zero at such a core. -/
theorem envp_geo_weight_zero_at_one_q (p r : Rat) (argv : List (List byte))
    (fs : Fs.Fs) (c : FinCore) (e : List byte) :
    e ∈ c.core_envp → e ≠ [] → envp_geo_weight p r 1 argv fs c = 0 := by
  intro Hin Hne
  unfold envp_geo_weight
  split
  · unfold envp_point
    rw [envp_factor_zero_at_one_q r c.core_envp e Hin Hne]
    grind
  · rfl

/-- The blindness at `q = 1`, read off the distribution. -/
theorem stdin_envp_geometric_envp_needs_q_below_one (p r : Rat)
    (argv : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore) (e : List byte) :
    e ∈ c.core_envp → e ≠ [] →
    cd_weight (stdin_envp_geometric p r 1 argv fs Hp0 Hp1 Hr0 Hr1 Qle_0_1 Rat.le_refl) c
      = 0 := by
  intro Hin Hne
  exact envp_geo_weight_zero_at_one_q p r argv fs c e Hin Hne

/-- ... AND THE HYPOTHESIS CANNOT BE WEAKENED to "the environment is
non-empty": at `q = 1` the environment with one empty entry weighs
`2 / 25`, positive, while the one-entry-of-one-byte environment weighs
zero. -/
theorem envp_geo_weight_at_one_q_needs_a_non_empty_entry :
    envp_geo_weight (1 / 2) (1 / 5) 1 [] []
        (FinCore.mkFinCore [] [[Z_to_bv 8 65]] [] []) = 0
    ∧ 0 < envp_geo_weight (1 / 2) (1 / 5) 1 [] []
            (FinCore.mkFinCore [] [[]] [] []) := by
  constructor
  · exact envp_geo_weight_zero_at_one_q _ _ _ _ _ [Z_to_bv 8 65] (by simp) (by simp)
  · rw [envp_geo_weight_match]
    decide +kernel
