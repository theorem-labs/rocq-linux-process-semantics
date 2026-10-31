-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdinVarying
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Calibrated
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFile
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileHeader
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Alphabet
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileHeaderAlphabet

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058

# EquivalenceDefinition.MeasureLib.GeoFileVarying — geometric file contents over a varying launch-time environment

This file holds `theories/EquivalenceDefinition/MeasureLib.v:11451-13129`: the
combinator that varies BOTH the input file's contents and the launch-time
environment, its cylinder bound and its two certificates, the six degenerate
members it pins, and the argv/path coupling that closes the one obligation a
caller of either file family can get silently wrong — the obligation itself,
the derived constructors that make the mismatch unrepresentable, the file
system lemmas behind the collapse, and the misconfigured instances exhibited
for all four file families.

Rocq's `Q` is Lean's `Rat` and Rocq's `Qeq` is Lean's `=`, as `Measure.lean`
says.  Every name is the Rocq name.
-/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## Rational steps core Lean does not carry

Rocq spends `Qle_lt_trans`, `Qlt_le_trans`, `Qmult_le_compat_nonneg` and
`Qlt_minus_iff` here; core Lean's `Rat` has neither, so this file proves the
four shapes it uses from the core lemmas that do exist.  They are `private`,
so no sibling span file can collide with them. -/

/-- A `≤` step followed by a `<` step. -/
private theorem rat_lt_of_le_of_lt {a b c : Rat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  Rat.not_le.mp (fun h => (Rat.not_le.mpr hbc) (Rat.le_trans h hab))

/-- Two nonnegative factors, each below its own bound, multiply below the
product of the bounds. -/
private theorem rat_mul_le_mul_nonneg {a b c d : Rat} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) : a * c ≤ b * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hcd ha)
    (Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans hc hcd))

/-- Subtracting a difference gives the subtrahend back. -/
private theorem rat_sub_sub_self (a b : Rat) : a - (a - b) = b := by
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg,
    ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]

/-- One minus a positive amount falls short of one. -/
private theorem rat_one_sub_lt_one (x : Rat) (hx : 0 < x) : (1 : Rat) - x < 1 := by
  rw [Rat.lt_iff_sub_pos, rat_sub_sub_self]
  exact hx

/-- A path equality test is `false` on two different paths. -/
private theorem path_eqb_false_of_ne {p q : Fs.path} (h : p ≠ q) : Fs.path_eqb p q = false := by
  cases hb : Fs.path_eqb p q with
  | false => rfl
  | true => exact absurd ((Fs.path_eqb_eq p q).mp hb) h

/-- Filtering keeps a duplicate-free list duplicate-free.  Rocq uses
`List.NoDup_filter`; core Lean has the sublist facts and not this one. -/
private theorem nodup_filter {α : Type} (p : α → Bool) (l : List α) (h : l.Nodup) :
    (l.filter p).Nodup :=
  List.Nodup.sublist List.filter_sublist h

/-! ## The template with both varying coordinates plugged in -/

/-- The core over a fixed argv, a fixed base file system and a fixed standard
input, carrying the environment `es` and the file contents `d`.  It is
`file_core` with the environment moved from the fixed parameters to the varying
ones, so that `file_geometric`'s two round trips serve this family unchanged. -/
def file_envp_core (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (es : List (List byte)) (d : List byte) : FinCore :=
  file_core argv es fs0 pth s d

/-- The file contents are readable back off the template. -/
theorem fs_file_file_envp_core (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (es : List (List byte)) (d : List byte) :
    fs_file pth (file_envp_core argv fs0 pth s es d).core_fs = d :=
  fs_file_file_core argv es fs0 pth s d

/-- The environment is readable back off the template. -/
theorem core_envp_file_envp_core (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (es : List (List byte)) (d : List byte) :
    (file_envp_core argv fs0 pth s es d).core_envp = es := rfl

/-- The weight: zero unless the core's argv, standard input and the rest of its
file system are the fixed ones; otherwise the environment's weight times the
geometric weight of its input file's length.  It is `envp_geo_weight` with the
standard-input factor replaced by the input file's. -/
def file_envp_geo_weight (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) : Rat :=
  if c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) then
    envp_point r q c.core_envp * geo_point p (fs_file pth c.core_fs).length
  else 0

/-- The weight at a core of the family: one factor per coordinate. -/
theorem file_envp_geo_weight_match (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (es : List (List byte)) (d : List byte) :
    file_envp_geo_weight p r q argv fs0 pth s (file_envp_core argv fs0 pth s es d)
      = envp_point r q es * geo_point p d.length := by
  unfold file_envp_geo_weight
  split
  · rw [core_envp_file_envp_core, fs_file_file_envp_core]
  · next hne =>
    exfalso
    apply hne
    rw [core_envp_file_envp_core, fs_file_file_envp_core]

/-- The weight is zero off the template. -/
theorem file_envp_geo_weight_mismatch (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) :
    c ≠ file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) →
    file_envp_geo_weight p r q argv fs0 pth s c = 0 := by
  intro Hne
  unfold file_envp_geo_weight
  split
  · next heq => exact absurd heq Hne
  · rfl

/-- All six factors of the family's weight at once, in the shape the
specification quotes. -/
theorem file_envp_geo_weight_closed_form (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (es : List (List byte)) (d : List byte) :
    file_envp_geo_weight p r q argv fs0 pth s (file_envp_core argv fs0 pth s es d)
      = r * Qpow (1 - r) es.length * entries_geo_product q es
        * (p * Qpow (1 - p) d.length * Qpow (1 / 256) d.length) := by
  rw [file_envp_geo_weight_match, envp_point_closed_form, geo_point_closed_form]

/-- The weight is nonnegative at every core, which is the distribution's one
field. -/
theorem file_envp_geo_weight_nonneg (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) :
    0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ c : FinCore, 0 ≤ file_envp_geo_weight p r q argv fs0 pth s c := by
  intro Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 c
  unfold file_envp_geo_weight
  split
  · refine Rat.mul_nonneg ?_ ?_
    · apply envp_point_nonneg <;> assumption
    · apply geo_point_nonneg <;> assumption
  · exact Rat.le_refl

/-- The distribution.  Mass `1` is declared, as everywhere in this library, and
the six side conditions are the constructor's arguments; no strict inequality is
demanded here, the lower certificate asks for the three it needs itself. -/
def file_envp_geometric (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) : CoreDistribution where
  cd_weight := file_envp_geo_weight p r q argv fs0 pth s
  cd_mass := 1
  cd_nonneg := file_envp_geo_weight_nonneg p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1

/-- The family's weight field, as a rewrite rule; Rocq reaches it with
`cbn [cd_weight file_envp_geometric]`. -/
private theorem cd_weight_file_envp_geometric (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      = file_envp_geo_weight p r q argv fs0 pth s := rfl

/-- The family's declared mass, as a rewrite rule. -/
private theorem cd_mass_file_envp_geometric (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    cd_mass (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) = 1 := rfl

/-! ## The two coordinates, recombined -/

/-- Every core over the fixed argv, base file system and standard input whose
environment comes from `A` and whose file contents come from `B`. -/
def file_envp_product (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (A : List (List (List byte))) (B : List (List byte)) : List FinCore :=
  A.flatMap (fun es => B.map (file_envp_core argv fs0 pth s es))

/-- A core whose two coordinates come from the two enumerations is in the
product. -/
theorem In_file_envp_product (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (A : List (List (List byte))) (B : List (List byte))
    (es : List (List byte)) (d : List byte) :
    es ∈ A → d ∈ B →
    file_envp_core argv fs0 pth s es d ∈ file_envp_product argv fs0 pth s A B := by
  intro HA HB
  exact List.mem_flatMap.mpr ⟨es, HA, List.mem_map.mpr ⟨d, HB, rfl⟩⟩

/-- One block of the product weighs the file-contents sum times the
environment's weight. -/
theorem qsum_file_envp_block (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (es : List (List byte)) (B : List (List byte)) :
    qsum (file_envp_geo_weight p r q argv fs0 pth s)
        (B.map (file_envp_core argv fs0 pth s es))
      = qsum (fun d => geo_point p d.length) B * envp_point r q es := by
  rw [qsum_map]
  rw [qsum_ext _
    (fun d => envp_point r q es * geo_point p d.length) B
    (fun d _ => file_envp_geo_weight_match p r q argv fs0 pth s es d)]
  rw [qsum_scale]
  exact Rat.mul_comm _ _

/-- The product's sum is the product of the two coordinates' sums.  This
identity is the only place the coordinates meet. -/
theorem qsum_file_envp_product (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (A : List (List (List byte))) (B : List (List byte)) :
    qsum (file_envp_geo_weight p r q argv fs0 pth s) (file_envp_product argv fs0 pth s A B)
      = qsum (envp_point r q) A * qsum (fun d => geo_point p d.length) B := by
  unfold file_envp_product
  rw [qsum_flat_map]
  rw [qsum_ext _
    (fun es => qsum (fun d => geo_point p d.length) B * envp_point r q es) A
    (fun es _ => qsum_file_envp_block p r q argv fs0 pth s es B)]
  rw [qsum_scale]
  exact Rat.mul_comm _ _

/-- The product of two duplicate-free enumerations repeats nothing: a core
determines its file contents and its environment. -/
theorem NoDup_file_envp_product (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (A : List (List (List byte))) (B : List (List byte)) :
    A.Nodup → B.Nodup → (file_envp_product argv fs0 pth s A B).Nodup := by
  intro HA HB
  unfold file_envp_product
  apply NoDup_flat_map
  · exact HA
  · intro es _
    apply NoDup_map_inj
    · intro x y _ _ Heq
      exact file_core_inj argv es fs0 pth s x y Heq
    · exact HB
  · intro es1 es2 c _ _ H1 H2
    obtain ⟨d1, _, Hd1⟩ := List.mem_map.mp H1
    obtain ⟨d2, _, Hd2⟩ := List.mem_map.mp H2
    have Henv : (file_envp_core argv fs0 pth s es1 d1).core_envp
        = (file_envp_core argv fs0 pth s es2 d2).core_envp := by rw [Hd1, Hd2]
    rw [core_envp_file_envp_core, core_envp_file_envp_core] at Henv
    exact Henv

/-! ## The cylinder bound over cores -/

/-- The cores this bound is about: the fixed argv, base file system and standard
input, an environment extending `es` and file contents extending `bs`. -/
def in_file_envp_cylinder (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (es : List (List byte)) (bs : List byte) (c : FinCore) : Prop :=
  ∃ eext ext, c = file_envp_core argv fs0 pth s (es ++ eext) (bs ++ ext)

/-- The cylinder's mass: what the two coordinates contribute, `envp_factor` on
one and `geo_mass` on the other. -/
def file_envp_geometric_cylinder_mass (p r q : Rat) (es : List (List byte))
    (bs : List byte) : Rat :=
  envp_factor r q es * geo_mass p bs.length

/-- The cylinder mass with both coordinates' factors written out. -/
theorem file_envp_geometric_cylinder_mass_closed_form (p r q : Rat)
    (es : List (List byte)) (bs : List byte) :
    file_envp_geometric_cylinder_mass p r q es bs
      = Qpow (1 - r) es.length * entries_geo_product q es
        * (Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length) := by
  unfold file_envp_geometric_cylinder_mass
  rw [envp_factor_closed_form, geo_mass_closed_form]

/-- The bound over cores: a duplicate-free list of cores lying in the cylinder
weighs at most the cylinder's mass.  Three depths are read off the list itself —
how many entries an environment has, how long an entry is, how long the input
file is — and each coordinate's bound is the one its own family proved. -/
theorem file_envp_geo_weight_cylinder_bound (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ (es : List (List byte)) (bs : List byte) (cs : List FinCore),
      cs.Nodup →
      (∀ c, c ∈ cs → in_file_envp_cylinder argv fs0 pth s es bs c) →
      qsum (file_envp_geo_weight p r q argv fs0 pth s) cs
        ≤ file_envp_geometric_cylinder_mass p r q es bs := by
  intro Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs cs Hnd Hcyl
  have hincl : cs ⊆ file_envp_product argv fs0 pth s
      (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
      (bytes_cyl bs (cores_file_depth pth cs)) := by
    intro c Hc
    obtain ⟨eext, ext, Heq⟩ := Hcyl c Hc
    have Henvp := cores_envp_depth_ge cs c Hc
    have Hfile := cores_file_depth_ge pth cs c Hc
    rw [Heq, core_envp_file_envp_core, List.length_append] at Henvp
    rw [Heq, fs_file_file_envp_core, List.length_append] at Hfile
    rw [Heq]
    apply In_file_envp_product
    · apply envp_enum_complete
      · omega
      · intro e He
        apply cores_entry_depth_gt cs c e Hc
        rw [Heq, core_envp_file_envp_core]
        exact List.mem_append_right _ He
    · exact bytes_cyl_In (cores_file_depth pth cs) bs ext (by omega)
  refine Rat.le_trans
    (qsum_core_incl_le (file_envp_geo_weight p r q argv fs0 pth s) cs _
      (file_envp_geo_weight_nonneg p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd hincl) ?_
  rw [qsum_file_envp_product]
  unfold file_envp_geometric_cylinder_mass
  refine rat_mul_le_mul_nonneg ?_ ?_ ?_ ?_
  · exact qsum_nonneg _ _ (fun x _ => by apply envp_point_nonneg <;> assumption)
  · exact envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ es
  · exact qsum_nonneg _ _ (fun x _ => by apply geo_point_nonneg <;> assumption)
  · exact bytes_cyl_sum_le p Hp0 Hp1 _ bs

/-! ## The file-and-environment family's exports -/

/-- The export: a list of records with duplicate-free cores, all lying in the
cylinder over an environment prefix and a file-contents prefix, weighs at most
that cylinder's mass.  The charge depends on both coordinates, which is what
this family exists for. -/
theorem file_envp_geometric_bound (p r q : Rat) (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (es : List (List byte)) (bs : List byte)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → in_file_envp_cylinder argv fs0 pth s es bs (fin_core f)) →
    core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ file_envp_geometric_cylinder_mass p r q es bs := by
  intro Hnd Hcyl
  rw [cd_weight_file_envp_geometric, core_sum_map_fin_core]
  refine file_envp_geo_weight_cylinder_bound p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hin, Hf⟩ := List.mem_map.mp Hc
  rw [← Hf]
  exact Hcyl f Hin

/-- The launch-time test as a boolean, so that `List.filter` can use it: this
family fixes argv, standard input and the base file system, so a core weighs
something only when it is the template with both its own coordinates plugged
in. -/
def matches_argv_file_fs (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (c : FinCore) : Bool :=
  if c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) then true else false

/-- A `false` test is a core off the template. -/
theorem matches_argv_file_fs_false (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (c : FinCore) :
    matches_argv_file_fs argv fs0 pth s c = false →
    c ≠ file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) := by
  intro H
  unfold matches_argv_file_fs at H
  split at H
  · exact Bool.noConfusion H
  · next hne => exact hne

/-- A `true` test is a core on the template. -/
theorem matches_argv_file_fs_true (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (c : FinCore) :
    matches_argv_file_fs argv fs0 pth s c = true →
    c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) := by
  intro H
  unfold matches_argv_file_fs at H
  split at H
  · next heq => exact heq
  · exact Bool.noConfusion H

/-- The cylinder bound slackened the only way it can be: each record is in the
cylinder, or its core misses the fixed argv, standard input or base file system
and therefore weighs nothing. -/
theorem file_envp_geometric_bound_or_off_environment (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (es : List (List byte)) (bs : List byte)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l →
      in_file_envp_cylinder argv fs0 pth s es bs (fin_core f)
      ∨ matches_argv_file_fs argv fs0 pth s (fin_core f) = false) →
    core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ file_envp_geometric_cylinder_mass p r q es bs := by
  intro Hnd Hor
  rw [cd_weight_file_envp_geometric, core_sum_map_fin_core]
  rw [qsum_filter (file_envp_geo_weight p r q argv fs0 pth s)
    (matches_argv_file_fs argv fs0 pth s) (l.map fin_core)
    (fun c Hc => file_envp_geo_weight_mismatch p r q argv fs0 pth s c
      (matches_argv_file_fs_false argv fs0 pth s c Hc))]
  refine file_envp_geo_weight_cylinder_bound p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs _ (nodup_filter _ _ Hnd) ?_
  intro c Hc
  rw [List.mem_filter] at Hc
  obtain ⟨Hin, Hm⟩ := Hc
  obtain ⟨f, Hinl, Hf⟩ := List.mem_map.mp Hin
  rcases Hor f Hinl with Hcyl | Hoff
  · rw [← Hf]
    exact Hcyl
  · rw [Hf] at Hoff
    rw [Hoff] at Hm
    exact Bool.noConfusion Hm

/-- The upper certificate: every admissible list weighs at most the declared
mass `1`.  It is the disjunctive bound at the two empty prefixes, where the
disjunction is exhaustive and both cylinder masses are `1`. -/
theorem file_envp_geometric_mass_upper (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ cd_mass (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) := by
  intro Hnd
  rw [cd_mass_file_envp_geometric]
  refine Rat.le_trans (file_envp_geometric_bound_or_off_environment p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 [] [] l Hnd ?_) ?_
  · intro f Hf
    cases hm : matches_argv_file_fs argv fs0 pth s (fin_core f) with
    | true =>
      exact Or.inl ⟨(fin_core f).core_envp, fs_file pth (fin_core f).core_fs,
        matches_argv_file_fs_true argv fs0 pth s (fin_core f) hm⟩
    | false => exact Or.inr rfl
  · refine Qle_of_Qeq _ _ ?_
    simp only [file_envp_geometric_cylinder_mass, List.length_nil, envp_factor,
      geo_mass_closed_form, Qpow_0, Rat.mul_one]

/-! ## Bounds that charge the environment nothing -/

/-- A list whose cores match the fixed argv, standard input and base file system
and whose file contents all come from `B` weighs at most what `B` weighs: the
environment coordinate is charged its whole declared `1` and nothing about the
environment is assumed. -/
theorem file_envp_geo_weight_file_family_bound (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ (B : List (List byte)) (SB : Rat) (cs : List FinCore),
      qsum (fun d => geo_point p d.length) B ≤ SB →
      cs.Nodup →
      (∀ c, c ∈ cs →
        c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs)
        ∧ fs_file pth c.core_fs ∈ B) →
      qsum (file_envp_geo_weight p r q argv fs0 pth s) cs ≤ SB := by
  intro Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 B SB cs HB Hnd Hall
  have hincl : cs ⊆ file_envp_product argv fs0 pth s
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) B := by
    intro c Hc
    obtain ⟨Hmatch, Hfile⟩ := Hall c Hc
    have Hins : ([] ++ c.core_envp)
        ∈ envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs) := by
      apply envp_enum_complete
      · exact cores_envp_depth_ge cs c Hc
      · intro e He
        exact cores_entry_depth_gt cs c e Hc He
    rw [List.nil_append] at Hins
    have Hprod := In_file_envp_product argv fs0 pth s
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) B
      c.core_envp (fs_file pth c.core_fs) Hins Hfile
    rw [← Hmatch] at Hprod
    exact Hprod
  refine Rat.le_trans
    (qsum_core_incl_le (file_envp_geo_weight p r q argv fs0 pth s) cs _
      (file_envp_geo_weight_nonneg p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd hincl) ?_
  rw [qsum_file_envp_product]
  refine Rat.le_trans (rat_mul_le_mul_nonneg ?_ ?_ ?_ HB) (Qle_of_Qeq _ _ (Rat.one_mul SB))
  · exact qsum_nonneg _ _ (fun x _ => by apply envp_point_nonneg <;> assumption)
  · refine Rat.le_trans (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ []) ?_
    exact Qle_of_Qeq _ _ (by simp only [envp_factor])
  · exact qsum_nonneg _ _ (fun x _ => by apply geo_point_nonneg <;> assumption)

/-- The length slice: a list drawn from one file-length slice weighs at most
`p * (1 - p) ^ n`, with no `1/256` left in it and nothing charged for the
environment.  No attainment is claimed, because a slice at a fixed file length
still holds one core per environment. -/
theorem file_envp_geometric_slice_bound (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l →
      fin_core f = file_envp_core argv fs0 pth s f.fin_envp (fs_file pth f.fin_image_fs)
      ∧ (fs_file pth f.fin_image_fs).length = n) →
    core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ p * Qpow (1 - p) n := by
  intro Hnd Hall
  rw [cd_weight_file_envp_geometric, core_sum_map_fin_core]
  refine file_envp_geo_weight_file_family_bound p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    (byte_lists n) (p * Qpow (1 - p) n) _ (Qle_of_Qeq _ _ (byte_lists_sum p n)) Hnd ?_
  intro c Hc
  obtain ⟨f, Hin, Hf⟩ := List.mem_map.mp Hc
  obtain ⟨Henv, Hlen⟩ := Hall f Hin
  subst Hf
  refine ⟨?_, ?_⟩
  · exact Henv
  · have hfs : fs_file pth (fin_core f).core_fs = fs_file pth f.fin_image_fs := rfl
    rw [hfs, ← Hlen]
    exact byte_lists_complete _

/-- A list confined to input files of length at most `n` weighs at most
`1 - (1 - p) ^ (n + 1)`, the partial sum at its own horizon; the environment is
charged nothing, and the tail past the horizon is what the next lemma is made
of. -/
theorem file_envp_geometric_bound_by_max_length (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → (fs_file pth f.fin_image_fs).length ≤ n) →
    core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
      ≤ 1 - Qpow (1 - p) (n + 1) := by
  intro Hnd Hlen
  rw [cd_weight_file_envp_geometric, core_sum_map_fin_core]
  rw [qsum_filter (file_envp_geo_weight p r q argv fs0 pth s)
    (matches_argv_file_fs argv fs0 pth s) (l.map fin_core)
    (fun c Hc => file_envp_geo_weight_mismatch p r q argv fs0 pth s c
      (matches_argv_file_fs_false argv fs0 pth s c Hc))]
  refine file_envp_geo_weight_file_family_bound p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    (short_inputs (n + 1)) (1 - Qpow (1 - p) (n + 1)) _
    (Qle_of_Qeq _ _ (by rw [short_inputs_sum, geo_prefix_sum_closed]))
    (nodup_filter _ _ Hnd) ?_
  intro c Hc
  rw [List.mem_filter] at Hc
  obtain ⟨Hin, Hm⟩ := Hc
  refine ⟨matches_argv_file_fs_true argv fs0 pth s c Hm, ?_⟩
  apply short_inputs_complete
  obtain ⟨f, Hinl, Hf⟩ := List.mem_map.mp Hin
  have Hle := Hlen f Hinl
  subst Hf
  have hfs : (fs_file pth (fin_core f).core_fs).length
      = (fs_file pth f.fin_image_fs).length := rfl
  rw [hfs]
  omega

/-! ## The declared mass is a supremum and not a maximum -/

/-- For `p < 1` no admissible list weighs the declared mass: the list's own
longest input file is a horizon, and past it sits a positive tail the list does
not collect.  The environment coordinate needs no hypothesis. -/
theorem file_envp_geometric_mass_not_attained (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput,
      (l.map fin_core).Nodup →
      core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
        < cd_mass (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) := by
  intro Hlt l Hnd
  rw [cd_mass_file_envp_geometric]
  refine rat_lt_of_le_of_lt
    (file_envp_geometric_bound_by_max_length p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
      (list_max (l.map (fun f => (fs_file pth f.fin_image_fs).length))) l Hnd ?_) ?_
  · intro f Hf
    exact list_max_ge _ _ (List.mem_map.mpr ⟨f, Hf, rfl⟩)
  · exact rat_one_sub_lt_one _ (Qpow_pos (1 - p) _ ((Rat.lt_iff_sub_pos p 1).mp Hlt))

/-- The same fact under the name a reader looks for. -/
theorem file_envp_geometric_mass_supremum_not_maximum (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput,
      (l.map fin_core).Nodup →
      ¬ (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
              Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
          = cd_mass (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) := by
  intro Hlt l Hnd
  exact Rat.ne_of_lt (file_envp_geometric_mass_not_attained p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hlt l Hnd)

/-! ## The lower certificate -/

/-- The witness family: over the fixed argv, base file system and standard
input, one record per environment-and-contents pair drawn from the two prefix
enumerations.  These records are not claimed valid and not claimed rejected. -/
def file_envp_geo_lower_witness (argv : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (M L k : Nat) : List FinProcInput :=
  (file_envp_product argv fs0 pth s (envps_upto L M) (short_inputs k)).map core_input

/-- The witness's cores are exactly the product of the two enumerations. -/
theorem map_fin_core_file_envp_geo_lower_witness (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (M L k : Nat) :
    (file_envp_geo_lower_witness argv fs0 pth s M L k).map fin_core
      = file_envp_product argv fs0 pth s (envps_upto L M) (short_inputs k) := by
  unfold file_envp_geo_lower_witness
  exact map_fin_core_core_input _

/-- The witness is admissible: its cores repeat nothing. -/
theorem file_envp_geo_lower_witness_nodup (argv : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (M L k : Nat) :
    ((file_envp_geo_lower_witness argv fs0 pth s M L k).map fin_core).Nodup := by
  rw [map_fin_core_file_envp_geo_lower_witness]
  exact NoDup_file_envp_product argv fs0 pth s _ _ (envps_upto_nodup L M) (short_inputs_nodup k)

/-- The witness at each triple of depths weighs exactly the product of the two
coordinates' partial sums. -/
theorem file_envp_geometric_mass_lower_witness (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (M L k : Nat) :
    ((file_envp_geo_lower_witness argv fs0 pth s M L k).map fin_core).Nodup
    ∧ core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))
        (file_envp_geo_lower_witness argv fs0 pth s M L k)
        = envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k) := by
  refine ⟨file_envp_geo_lower_witness_nodup argv fs0 pth s M L k, ?_⟩
  rw [cd_weight_file_envp_geometric, core_sum_map_fin_core,
    map_fin_core_file_envp_geo_lower_witness, qsum_file_envp_product,
    qsum_envp_point_envps_upto, short_inputs_sum, geo_prefix_sum_closed]

/-- The lower certificate: for every margin there is an admissible list weighing
at least the declared mass minus that margin.  The three depths come from
`envp_stdin_depths_above` and the arithmetic from `envp_stdin_margin_at_depths`,
both of which this family consumes unchanged. -/
theorem file_envp_geometric_mass_lower_certificate (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (eps : Rat) :
    0 < p → 0 < r → 0 < q → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) - eps
          ≤ core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
              Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l := by
  intro Hppos Hrpos Hqpos Heps
  obtain ⟨M, L, k, _, _, Hsum, _⟩ :=
    envp_stdin_depths_above p r q eps 0 0 Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps
  refine ⟨file_envp_geo_lower_witness argv fs0 pth s M L k,
    file_envp_geo_lower_witness_nodup argv fs0 pth s M L k, ?_⟩
  rw [(file_envp_geometric_mass_lower_witness p r q argv fs0 pth s
      Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k).2,
    cd_mass_file_envp_geometric]
  exact envp_stdin_margin_at_depths p r q eps M L k Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum

/-! ## Non-vacuity: the environment carries mass here too -/

/-- `file_geo_weight`'s environment instance: a core whose environment is not
the fixed one weighs zero. -/
theorem file_geo_weight_off_envp_zero (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    c.core_envp ≠ envp → file_geo_weight p argv envp fs0 pth s c = 0 := by
  intro Hne
  apply file_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_envp Heq)

/-- A core whose argv is not the fixed one weighs zero in this family. -/
theorem file_envp_geo_weight_off_argv_zero (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    c.core_argv ≠ argv → file_envp_geo_weight p r q argv fs0 pth s c = 0 := by
  intro Hne
  apply file_envp_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- A core over a non-canonical launch-time environment carrying the input file:
one entry, the single byte `A`, and the empty file at `file_example_path`.  It is
not claimed valid; it is where the two file families disagree. -/
def file_envp_example_named : FinCore :=
  file_envp_core [] [] file_example_path [] [[Z_to_bv 8 65]] []

/-- The bite this family exists for, both halves on one core: `file_geometric`
over the empty environment weighs `file_envp_example_named` exactly zero, while
this family weighs it strictly positively. -/
theorem file_envp_geometric_envp_bites (p r q : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 < p → p < 1 → 0 < r → r < 1 → 0 < q → q < 1 →
    cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
        file_envp_example_named = 0
    ∧ 0 < cd_weight (file_envp_geometric p r q [] [] file_example_path []
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) file_envp_example_named := by
  intro Hppos Hplt Hrpos Hrlt Hqpos Hqlt
  constructor
  · show file_geo_weight p [] [] [] file_example_path [] file_envp_example_named = 0
    apply file_geo_weight_off_envp_zero
    unfold file_envp_example_named
    rw [core_envp_file_envp_core]
    exact List.cons_ne_nil _ _
  · show 0 < file_envp_geo_weight p r q [] [] file_example_path [] file_envp_example_named
    unfold file_envp_example_named
    rw [file_envp_geo_weight_match]
    refine Rat.mul_pos ?_ ?_
    · apply envp_point_pos <;> assumption
    · apply geo_point_pos <;> assumption

/-- The family is still not constant: a core whose argv misses the fixed one
weighs exactly zero, while the canonical core weighs something. -/
theorem file_envp_geometric_bites (p r q : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 < p → p < 1 → 0 < r → r < 1 → 0 < q → q < 1 →
    0 < cd_weight (file_envp_geometric p r q [] [] file_example_path []
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) file_example_core
    ∧ cd_weight (file_envp_geometric p r q [] [] file_example_path []
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) geo_example_other = 0 := by
  intro Hppos Hplt Hrpos Hrlt Hqpos Hqlt
  constructor
  · show 0 < file_envp_geo_weight p r q [] [] file_example_path [] file_example_core
    have hcore : file_example_core = file_envp_core [] [] file_example_path [] [] [] := rfl
    rw [hcore, file_envp_geo_weight_match]
    refine Rat.mul_pos ?_ ?_
    · apply envp_point_pos <;> assumption
    · apply geo_point_pos <;> assumption
  · show file_envp_geo_weight p r q [] [] file_example_path [] geo_example_other = 0
    apply file_envp_geo_weight_off_argv_zero
    exact List.cons_ne_nil _ _

/-! ## Non-vacuity: duplicate-freedom is load-bearing here too -/

/-- The member of the family at `p = r = q = 1`: stop immediately on every axis.
It is the point mass on the core with no environment and an empty input file. -/
def file_envp_point_cd : CoreDistribution :=
  file_envp_geometric 1 1 1 [] [] file_example_path []
    Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl

/-- Duplicate-freedom is load-bearing for the cylinder bound: offer the same
core twice and the sum is `2` against a cylinder mass of `1`.  All three
conjuncts are needed, as at `file_geometric_bound_needs_nodup`. -/
theorem file_envp_geometric_bound_needs_nodup :
    ¬ (([file_empty_input, file_empty_input] : List FinProcInput).map fin_core).Nodup
    ∧ (∀ f, f ∈ ([file_empty_input, file_empty_input] : List FinProcInput) →
        in_file_envp_cylinder [] [] file_example_path [] [] [] (fin_core f))
    ∧ ¬ (core_sum (cd_weight file_envp_point_cd) [file_empty_input, file_empty_input]
        ≤ file_envp_geometric_cylinder_mass 1 1 1 [] []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    rw [List.map_cons, List.map_cons, List.map_nil, List.nodup_cons] at Hnd
    exact Hnd.1 (List.Mem.head _)
  · intro f Hf
    rcases List.mem_cons.mp Hf with rfl | Hf2
    · exact ⟨[], [], rfl⟩
    · rcases List.mem_cons.mp Hf2 with rfl | Hf3
      · exact ⟨[], [], rfl⟩
      · cases Hf3
  · -- Closed rational arithmetic: `2 ≤ 1` is false, decided by the kernel the
    -- way `Measure.lean` decides its own closed comparison.
    decide +kernel

/-! ## The six degenerate members, each pinned -/

/-- At `p = 0` the weight vanishes identically. -/
theorem file_envp_geo_weight_zero_at_zero_p (r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    file_envp_geo_weight 0 r q argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  split
  · simp only [geo_point, Rat.zero_mul, Rat.mul_zero]
  · rfl

/-- At `r = 0` the weight vanishes identically. -/
theorem file_envp_geo_weight_zero_at_zero_r (p q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    file_envp_geo_weight p 0 q argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  split
  · simp only [envp_point, Rat.zero_mul]
  · rfl

/-- At `q = 0` every core with a non-empty environment weighs zero. -/
theorem file_envp_geo_weight_zero_at_zero_q (p r : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    c.core_envp ≠ [] → file_envp_geo_weight p r 0 argv fs0 pth s c = 0 := by
  intro Hne
  unfold file_envp_geo_weight
  split
  · cases h : c.core_envp with
    | nil => exact absurd h Hne
    | cons e es =>
      -- `cases` has already replaced the environment in the goal.
      simp only [envp_point, envp_factor, geo_point, Rat.zero_mul, Rat.mul_zero]
  · rfl

/-- At `p = 1` every core with a non-empty input file weighs zero. -/
theorem file_envp_geo_weight_collapses_at_one_p (r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    fs_file pth c.core_fs ≠ [] → file_envp_geo_weight 1 r q argv fs0 pth s c = 0 := by
  intro Hne
  unfold file_envp_geo_weight
  split
  · cases h : fs_file pth c.core_fs with
    | nil => exact absurd h Hne
    | cons b d =>
      -- `cases` has already replaced the file contents in the goal.
      simp only [geo_point, geo_mass, List.length_cons, Qpow_succ, Rat.sub_self,
        Rat.zero_mul, Rat.mul_zero]
  · rfl

/-- At `r = 1` this family is `file_geometric` over the empty launch-time
environment, weight for weight and at every core.  So `r < 1` is genuinely asked
for by the bite above. -/
theorem file_envp_geo_weight_collapses_at_one_r (p q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    file_envp_geo_weight p 1 q argv fs0 pth s c = file_geo_weight p argv [] fs0 pth s c := by
  unfold file_envp_geo_weight file_geo_weight file_envp_core
  split
  · next Hm =>
    split
    · next He =>
      have Henv : c.core_envp = [] := congrArg FinCore.core_envp He
      rw [Henv]
      simp only [envp_point, envp_factor, Rat.one_mul]
    · next He =>
      cases h : c.core_envp with
      | nil => exact absurd (by rw [← h]; exact Hm) He
      | cons e es =>
        simp only [envp_point, envp_factor, Rat.sub_self, Rat.zero_mul, Rat.mul_zero]
  · next Hm =>
    split
    · next He =>
      exfalso
      apply Hm
      have Henv : c.core_envp = [] := congrArg FinCore.core_envp He
      rw [Henv]
      exact He
    · rfl

/-- The collapse at `r = 1`, read on the distributions. -/
theorem file_envp_geometric_collapses_at_one_r (p q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    cd_weight (file_envp_geometric p 1 q argv fs0 pth s Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1) c
      = cd_weight (file_geometric p argv [] fs0 pth s Hp0 Hp1) c := by
  show file_envp_geo_weight p 1 q argv fs0 pth s c = file_geo_weight p argv [] fs0 pth s c
  exact file_envp_geo_weight_collapses_at_one_r p q argv fs0 pth s c

/-- The blindness at `r = 1`: every non-empty environment weighs zero. -/
theorem file_envp_geometric_envp_needs_r_below_one (p q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    c.core_envp ≠ [] →
    cd_weight (file_envp_geometric p 1 q argv fs0 pth s Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1) c
      = 0 := by
  intro Hne
  rw [file_envp_geometric_collapses_at_one_r p q argv fs0 pth s Hp0 Hp1 Hq0 Hq1 c]
  show file_geo_weight p argv [] fs0 pth s c = 0
  exact file_geo_weight_off_envp_zero p argv [] fs0 pth s c Hne

/-- The blindness at `q = 0`: every non-empty environment weighs zero. -/
theorem file_envp_geometric_envp_needs_positive_q (p r : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore) :
    c.core_envp ≠ [] →
    cd_weight (file_envp_geometric p r 0 argv fs0 pth s Hp0 Hp1 Hr0 Hr1
      Rat.le_refl Qle_0_1) c = 0 := by
  intro Hne
  show file_envp_geo_weight p r 0 argv fs0 pth s c = 0
  exact file_envp_geo_weight_zero_at_zero_q p r argv fs0 pth s c Hne

/-- At `q = 1` an environment holding any non-empty entry weighs zero, while
environments of empty entries keep their weight. -/
theorem file_envp_geo_weight_zero_at_one_q (p r : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) (e : List byte) :
    e ∈ c.core_envp → e ≠ [] → file_envp_geo_weight p r 1 argv fs0 pth s c = 0 := by
  intro Hin Hne
  unfold file_envp_geo_weight
  split
  · simp only [envp_point]
    rw [envp_factor_zero_at_one_q r c.core_envp e Hin Hne]
    simp only [Rat.mul_zero, Rat.zero_mul]
  · rfl

/-- The blindness at `q = 1`, read on the distribution. -/
theorem file_envp_geometric_envp_needs_q_below_one (p r : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore) (e : List byte) :
    e ∈ c.core_envp → e ≠ [] →
    cd_weight (file_envp_geometric p r 1 argv fs0 pth s Hp0 Hp1 Hr0 Hr1
      Qle_0_1 Rat.le_refl) c = 0 := by
  intro Hin Hne
  show file_envp_geo_weight p r 1 argv fs0 pth s c = 0
  exact file_envp_geo_weight_zero_at_one_q p r argv fs0 pth s c e Hin Hne

/-- The hypothesis at `q = 1` names a non-empty entry and not a non-empty
environment: the environment of one empty entry still weighs something. -/
theorem file_envp_geo_weight_at_one_q_needs_a_non_empty_entry :
    file_envp_geo_weight (1 / 2) (1 / 5) 1 [] [] file_example_path []
        file_envp_example_named = 0
    ∧ 0 < file_envp_geo_weight (1 / 2) (1 / 5) 1 [] [] file_example_path []
        (file_envp_core [] [] file_example_path [] [[]] []) := by
  constructor
  · refine file_envp_geo_weight_zero_at_one_q (1 / 2) (1 / 5) [] [] file_example_path []
      file_envp_example_named [Z_to_bv 8 65] ?_ ?_
    · show [Z_to_bv 8 65] ∈ file_envp_example_named.core_envp
      unfold file_envp_example_named
      rw [core_envp_file_envp_core]
      exact List.Mem.head _
    · exact List.cons_ne_nil _ _
  · rw [file_envp_geo_weight_match]
    decide +kernel

/-- At `p = 1` every core with a non-empty input file weighs zero, so the family
goes blind to the coordinate both file families were built for. -/
theorem file_envp_geometric_needs_p_below_one (r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    fs_file pth c.core_fs ≠ [] →
    cd_weight (file_envp_geometric 1 r q argv fs0 pth s Qle_0_1 Rat.le_refl
      Hr0 Hr1 Hq0 Hq1) c = 0 := by
  intro Hne
  show file_envp_geo_weight 1 r q argv fs0 pth s c = 0
  exact file_envp_geo_weight_collapses_at_one_p r q argv fs0 pth s c Hne

/-- The strictness at `p` is load-bearing for the lower certificate: at `p = 0`
every admissible list weighs zero while the declared mass stays `1`, so no list
comes within `1/2` of it. -/
theorem file_envp_geometric_mass_lower_needs_positive (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    (∀ l : List FinProcInput,
      core_sum (cd_weight (file_envp_geometric 0 r q argv fs0 pth s Rat.le_refl Qle_0_1
        Hr0 Hr1 Hq0 Hq1)) l = 0)
    ∧ ¬ (cd_mass (file_envp_geometric 0 r q argv fs0 pth s Rat.le_refl Qle_0_1
        Hr0 Hr1 Hq0 Hq1) - (1 / 2) ≤ 0) := by
  constructor
  · intro l
    apply core_sum_zero_weight
    intro c
    show file_envp_geo_weight 0 r q argv fs0 pth s c = 0
    exact file_envp_geo_weight_zero_at_zero_p r q argv fs0 pth s c
  · show ¬ ((1 : Rat) - (1 / 2) ≤ 0)
    decide +kernel

/-! ## The argv/path coupling -/

/-- The obligation a task owes when it passes argv and the varied path
independently: the path occurs somewhere in the fixed argv.  It is the
syntactic proxy for "the program opens the file at this path", which is a claim
about the program and not mechanizable here. -/
def argv_names_path (argv : List (List byte)) (pth : Fs.path) : Prop := pth ∈ argv

/-- The argv of the common driver shape: a program name, then the input file's
path. -/
def path_argv (prog : List byte) (pth : Fs.path) : List (List byte) := [prog, pth]

/-- That shape names the path. -/
theorem path_argv_names_path (prog : List byte) (pth : Fs.path) :
    argv_names_path (path_argv prog pth) pth :=
  List.Mem.tail _ (List.Mem.head _)

/-- The whole-file family with the path passed once, so the two slots cannot
disagree. -/
def file_geometric_argv1 (p : Rat) (prog : List byte) (envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    CoreDistribution :=
  file_geometric p (path_argv prog pth) envp fs0 pth s Hp0 Hp1

/-- The environment-varying file family with the path passed once. -/
def file_envp_geometric_argv1 (p r q : Rat) (prog : List byte) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) : CoreDistribution :=
  file_envp_geometric p r q (path_argv prog pth) fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1

/-- The coupled whole-file constructor discharges the obligation by
construction. -/
theorem file_geometric_argv1_names_path (p : Rat) (prog : List byte)
    (envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    argv_names_path (path_argv prog pth) pth
    ∧ file_geometric_argv1 p prog envp fs0 pth s Hp0 Hp1
      = file_geometric p (path_argv prog pth) envp fs0 pth s Hp0 Hp1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

/-- The coupled environment-varying constructor discharges it too. -/
theorem file_envp_geometric_argv1_names_path (p r q : Rat) (prog : List byte)
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    argv_names_path (path_argv prog pth) pth
    ∧ file_envp_geometric_argv1 p r q prog fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
      = file_envp_geometric p r q (path_argv prog pth) fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

/-- The header-conditioned family with the path passed once. -/
def file_geometric_prefix_argv1 (hdr : List byte) (p : Rat) (prog : List byte)
    (envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  file_geometric_prefix hdr p (path_argv prog pth) envp fs0 pth s Hp0 Hp1

/-- The coupled header-conditioned constructor discharges the obligation. -/
theorem file_geometric_prefix_argv1_names_path (hdr : List byte) (p : Rat)
    (prog : List byte) (envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    argv_names_path (path_argv prog pth) pth
    ∧ file_geometric_prefix_argv1 hdr p prog envp fs0 pth s Hp0 Hp1
      = file_geometric_prefix hdr p (path_argv prog pth) envp fs0 pth s Hp0 Hp1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

/-- The alphabet-restricted family with the path passed once. -/
def file_geometric_prefix_over_argv1 (alpha : List byte) (Hnd : alpha.Nodup)
    (Hne : alpha ≠ []) (hdr : List byte) (p : Rat) (prog : List byte)
    (envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  file_geometric_prefix_over alpha Hnd Hne hdr p (path_argv prog pth) envp fs0 pth s Hp0 Hp1

/-- The coupled alphabet-restricted constructor discharges the obligation. -/
theorem file_geometric_prefix_over_argv1_names_path (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat) (prog : List byte)
    (envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    argv_names_path (path_argv prog pth) pth
    ∧ file_geometric_prefix_over_argv1 alpha Hnd Hne hdr p prog envp fs0 pth s Hp0 Hp1
      = file_geometric_prefix_over alpha Hnd Hne hdr p (path_argv prog pth) envp fs0
          pth s Hp0 Hp1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

/-! ## What goes wrong when the coupling is violated -/

/-- `Fs.fs_set` touches one key and no other: a lookup at a different key reads
the original file system. -/
theorem fs_lookup_set_other (fs : Fs.Fs) (pth : Fs.path) (d : List byte) (pth' : Fs.path) :
    pth' ≠ pth → Fs.fs_lookup (Fs.fs_set fs pth d) pth' = Fs.fs_lookup fs pth' := by
  intro Hne
  have hpp : Fs.path_eqb pth' pth = false := path_eqb_false_of_ne Hne
  induction fs with
  | nil => simp [Fs.fs_set, Fs.fs_lookup, hpp]
  | cons hd tl ih =>
    obtain ⟨qq, e⟩ := hd
    cases hlt : Fs.path_ltb pth qq with
    | true => simp [Fs.fs_set, Fs.fs_lookup, hlt, hpp]
    | false =>
      cases heq : Fs.path_eqb pth qq with
      | true =>
        have hq : pth = qq := (Fs.path_eqb_eq pth qq).mp heq
        subst hq
        simp [Fs.fs_set, Fs.fs_lookup, hlt, heq, hpp]
      | false => simp [Fs.fs_set, Fs.fs_lookup, hlt, heq, ih]

/-- The file at a different path is the base file system's file. -/
theorem fs_file_set_other (fs0 : Fs.Fs) (pth : Fs.path) (d : List byte) (pth' : Fs.path) :
    pth' ≠ pth → fs_file pth' (Fs.fs_set fs0 pth d) = fs_file pth' fs0 := by
  intro Hne
  unfold fs_file
  rw [fs_lookup_set_other fs0 pth d pth' Hne]

/-- A template core holds the base file system's contents at every other
path. -/
theorem fs_file_file_core_other (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s d : List byte) (pth' : Fs.path) :
    pth' ≠ pth →
    fs_file pth' (file_core argv envp fs0 pth s d).core_fs = fs_file pth' fs0 := by
  intro Hne
  show fs_file pth' (Fs.fs_set fs0 pth d) = fs_file pth' fs0
  exact fs_file_set_other fs0 pth d pth' Hne

/-- A core the whole-file weight does not zero is the template with its own
contents plugged in. -/
theorem file_geo_weight_positive_matches (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    0 < file_geo_weight p argv envp fs0 pth s c →
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) := by
  intro Hpos
  unfold file_geo_weight at Hpos
  split at Hpos
  · next heq => exact heq
  · exact absurd Hpos Rat.lt_irrefl

/-- The same for this file's family. -/
theorem file_envp_geo_weight_positive_matches (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    0 < file_envp_geo_weight p r q argv fs0 pth s c →
    c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) := by
  intro Hpos
  unfold file_envp_geo_weight at Hpos
  split at Hpos
  · next heq => exact heq
  · exact absurd Hpos Rat.lt_irrefl

/-- The collapse: at every path other than the one it varies, every core the
whole-file family weighs holds the base file system's contents. -/
theorem file_geo_weight_blind_off_path (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (pth' : Fs.path) (c : FinCore) :
    pth' ≠ pth → 0 < file_geo_weight p argv envp fs0 pth s c →
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  intro Hne Hpos
  have Heq := file_geo_weight_positive_matches p argv envp fs0 pth s c Hpos
  rw [Heq]
  exact fs_file_file_core_other argv envp fs0 pth s (fs_file pth c.core_fs) pth' Hne

/-- The same collapse for this file's family. -/
theorem file_envp_geo_weight_blind_off_path (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (pth' : Fs.path) (c : FinCore) :
    pth' ≠ pth → 0 < file_envp_geo_weight p r q argv fs0 pth s c →
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  intro Hne Hpos
  have Heq := file_envp_geo_weight_positive_matches p r q argv fs0 pth s c Hpos
  rw [Heq]
  unfold file_envp_core
  exact fs_file_file_core_other argv c.core_envp fs0 pth s (fs_file pth c.core_fs) pth' Hne

/-- Any two cores the whole-file family weighs agree off the varied path. -/
theorem file_geometric_blind_off_path (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (pth' : Fs.path) (c1 c2 : FinCore) :
    pth' ≠ pth →
    0 < cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1) c1 →
    0 < cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1) c2 →
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  intro Hne H1 H2
  replace H1 : 0 < file_geo_weight p argv envp fs0 pth s c1 := H1
  replace H2 : 0 < file_geo_weight p argv envp fs0 pth s c2 := H2
  rw [file_geo_weight_blind_off_path p argv envp fs0 pth s pth' c1 Hne H1,
    file_geo_weight_blind_off_path p argv envp fs0 pth s pth' c2 Hne H2]

/-- Any two cores this family weighs agree off the varied path. -/
theorem file_envp_geometric_blind_off_path (p r q : Rat) (argv : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (pth' : Fs.path)
    (c1 c2 : FinCore) :
    pth' ≠ pth →
    0 < cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) c1 →
    0 < cd_weight (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) c2 →
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  intro Hne H1 H2
  replace H1 : 0 < file_envp_geo_weight p r q argv fs0 pth s c1 := H1
  replace H2 : 0 < file_envp_geo_weight p r q argv fs0 pth s c2 := H2
  rw [file_envp_geo_weight_blind_off_path p r q argv fs0 pth s pth' c1 Hne H1,
    file_envp_geo_weight_blind_off_path p r q argv fs0 pth s pth' c2 Hne H2]

/-! ## The misconfigured instance, exhibited -/

/-- A program name, three bytes long so that the inequalities below are facts
about lengths. -/
def file_example_prog : List byte := [Z_to_bv 8 105, Z_to_bv 8 105, Z_to_bv 8 105]

/-- A second path, two bytes long. -/
def file_other_path : Fs.path := [Z_to_bv 8 105, Z_to_bv 8 105]

/-- The two example paths differ, by length. -/
theorem file_other_path_ne : file_other_path ≠ file_example_path := by
  intro H
  exact absurd (congrArg List.length H) (by decide)

/-- The misconfiguration: an argv that names `file_other_path` while the family
varies `file_example_path`. -/
def file_misconfigured_argv : List (List byte) := [file_example_prog, file_other_path]

/-- The hazard exhibited for the whole-file family: the obligation fails, the
distribution still looks healthy — two cores with different file contents, both
of positive weight — and at the path argv names those two cores hold the same
bytes, so the whole variation is invisible to the program. -/
theorem file_geometric_needs_argv_to_name_the_path (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p → p < 1 →
    ¬ argv_names_path file_misconfigured_argv file_example_path
    ∧ 0 < cd_weight (file_geometric p file_misconfigured_argv [] [] file_example_path []
        Hp0 Hp1) (file_core file_misconfigured_argv [] [] file_example_path [] [])
    ∧ 0 < cd_weight (file_geometric p file_misconfigured_argv [] [] file_example_path []
        Hp0 Hp1) (file_core file_misconfigured_argv [] [] file_example_path []
          [Z_to_bv 8 65])
    ∧ fs_file file_other_path
        (file_core file_misconfigured_argv [] [] file_example_path [] []).core_fs
      = fs_file file_other_path
        (file_core file_misconfigured_argv [] [] file_example_path []
          [Z_to_bv 8 65]).core_fs := by
  intro Hpos Hlt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Hin
    unfold argv_names_path file_misconfigured_argv at Hin
    rcases List.mem_cons.mp Hin with Heq | Hin2
    · exact absurd (congrArg List.length Heq) (by decide)
    · rcases List.mem_cons.mp Hin2 with Heq | Hin3
      · exact file_other_path_ne Heq.symm
      · cases Hin3
  · show 0 < file_geo_weight p file_misconfigured_argv [] [] file_example_path []
      (file_core file_misconfigured_argv [] [] file_example_path [] [])
    rw [file_geo_weight_match]
    apply geo_point_pos <;> assumption
  · show 0 < file_geo_weight p file_misconfigured_argv [] [] file_example_path []
      (file_core file_misconfigured_argv [] [] file_example_path [] [Z_to_bv 8 65])
    rw [file_geo_weight_match]
    apply geo_point_pos <;> assumption
  · rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] []
      file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path []
        [Z_to_bv 8 65] file_other_path file_other_path_ne]

/-- The same hazard for this family, with the environment coordinate left where
it is: two weighted cores over one environment, differing in the input file,
agreeing at the path argv names. -/
theorem file_envp_geometric_needs_argv_to_name_the_path (p r q : Rat) (Hp0 : 0 ≤ p)
    (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 < p → p < 1 → 0 < r → r < 1 → 0 < q → q < 1 →
    ¬ argv_names_path file_misconfigured_argv file_example_path
    ∧ 0 < cd_weight (file_envp_geometric p r q file_misconfigured_argv []
        file_example_path [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
        (file_envp_core file_misconfigured_argv [] file_example_path [] [] [])
    ∧ 0 < cd_weight (file_envp_geometric p r q file_misconfigured_argv []
        file_example_path [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
        (file_envp_core file_misconfigured_argv [] file_example_path [] []
          [Z_to_bv 8 65])
    ∧ fs_file file_other_path
        (file_envp_core file_misconfigured_argv [] file_example_path [] [] []).core_fs
      = fs_file file_other_path
        (file_envp_core file_misconfigured_argv [] file_example_path [] []
          [Z_to_bv 8 65]).core_fs := by
  intro Hppos Hplt Hrpos Hrlt Hqpos Hqlt
  refine ⟨(file_geometric_needs_argv_to_name_the_path p Hp0 Hp1 Hppos Hplt).1, ?_, ?_, ?_⟩
  · show 0 < file_envp_geo_weight p r q file_misconfigured_argv [] file_example_path []
      (file_envp_core file_misconfigured_argv [] file_example_path [] [] [])
    rw [file_envp_geo_weight_match]
    refine Rat.mul_pos ?_ ?_
    · apply envp_point_pos <;> assumption
    · apply geo_point_pos <;> assumption
  · show 0 < file_envp_geo_weight p r q file_misconfigured_argv [] file_example_path []
      (file_envp_core file_misconfigured_argv [] file_example_path [] [] [Z_to_bv 8 65])
    rw [file_envp_geo_weight_match]
    refine Rat.mul_pos ?_ ?_
    · apply envp_point_pos <;> assumption
    · apply geo_point_pos <;> assumption
  · unfold file_envp_core
    rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] []
      file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path []
        [Z_to_bv 8 65] file_other_path file_other_path_ne]

/-! ## The same coupling, for the header-conditioned family -/

/-- A core the header-conditioned weight does not zero is the whole-file
template at its own contents. -/
theorem file_prefix_geo_weight_positive_matches (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c →
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) := by
  intro Hpos
  unfold file_prefix_geo_weight at Hpos
  split at Hpos
  · next heq => exact heq
  · exact absurd Hpos Rat.lt_irrefl

/-- One step further: such a core is the shifted template at some payload. -/
theorem file_prefix_geo_weight_positive_extends (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c →
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t := by
  intro Hpos
  have Heq := file_prefix_geo_weight_positive_matches hdr p argv envp fs0 pth s c Hpos
  cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
  | none =>
    exfalso
    rw [file_prefix_geo_weight_off_header hdr p argv envp fs0 pth s c hs] at Hpos
    exact Rat.lt_irrefl Hpos
  | some t =>
    refine ⟨t, ?_⟩
    unfold file_prefix_core
    rw [← strip_prefix_Some hdr (fs_file pth c.core_fs) t hs]
    exact Heq

/-- The collapse for the header-conditioned family. -/
theorem file_prefix_geo_weight_blind_off_path (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (pth' : Fs.path) (c : FinCore) :
    pth' ≠ pth → 0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c →
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  intro Hne Hpos
  have Heq := file_prefix_geo_weight_positive_matches hdr p argv envp fs0 pth s c Hpos
  rw [Heq]
  exact fs_file_file_core_other argv envp fs0 pth s (fs_file pth c.core_fs) pth' Hne

/-- Any two cores the header-conditioned family weighs agree off the varied
path. -/
theorem file_geometric_prefix_blind_off_path (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (pth' : Fs.path) (c1 c2 : FinCore) :
    pth' ≠ pth →
    0 < cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c1 →
    0 < cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c2 →
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  intro Hne H1 H2
  replace H1 : 0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c1 := H1
  replace H2 : 0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c2 := H2
  rw [file_prefix_geo_weight_blind_off_path hdr p argv envp fs0 pth s pth' c1 Hne H1,
    file_prefix_geo_weight_blind_off_path hdr p argv envp fs0 pth s pth' c2 Hne H2]

/-- The misconfigured instance for the header-conditioned family, behind the
one-byte example header: two weighted cores whose payloads differ, agreeing at
the path argv names. -/
theorem file_geometric_prefix_needs_argv_to_name_the_path (p : Rat) (Hp0 : 0 ≤ p)
    (Hp1 : p ≤ 1) :
    0 < p → p < 1 →
    ¬ argv_names_path file_misconfigured_argv file_example_path
    ∧ 0 < cd_weight (file_geometric_prefix file_example_hdr p file_misconfigured_argv []
        [] file_example_path [] Hp0 Hp1)
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [])
    ∧ 0 < cd_weight (file_geometric_prefix file_example_hdr p file_misconfigured_argv []
        [] file_example_path [] Hp0 Hp1)
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [Z_to_bv 8 65])
    ∧ fs_file file_other_path
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] []).core_fs
      = fs_file file_other_path
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [Z_to_bv 8 65]).core_fs := by
  intro Hpos Hlt
  refine ⟨(file_geometric_needs_argv_to_name_the_path p Hp0 Hp1 Hpos Hlt).1, ?_, ?_, ?_⟩
  · show 0 < file_prefix_geo_weight file_example_hdr p file_misconfigured_argv [] []
      file_example_path []
      (file_prefix_core file_example_hdr file_misconfigured_argv [] []
        file_example_path [] [])
    rw [file_prefix_geo_weight_match]
    apply geo_point_pos <;> assumption
  · show 0 < file_prefix_geo_weight file_example_hdr p file_misconfigured_argv [] []
      file_example_path []
      (file_prefix_core file_example_hdr file_misconfigured_argv [] []
        file_example_path [] [Z_to_bv 8 65])
    rw [file_prefix_geo_weight_match]
    apply geo_point_pos <;> assumption
  · unfold file_prefix_core
    rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path []
      (file_example_hdr ++ []) file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path []
        (file_example_hdr ++ [Z_to_bv 8 65]) file_other_path file_other_path_ne]

/-! ## The same coupling, for the alphabet-restricted family -/

/-- A core the alphabet-restricted weight does not zero is the whole-file
template at its own contents. -/
theorem file_prefix_over_geo_weight_positive_matches (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c →
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) := by
  intro Hpos
  unfold file_prefix_over_geo_weight at Hpos
  split at Hpos
  · next heq => exact heq
  · exact absurd Hpos Rat.lt_irrefl

/-- One step further: such a core is the shifted template at a payload over the
alphabet. -/
theorem file_prefix_over_geo_weight_positive_extends (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c →
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ alpha_only alpha t = true := by
  intro Hpos
  have Heq := file_prefix_over_geo_weight_positive_matches alpha hdr p argv envp fs0 pth s c Hpos
  cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
  | none =>
    exfalso
    rw [file_prefix_over_geo_weight_off_header alpha hdr p argv envp fs0 pth s c hs] at Hpos
    exact Rat.lt_irrefl Hpos
  | some t =>
    have hc : c = file_prefix_core hdr argv envp fs0 pth s t := by
      unfold file_prefix_core
      rw [← strip_prefix_Some hdr (fs_file pth c.core_fs) t hs]
      exact Heq
    cases ha : alpha_only alpha t with
    | false =>
      exfalso
      rw [hc, file_prefix_over_geo_weight_off_alphabet alpha hdr p argv envp fs0 pth s t ha]
        at Hpos
      exact Rat.lt_irrefl Hpos
    | true => exact ⟨t, hc, ha⟩

/-- The collapse for the alphabet-restricted family. -/
theorem file_prefix_over_geo_weight_blind_off_path (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (pth' : Fs.path) (c : FinCore) :
    pth' ≠ pth → 0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c →
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  intro Hne Hpos
  have Heq := file_prefix_over_geo_weight_positive_matches alpha hdr p argv envp fs0 pth s c Hpos
  rw [Heq]
  exact fs_file_file_core_other argv envp fs0 pth s (fs_file pth c.core_fs) pth' Hne

/-- Any two cores the alphabet-restricted family weighs agree off the varied
path. -/
theorem file_geometric_prefix_over_blind_off_path (alpha : List byte) (Hnd : alpha.Nodup)
    (Hne : alpha ≠ []) (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (pth' : Fs.path) (c1 c2 : FinCore) :
    pth' ≠ pth →
    0 < cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1) c1 →
    0 < cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1) c2 →
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  intro Hne' H1 H2
  replace H1 : 0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c1 := H1
  replace H2 : 0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c2 := H2
  rw [file_prefix_over_geo_weight_blind_off_path alpha hdr p argv envp fs0 pth s pth' c1
      Hne' H1,
    file_prefix_over_geo_weight_blind_off_path alpha hdr p argv envp fs0 pth s pth' c2
      Hne' H2]

/-- The misconfigured instance for the alphabet-restricted family, over the
one-byte example alphabet: the payloads are the empty one and the alphabet's own
byte. -/
theorem file_geometric_prefix_over_needs_argv_to_name_the_path (p : Rat) (Hp0 : 0 ≤ p)
    (Hp1 : p ≤ 1) :
    0 < p → p < 1 →
    ¬ argv_names_path file_misconfigured_argv file_example_path
    ∧ 0 < cd_weight (file_geometric_prefix_over file_example_alpha
        file_example_alpha_nodup file_example_alpha_ne file_example_hdr p
        file_misconfigured_argv [] [] file_example_path [] Hp0 Hp1)
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [])
    ∧ 0 < cd_weight (file_geometric_prefix_over file_example_alpha
        file_example_alpha_nodup file_example_alpha_ne file_example_hdr p
        file_misconfigured_argv [] [] file_example_path [] Hp0 Hp1)
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [Z_to_bv 8 65])
    ∧ fs_file file_other_path
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] []).core_fs
      = fs_file file_other_path
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [Z_to_bv 8 65]).core_fs := by
  intro Hpos Hlt
  refine ⟨(file_geometric_needs_argv_to_name_the_path p Hp0 Hp1 Hpos Hlt).1, ?_, ?_, ?_⟩
  · show 0 < file_prefix_over_geo_weight file_example_alpha file_example_hdr p
      file_misconfigured_argv [] [] file_example_path []
      (file_prefix_core file_example_hdr file_misconfigured_argv [] []
        file_example_path [] [])
    rw [file_prefix_over_geo_weight_match file_example_alpha file_example_hdr p
      file_misconfigured_argv [] [] file_example_path [] [] (by decide)]
    apply alpha_geo_point_pos
    · exact Hpos
    · exact Hlt
    · exact file_example_alpha_ne
  · show 0 < file_prefix_over_geo_weight file_example_alpha file_example_hdr p
      file_misconfigured_argv [] [] file_example_path []
      (file_prefix_core file_example_hdr file_misconfigured_argv [] []
        file_example_path [] [Z_to_bv 8 65])
    rw [file_prefix_over_geo_weight_match file_example_alpha file_example_hdr p
      file_misconfigured_argv [] [] file_example_path [] [Z_to_bv 8 65] (by decide)]
    apply alpha_geo_point_pos
    · exact Hpos
    · exact Hlt
    · exact file_example_alpha_ne
  · unfold file_prefix_core
    rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path []
      (file_example_hdr ++ []) file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path []
        (file_example_hdr ++ [Z_to_bv 8 65]) file_other_path file_other_path_ne]

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
