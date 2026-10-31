-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdinVarying
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Calibrated
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFile
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileHeader
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileHeaderAlphabet
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileVarying

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-!

# EquivalenceDefinition.MeasureLib.FullSupport — the full-support base family

This file holds `theories/EquivalenceDefinition/MeasureLib.v` lines 13130 to
15335, the combinator whose law puts every core in its support.  Four
independent factors, one per field of `FinInput.FinCore`, each strictly
positive at every value of its coordinate when its eight rates are strictly
inside `(0, 1)`: argv and envp are spread by the entry-count and per-entry-byte
source `envp_point` was built for, under the field-neutral names
`strings_point` and `strings_factor`; the file system is spread by `fs_point`,
the same entry-count shell with a path factor and a contents factor per entry;
and standard input is `geo_point`.  Mass `1` is declared, and the file carries
its upper certificate (`full_support_base_mass_upper`), its marginal and
cylinder bounds, the composability bound through the weight-preserving
injection `core_strip`, the proof that the declared mass is never attained for
`ps < 1`, and the lower certificate that makes it the least upper bound.

The long arguments, and what this family does not claim — `fs_point` weighs
every list of pairs, sorted or not, so the cores it weighs are not claimed
valid — stay in the Rocq file's banners.

Rocq's `Q` is core Lean's reduced `Rat`, so each lemma Rocq states over `Qeq`
is stated here over `=`, as `Measure.lean` does.  Rocq's `ring` steps are
`grind`, which normalizes `Rat` ring identities on the pinned toolchain; the
nonlinear order steps are core `Rat` lemmas.  `fsb_mul_le_mul` is private and
is the one helper this file adds: it is `QArith`'s `Qmult_le_compat_nonneg`,
which core Lean's `Rat` does not ship, and Rocq takes it from the standard
library rather than declaring it in `MeasureLib.v`. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## The argv law and the envp law are one source -/

/-- The argv coordinate's running product: `envp_factor` under a
field-neutral name, so that a statement about argv does not read as a
statement about the environment. -/
def strings_factor : Rat → Rat → List (List byte) → Rat := envp_factor

/-- The argv coordinate's law: `envp_point` under a field-neutral name. -/
def strings_point : Rat → Rat → List (List byte) → Rat := envp_point

/-- The three-factor form of `strings_point`: the stop rate, the
continuation tail over the entry count, and the entries' product. -/
theorem strings_point_closed_form (r q : Rat) (xs : List (List byte)) :
    strings_point r q xs = r * Qpow (1 - r) xs.length * entries_geo_product q xs :=
  envp_point_closed_form r q xs

/-- `strings_point` is nonnegative at rates in the unit interval. -/
theorem strings_point_nonneg (r q : Rat) :
    0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 → ∀ xs : List (List byte), 0 ≤ strings_point r q xs :=
  envp_point_nonneg r q

/-- `strings_point` is strictly positive at rates strictly inside the
unit interval, at every list of byte strings. -/
theorem strings_point_pos (r q : Rat) (xs : List (List byte)) :
    0 < r → r < 1 → 0 < q → q < 1 → 0 < strings_point r q xs :=
  envp_point_pos r q xs

/-! ## The file-system law -/

/-- The entries' product of a file system: one byte-geometric factor
for the path and one for the contents, per entry. -/
def fs_entries_product (v w : Rat) : Fs.Fs → Rat
  | [] => 1
  | (pth, d) :: fs' =>
      geo_point v pth.length * geo_point w d.length * fs_entries_product v w fs'

/-- The file system's running product: continuing past an entry costs
`1 - u`, and the entry costs its path's weight times its contents'. -/
def fs_factor (u v w : Rat) : Fs.Fs → Rat
  | [] => 1
  | (pth, d) :: fs' =>
      (1 - u) * geo_point v pth.length * geo_point w d.length * fs_factor u v w fs'

/-- The file-system law: the weight of stopping times the running product. -/
def fs_point (u v w : Rat) (fs : Fs.Fs) : Rat := u * fs_factor u v w fs

/-- The running product in closed form: the continuation tail over the
entry count times the entries' product. -/
theorem fs_factor_closed_form (u v w : Rat) (fs : Fs.Fs) :
    fs_factor u v w fs = Qpow (1 - u) fs.length * fs_entries_product v w fs := by
  induction fs with
  | nil => simp only [fs_factor, fs_entries_product, List.length_nil, Qpow_0]; grind
  | cons e fs ih =>
    obtain ⟨pth, d⟩ := e
    simp only [fs_factor, fs_entries_product, List.length_cons, Qpow_succ, ih]
    grind

/-- The three-factor form the family is specified with: the stop rate,
the continuation tail over the entry count, and the entries' product. -/
theorem fs_point_closed_form (u v w : Rat) (fs : Fs.Fs) :
    fs_point u v w fs = u * Qpow (1 - u) fs.length * fs_entries_product v w fs := by
  simp only [fs_point, fs_factor_closed_form]; grind

/-- The running product of an appended file system is the product of
the two running products. -/
theorem fs_factor_app (u v w : Rat) (fs fs' : Fs.Fs) :
    fs_factor u v w (fs ++ fs') = fs_factor u v w fs * fs_factor u v w fs' := by
  induction fs with
  | nil => simp only [List.nil_append, fs_factor]; grind
  | cons e fs ih =>
    obtain ⟨pth, d⟩ := e
    simp only [List.cons_append, fs_factor, ih]
    grind

/-- The running product of a one-entry file system. -/
theorem fs_factor_one (u v w : Rat) (pth : Fs.path) (d : List byte) :
    fs_factor u v w [(pth, d)] = (1 - u) * geo_point v pth.length * geo_point w d.length := by
  simp only [fs_factor]; grind

/-- The running product is nonnegative: five side conditions, one per
factor the three rates contribute. -/
theorem fs_factor_nonneg (u v w : Rat) :
    u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → ∀ fs : Fs.Fs, 0 ≤ fs_factor u v w fs := by
  intro hu1 hv0 hv1 hw0 hw1 fs
  induction fs with
  | nil => exact Qle_0_1
  | cons e fs ih =>
    obtain ⟨pth, d⟩ := e
    simp only [fs_factor]
    refine Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg ?_ ?_) ?_) ih
    · grind
    · exact geo_point_nonneg v pth.length hv0 hv1
    · exact geo_point_nonneg w d.length hw0 hw1

/-- The file-system law is nonnegative at rates in the unit interval. -/
theorem fs_point_nonneg (u v w : Rat) :
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
    ∀ fs : Fs.Fs, 0 ≤ fs_point u v w fs := by
  intro hu0 hu1 hv0 hv1 hw0 hw1 fs
  exact Rat.mul_nonneg hu0 (fs_factor_nonneg u v w hu1 hv0 hv1 hw0 hw1 fs)

/-- One file system weighs at most the mass of the file systems
extending it as lists, because the stop rate is at most `1`. -/
theorem fs_point_le_factor (u v w : Rat) :
    u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
    ∀ fs : Fs.Fs, fs_point u v w fs ≤ fs_factor u v w fs := by
  intro hu1 hv0 hv1 hw0 hw1 fs
  have hF : 0 ≤ fs_factor u v w fs := fs_factor_nonneg u v w hu1 hv0 hv1 hw0 hw1 fs
  have h := Rat.mul_le_mul_of_nonneg_right hu1 hF
  simp only [fs_point]
  grind

/-- Strict positivity at every list of pairs, sorted or not: every
factor of the running product is positive. -/
theorem fs_point_pos (u v w : Rat) (fs : Fs.Fs) :
    0 < u → u < 1 → 0 < v → v < 1 → 0 < w → w < 1 → 0 < fs_point u v w fs := by
  intro hu0 hu1 hv0 hv1 hw0 hw1
  refine Rat.mul_pos hu0 ?_
  induction fs with
  | nil => exact (by decide +kernel : (0 : Rat) < 1)
  | cons e fs ih =>
    obtain ⟨pth, d⟩ := e
    simp only [fs_factor]
    refine Rat.mul_pos (Rat.mul_pos (Rat.mul_pos ?_ ?_) ?_) ih
    · grind
    · exact geo_point_pos v pth.length hv0 hv1
    · exact geo_point_pos w d.length hw0 hw1

/-! ## The weight, and the distribution -/

/-- The weight: the product of the four coordinates' laws.  There is no
template to match and no decision to make, because every core is in the
support. -/
def base_weight (ra qa re qe u v w ps : Rat) (c : FinCore) : Rat :=
  strings_point ra qa c.core_argv * strings_point re qe c.core_envp
    * fs_point u v w c.core_fs * geo_point ps c.core_stdin.length

/-- The rewrite rule on a constructed core; it holds by computation. -/
theorem base_weight_mk (ra qa re qe u v w ps : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (s : List byte) :
    base_weight ra qa re qe u v w ps (FinCore.mkFinCore argv envp fs s)
      = strings_point ra qa argv * strings_point re qe envp
        * fs_point u v w fs * geo_point ps s.length := rfl

/-- The family's formula with all eight rates visible, so that a reader
can check the definition against the shape the law is usually written in. -/
theorem base_weight_closed_form (ra qa re qe u v w ps : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (s : List byte) :
    base_weight ra qa re qe u v w ps (FinCore.mkFinCore argv envp fs s)
      = (ra * Qpow (1 - ra) argv.length * entries_geo_product qa argv)
        * (re * Qpow (1 - re) envp.length * entries_geo_product qe envp)
        * (u * Qpow (1 - u) fs.length * fs_entries_product v w fs)
        * (ps * Qpow (1 - ps) s.length * Qpow (1 / 256) s.length) := by
  rw [base_weight_mk, strings_point_closed_form, strings_point_closed_form,
    fs_point_closed_form, geo_point_closed_form]

/-- The weight is nonnegative at the sixteen rate bounds. -/
theorem base_weight_nonneg (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ c : FinCore, 0 ≤ base_weight ra qa re qe u v w ps c := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 c
  refine Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg ?_ ?_) ?_) ?_
  · exact strings_point_nonneg ra qa hra0 hra1 hqa0 hqa1 c.core_argv
  · exact strings_point_nonneg re qe hre0 hre1 hqe0 hqe1 c.core_envp
  · exact fs_point_nonneg u v w hu0 hu1 hv0 hv1 hw0 hw1 c.core_fs
  · exact geo_point_nonneg ps c.core_stdin.length hps0 hps1

/-- The distribution.  Mass `1` is declared, and the sixteen rate bounds
are constructor arguments.  None of the eight strict inequalities is
demanded here: the two lemmas that need them ask for them themselves, so
a rate at `0` or at `1` still builds a member. -/
def full_support_base (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) : CoreDistribution :=
  CoreDistribution.mkCoreDistribution (base_weight ra qa re qe u v w ps) 1
    (base_weight_nonneg ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
      Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)

/-- The declared mass is nonnegative. -/
theorem full_support_base_mass_nonneg (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) :
    0 ≤ cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) := by
  show (0 : Rat) ≤ 1
  decide +kernel

/-! ## Full support: every core weighs something -/

/-- The full-support lemma.  At eight rates strictly inside `(0, 1)`
every core weighs strictly more than zero, so no fire set sits in a null
set and no `Measure.weight_bound_T` claim about this family is vacuous. -/
theorem full_support_base_positive (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) :
    0 < ra → ra < 1 → 0 < qa → qa < 1 → 0 < re → re < 1 → 0 < qe → qe < 1 →
    0 < u → u < 1 → 0 < v → v < 1 → 0 < w → w < 1 → 0 < ps → ps < 1 →
    ∀ c : FinCore,
      0 < cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) c := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 c
  show 0 < base_weight ra qa re qe u v w ps c
  refine Rat.mul_pos (Rat.mul_pos (Rat.mul_pos ?_ ?_) ?_) ?_
  · exact strings_point_pos ra qa c.core_argv hra0 hra1 hqa0 hqa1
  · exact strings_point_pos re qe c.core_envp hre0 hre1 hqe0 hqe1
  · exact fs_point_pos u v w c.core_fs hu0 hu1 hv0 hv1 hw0 hw1
  · exact geo_point_pos ps c.core_stdin.length hps0 hps1

/-- The same fact on records, which is the form the measure layer reads
a weight in: every record weighs something. -/
theorem full_support_base_lift_positive (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) :
    0 < ra → ra < 1 → 0 < qa → qa < 1 → 0 < re → re < 1 → 0 < qe → qe < 1 →
    0 < u → u < 1 → 0 < v → v < 1 → 0 < w → w < 1 → 0 < ps → ps < 1 →
    ∀ f : FinProcInput,
      0 < cd_lift (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) f := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 f
  exact full_support_base_positive ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 (fin_core f)

/-- A core off every fixed template: one byte in each of its four
fields. -/
def full_support_example_core : FinCore :=
  FinCore.mkFinCore [[Z_to_bv 8 65]] [[Z_to_bv 8 65]] [([Z_to_bv 8 65], [Z_to_bv 8 65])]
    [Z_to_bv 8 65]

/-- The bite, against every sibling family at once: the example core
weighs zero under each template family over the empty environment, and
strictly more than zero here. -/
theorem full_support_base_bites (p r q : Rat) :
    geo_weight p [] [] [] full_support_example_core = 0
    ∧ envp_geo_weight p r q [] [] full_support_example_core = 0
    ∧ file_geo_weight p [] [] [] [Z_to_bv 8 65] [] full_support_example_core = 0
    ∧ file_envp_geo_weight p r q [] [] [Z_to_bv 8 65] [] full_support_example_core = 0
    ∧ file_prefix_geo_weight [] p [] [] [] [Z_to_bv 8 65] [] full_support_example_core = 0
    ∧ file_prefix_over_geo_weight [Z_to_bv 8 65] [] p [] [] [] [Z_to_bv 8 65] []
        full_support_example_core = 0
    ∧ 0 < base_weight (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2)
        full_support_example_core := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine geo_weight_mismatch p [] [] [] full_support_example_core ?_
    intro heq
    have h := congrArg FinCore.core_argv heq
    simp [full_support_example_core] at h
  · refine envp_geo_weight_mismatch p r q [] [] full_support_example_core ?_
    intro heq
    have h := congrArg FinCore.core_argv heq
    simp [full_support_example_core] at h
  · refine file_geo_weight_mismatch p [] [] [] [Z_to_bv 8 65] [] full_support_example_core ?_
    intro heq
    have h := congrArg FinCore.core_argv heq
    simp [full_support_example_core, file_core] at h
  · refine file_envp_geo_weight_mismatch p r q [] [] [Z_to_bv 8 65] []
      full_support_example_core ?_
    intro heq
    have h := congrArg FinCore.core_argv heq
    simp [full_support_example_core, file_envp_core, file_core] at h
  · refine file_prefix_geo_weight_mismatch [] p [] [] [] [Z_to_bv 8 65] []
      full_support_example_core ?_
    intro heq
    have h := congrArg FinCore.core_argv heq
    simp [full_support_example_core, file_core] at h
  · refine file_prefix_over_geo_weight_mismatch [Z_to_bv 8 65] [] p [] [] [] [Z_to_bv 8 65] []
      full_support_example_core ?_
    intro heq
    have h := congrArg FinCore.core_argv heq
    simp [full_support_example_core, file_core] at h
  · decide +kernel

/-! ## The four coordinates, recombined -/

/-- `x * z ≤ y * t` from two bounds whose smaller sides are
nonnegative.  Rocq takes this from `QArith`'s `Qmult_le_compat_nonneg`,
which core Lean's `Rat` does not ship. -/
private theorem fsb_mul_le_mul {x y z t : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z)
    (hzt : z ≤ t) : x * z ≤ y * t :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hzt hx)
    (Rat.mul_le_mul_of_nonneg_right hxy (Rat.le_trans hz hzt))

/-- Every core whose argv comes from `Av`, environment from `Ae`, file
system from `Af` and standard input from `B`.  Its sum is the product of
the four coordinates' sums, and this is the only place the four
coordinates meet. -/
def full_support_product (Av Ae : List (List (List byte))) (Af : List Fs.Fs)
    (B : List (List byte)) : List FinCore :=
  Av.flatMap (fun argv =>
    Ae.flatMap (fun envp =>
      Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs))))

/-- A core built from four members of the four enumerations is in the
product. -/
theorem In_full_support_product (Av Ae : List (List (List byte))) (Af : List Fs.Fs)
    (B : List (List byte)) (argv envp : List (List byte)) (fs : Fs.Fs) (s : List byte) :
    argv ∈ Av → envp ∈ Ae → fs ∈ Af → s ∈ B →
    FinCore.mkFinCore argv envp fs s ∈ full_support_product Av Ae Af B := by
  intro ha he hf hs
  refine List.mem_flatMap.mpr ⟨argv, ha, ?_⟩
  refine List.mem_flatMap.mpr ⟨envp, he, ?_⟩
  refine List.mem_flatMap.mpr ⟨fs, hf, ?_⟩
  exact List.mem_map.mpr ⟨s, hs, rfl⟩

/-- The innermost block: the standard inputs of one argv, environment
and file system. -/
theorem qsum_base_stdin_block (ra qa re qe u v w ps : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (B : List (List byte)) :
    qsum (base_weight ra qa re qe u v w ps) (B.map (FinCore.mkFinCore argv envp fs))
      = strings_point ra qa argv * strings_point re qe envp * fs_point u v w fs
        * qsum (fun s => geo_point ps s.length) B := by
  rw [qsum_map, qsum_ext _ (fun s => strings_point ra qa argv * strings_point re qe envp
      * fs_point u v w fs * geo_point ps s.length) B
      (fun s _ => base_weight_mk ra qa re qe u v w ps argv envp fs s), qsum_scale]

/-- One layer out: the file systems of one argv and environment. -/
theorem qsum_base_fs_block (ra qa re qe u v w ps : Rat) (argv envp : List (List byte))
    (Af : List Fs.Fs) (B : List (List byte)) :
    qsum (base_weight ra qa re qe u v w ps)
        (Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs)))
      = strings_point ra qa argv * strings_point re qe envp
        * qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by
  rw [qsum_flat_map, qsum_ext _ (fun fs => (strings_point ra qa argv * strings_point re qe envp
      * qsum (fun s => geo_point ps s.length) B) * fs_point u v w fs) Af
      (fun fs _ => by rw [qsum_base_stdin_block]; grind), qsum_scale]
  grind

/-- Two layers out: the environments of one argv. -/
theorem qsum_base_envp_block (ra qa re qe u v w ps : Rat) (argv : List (List byte))
    (Ae : List (List (List byte))) (Af : List Fs.Fs) (B : List (List byte)) :
    qsum (base_weight ra qa re qe u v w ps)
        (Ae.flatMap (fun envp => Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs))))
      = strings_point ra qa argv * qsum (strings_point re qe) Ae
        * qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by
  rw [qsum_flat_map, qsum_ext _ (fun envp => (strings_point ra qa argv
      * qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B)
      * strings_point re qe envp) Ae
      (fun envp _ => by rw [qsum_base_fs_block]; grind), qsum_scale]
  grind

/-- The product's sum is the product of the four coordinates' sums. -/
theorem qsum_full_support_product (ra qa re qe u v w ps : Rat)
    (Av Ae : List (List (List byte))) (Af : List Fs.Fs) (B : List (List byte)) :
    qsum (base_weight ra qa re qe u v w ps) (full_support_product Av Ae Af B)
      = qsum (strings_point ra qa) Av * qsum (strings_point re qe) Ae
        * qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by
  rw [full_support_product, qsum_flat_map,
    qsum_ext _ (fun argv => (qsum (strings_point re qe) Ae * qsum (fs_point u v w) Af
      * qsum (fun s => geo_point ps s.length) B) * strings_point ra qa argv) Av
      (fun argv _ => by rw [qsum_base_envp_block]; grind), qsum_scale]
  grind

/-- The product of four duplicate-free enumerations repeats nothing: a
core determines each of its four fields.  Only the lower certificate
needs this. -/
theorem NoDup_full_support_product (Av Ae : List (List (List byte))) (Af : List Fs.Fs)
    (B : List (List byte)) :
    Av.Nodup → Ae.Nodup → Af.Nodup → B.Nodup →
    (full_support_product Av Ae Af B).Nodup := by
  intro hA hE hF hB
  refine NoDup_flat_map _ Av hA ?_ ?_
  · intro argv _
    refine NoDup_flat_map _ Ae hE ?_ ?_
    · intro envp _
      refine NoDup_flat_map _ Af hF ?_ ?_
      · intro fs _
        refine NoDup_map_inj _ B ?_ hB
        intro x y _ _ heq
        exact congrArg FinCore.core_stdin heq
      · intro fs1 fs2 c _ _ h1 h2
        obtain ⟨s1, _, hs1⟩ := List.mem_map.mp h1
        obtain ⟨s2, _, hs2⟩ := List.mem_map.mp h2
        exact congrArg FinCore.core_fs (hs1.trans hs2.symm)
    · intro envp1 envp2 c _ _ h1 h2
      obtain ⟨fs1, _, h1⟩ := List.mem_flatMap.mp h1
      obtain ⟨s1, _, hs1⟩ := List.mem_map.mp h1
      obtain ⟨fs2, _, h2⟩ := List.mem_flatMap.mp h2
      obtain ⟨s2, _, hs2⟩ := List.mem_map.mp h2
      exact congrArg FinCore.core_envp (hs1.trans hs2.symm)
  · intro argv1 argv2 c _ _ h1 h2
    obtain ⟨envp1, _, h1⟩ := List.mem_flatMap.mp h1
    obtain ⟨fs1, _, h1⟩ := List.mem_flatMap.mp h1
    obtain ⟨s1, _, hs1⟩ := List.mem_map.mp h1
    obtain ⟨envp2, _, h2⟩ := List.mem_flatMap.mp h2
    obtain ⟨fs2, _, h2⟩ := List.mem_flatMap.mp h2
    obtain ⟨s2, _, hs2⟩ := List.mem_map.mp h2
    exact congrArg FinCore.core_argv (hs1.trans hs2.symm)

/-- The engine every bound below runs on: a duplicate-free list of cores
each of whose four fields lies in a given enumeration weighs at most the
product of four numbers bounding the four enumerations' sums. -/
theorem base_weight_product_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (Av Ae : List (List (List byte))) (Af : List Fs.Fs) (B : List (List byte))
      (SA SE SF SB : Rat) (cs : List FinCore),
      qsum (strings_point ra qa) Av ≤ SA →
      qsum (strings_point re qe) Ae ≤ SE →
      qsum (fs_point u v w) Af ≤ SF →
      qsum (fun s => geo_point ps s.length) B ≤ SB →
      cs.Nodup →
      (∀ c, c ∈ cs → c.core_argv ∈ Av ∧ c.core_envp ∈ Ae ∧ c.core_fs ∈ Af
        ∧ c.core_stdin ∈ B) →
      qsum (base_weight ra qa re qe u v w ps) cs ≤ SA * SE * SF * SB := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1
    Av Ae Af B SA SE SF SB cs hA hE hF hB hnd hall
  have hA0 : 0 ≤ qsum (strings_point ra qa) Av :=
    qsum_nonneg _ Av (fun x _ => strings_point_nonneg ra qa hra0 hra1 hqa0 hqa1 x)
  have hE0 : 0 ≤ qsum (strings_point re qe) Ae :=
    qsum_nonneg _ Ae (fun x _ => strings_point_nonneg re qe hre0 hre1 hqe0 hqe1 x)
  have hF0 : 0 ≤ qsum (fs_point u v w) Af :=
    qsum_nonneg _ Af (fun x _ => fs_point_nonneg u v w hu0 hu1 hv0 hv1 hw0 hw1 x)
  have hB0 : 0 ≤ qsum (fun s => geo_point ps s.length) B :=
    qsum_nonneg _ B (fun x _ => geo_point_nonneg ps x.length hps0 hps1)
  refine Rat.le_trans (qsum_core_incl_le (base_weight ra qa re qe u v w ps) cs
    (full_support_product Av Ae Af B)
    (base_weight_nonneg ra qa re qe u v w ps hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1
      hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1) hnd ?_) ?_
  · intro c hc
    obtain ⟨ha, he, hf, hs⟩ := hall c hc
    obtain ⟨argv, envp, fs, s⟩ := c
    exact In_full_support_product Av Ae Af B argv envp fs s ha he hf hs
  · rw [qsum_full_support_product]
    exact fsb_mul_le_mul
      (Rat.mul_nonneg (Rat.mul_nonneg hA0 hE0) hF0)
      (fsb_mul_le_mul (Rat.mul_nonneg hA0 hE0) (fsb_mul_le_mul hA0 hA hE0 hE) hF0 hF)
      hB0 hB

/-! ## The file-system enumeration, and its cancellation -/

/-- Every file system extending `fs0` as a list by at most `M` further
entries, each with a path shorter than `Lp` and contents shorter than
`Lc`.  Duplicate-freedom is neither proved nor needed for the bounds. -/
def fs_enum : Fs.Fs → Nat → Nat → Nat → List Fs.Fs
  | fs0, 0, _, _ => [fs0]
  | fs0, M' + 1, Lp, Lc =>
      fs0 :: (short_inputs Lp).flatMap (fun pth =>
        (short_inputs Lc).flatMap (fun d => fs_enum (fs0 ++ [(pth, d)]) M' Lp Lc))

/-- The enumeration contains every extension within its three depths. -/
theorem fs_enum_complete (M Lp Lc : Nat) (fs0 rest : Fs.Fs) :
    rest.length ≤ M → (∀ e ∈ rest, e.1.length < Lp ∧ e.2.length < Lc) →
    (fs0 ++ rest) ∈ fs_enum fs0 M Lp Lc := by
  induction M generalizing fs0 rest with
  | zero =>
    intro hlen _
    cases rest with
    | nil => simp [fs_enum]
    | cons e r => simp at hlen
  | succ M ih =>
    intro hlen hent
    cases rest with
    | nil => simp [fs_enum]
    | cons e r =>
      obtain ⟨pth, d⟩ := e
      obtain ⟨hp, hd⟩ := hent (pth, d) (List.mem_cons_self ..)
      simp only [fs_enum]
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_flatMap.mpr ⟨pth, short_inputs_complete Lp pth hp, ?_⟩
      refine List.mem_flatMap.mpr ⟨d, short_inputs_complete Lc d hd, ?_⟩
      have heq : fs0 ++ (pth, d) :: r = (fs0 ++ [(pth, d)]) ++ r := by simp
      rw [heq]
      refine ih (fs0 ++ [(pth, d)]) r ?_ ?_
      · simp only [List.length_cons] at hlen; omega
      · intro x hx; exact hent x (List.mem_cons_of_mem _ hx)

/-- One step of the file-system cancellation: the file systems one entry
deeper than `fs0` carry the running product of `fs0` times `1 - u` times
what the path enumeration weighs times what the contents enumeration
weighs. -/
theorem qsum_fs_factor_step (u v w : Rat) (fs0 : Fs.Fs) (Lp Lc : Nat) :
    qsum (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)])) (short_inputs Lc))
        (short_inputs Lp)
      = fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc) := by
  have inner : ∀ pth : Fs.path, pth ∈ short_inputs Lp →
      qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)])) (short_inputs Lc)
        = fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - w) Lc) * geo_point v pth.length := by
    intro pth _
    have hext : ∀ d : List byte, d ∈ short_inputs Lc →
        fs_factor u v w (fs0 ++ [(pth, d)])
          = fs_factor u v w fs0 * (1 - u) * geo_point v pth.length * geo_point w d.length := by
      intro d _
      rw [fs_factor_app, fs_factor_one]
      grind
    rw [qsum_ext _ _ _ hext, qsum_scale, short_inputs_sum, geo_prefix_sum_closed]
    grind
  rw [qsum_ext _ _ _ inner, qsum_scale, short_inputs_sum, geo_prefix_sum_closed]
  grind

/-- A rate in the unit interval leaves a continuation factor in it. -/
theorem one_minus_unit (q : Rat) : 0 ≤ q → q ≤ 1 → 0 ≤ 1 - q ∧ 1 - q ≤ 1 := by
  intro h0 h1
  exact ⟨by grind, by grind⟩

/-- The geometric tail of a rate in the unit interval is in it. -/
theorem geo_tail_unit (q : Rat) (L : Nat) :
    0 ≤ q → q ≤ 1 → 0 ≤ Qpow (1 - q) L ∧ Qpow (1 - q) L ≤ 1 := by
  intro h0 h1
  obtain ⟨hm0, hm1⟩ := one_minus_unit q h0 h1
  exact ⟨Qpow_nonneg _ L hm0, Qpow_le_1 _ L hm0 hm1⟩

/-- The head of that geometric tail is in the unit interval too. -/
theorem geo_head_unit (q : Rat) (L : Nat) :
    0 ≤ q → q ≤ 1 → 0 ≤ 1 - Qpow (1 - q) L ∧ 1 - Qpow (1 - q) L ≤ 1 := by
  intro h0 h1
  obtain ⟨hg0, hg1⟩ := geo_tail_unit q L h0 h1
  exact one_minus_unit _ hg0 hg1

/-- The cancellation on the file-system coordinate: the whole
enumeration weighs no more than the mass of the file systems extending
`fs0`. -/
theorem fs_enum_sum_le (u v w : Rat) :
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
    ∀ (M Lp Lc : Nat) (fs0 : Fs.Fs),
      qsum (fs_point u v w) (fs_enum fs0 M Lp Lc) ≤ fs_factor u v w fs0 := by
  intro hu0 hu1 hv0 hv1 hw0 hw1 M Lp Lc
  induction M with
  | zero =>
    intro fs0
    have h := fs_point_le_factor u v w hu1 hv0 hv1 hw0 hw1 fs0
    simp only [fs_enum, qsum_cons, qsum_nil]
    grind
  | succ M ih =>
    intro fs0
    have hF : 0 ≤ fs_factor u v w fs0 := fs_factor_nonneg u v w hu1 hv0 hv1 hw0 hw1 fs0
    have hFu : 0 ≤ fs_factor u v w fs0 * (1 - u) := by
      refine Rat.mul_nonneg hF ?_
      grind
    obtain ⟨hGv0, hGv1⟩ := geo_head_unit v Lp hv0 hv1
    obtain ⟨hGw0, hGw1⟩ := geo_head_unit w Lc hw0 hw1
    have hflat : qsum (fs_point u v w) ((short_inputs Lp).flatMap (fun pth =>
        (short_inputs Lc).flatMap (fun d => fs_enum (fs0 ++ [(pth, d)]) M Lp Lc)))
        ≤ qsum (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
            (short_inputs Lc)) (short_inputs Lp) := by
      refine qsum_flat_map_le _ _ _ _ (fun pth _ => ?_)
      exact qsum_flat_map_le _ _ _ _ (fun d _ => ih (fs0 ++ [(pth, d)]))
    rw [qsum_fs_factor_step] at hflat
    have hstep1 : fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - v) Lp)
        ≤ fs_factor u v w fs0 * (1 - u) * 1 :=
      fsb_mul_le_mul hFu Rat.le_refl hGv0 hGv1
    have hstep2 : fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - v) Lp)
        * (1 - Qpow (1 - w) Lc) ≤ fs_factor u v w fs0 * (1 - u) * 1 * 1 :=
      fsb_mul_le_mul (Rat.mul_nonneg hFu hGv0) hstep1 hGw0 hGw1
    simp only [fs_enum, qsum_cons, fs_point]
    grind

/-! ## The depths, read off the task's own list -/

/-- The longest argv of the list. -/
def cores_argv_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => c.core_argv.length))

/-- One past the longest argv entry of the list; the enumerations
enumerate strictly shorter entries. -/
def cores_argv_entry_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => list_max (c.core_argv.map (fun e => e.length)))) + 1

/-- The longest file system of the list. -/
def cores_fs_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => c.core_fs.length))

/-- One past the longest file-system path of the list. -/
def cores_fs_path_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => list_max (c.core_fs.map (fun e => e.1.length)))) + 1

/-- One past the longest file-system contents of the list. -/
def cores_fs_contents_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => list_max (c.core_fs.map (fun e => e.2.length)))) + 1

/-- Every argv of the list is within the argv-count depth. -/
theorem cores_argv_depth_ge (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_argv.length ≤ cores_argv_depth cs := by
  intro hc
  exact list_max_ge _ _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- Every file system of the list is within the entry-count depth. -/
theorem cores_fs_depth_ge (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_fs.length ≤ cores_fs_depth cs := by
  intro hc
  exact list_max_ge _ _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- The three "strictly shorter than" depths share one proof: an entry
is under its core's inner maximum, and that is under the outer one. -/
theorem cores_inner_max_gt (A : Type) (proj : FinCore → List A) (len : A → Nat)
    (cs : List FinCore) (c : FinCore) (e : A) :
    c ∈ cs → e ∈ proj c →
    len e < list_max (cs.map (fun c0 => list_max ((proj c0).map len))) + 1 := by
  intro hc he
  have hinner : len e ≤ list_max ((proj c).map len) :=
    list_max_ge _ _ (List.mem_map.mpr ⟨e, he, rfl⟩)
  have houter : list_max ((proj c).map len)
      ≤ list_max (cs.map (fun c0 => list_max ((proj c0).map len))) :=
    list_max_ge _ _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  omega

/-- Every argv entry of the list is strictly shorter than the argv entry
depth. -/
theorem cores_argv_entry_depth_gt (cs : List FinCore) (c : FinCore) (e : List byte) :
    c ∈ cs → e ∈ c.core_argv → e.length < cores_argv_entry_depth cs :=
  fun hc he => cores_inner_max_gt (List byte) FinCore.core_argv (fun e => e.length) cs c e hc he

/-- Every file-system path of the list is strictly shorter than the path
depth. -/
theorem cores_fs_path_depth_gt (cs : List FinCore) (c : FinCore) (e : Fs.path × List byte) :
    c ∈ cs → e ∈ c.core_fs → e.1.length < cores_fs_path_depth cs :=
  fun hc he => cores_inner_max_gt (Fs.path × List byte) FinCore.core_fs (fun e => e.1.length)
    cs c e hc he

/-- Every file-system contents of the list is strictly shorter than the
contents depth. -/
theorem cores_fs_contents_depth_gt (cs : List FinCore) (c : FinCore)
    (e : Fs.path × List byte) :
    c ∈ cs → e ∈ c.core_fs → e.2.length < cores_fs_contents_depth cs :=
  fun hc he => cores_inner_max_gt (Fs.path × List byte) FinCore.core_fs (fun e => e.2.length)
    cs c e hc he

/-- The argv enumeration at the depths the list dictates. -/
def argv_free (cs : List FinCore) : List (List (List byte)) :=
  envp_enum [] (cores_argv_depth cs) (cores_argv_entry_depth cs)

/-- The environment enumeration at the depths the list dictates. -/
def envp_free (cs : List FinCore) : List (List (List byte)) :=
  envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)

/-- The file-system enumeration at the depths the list dictates. -/
def fs_free (cs : List FinCore) : List Fs.Fs :=
  fs_enum [] (cores_fs_depth cs) (cores_fs_path_depth cs) (cores_fs_contents_depth cs)

/-- The standard-input enumeration at the depth the list dictates. -/
def stdin_free (cs : List FinCore) : List (List byte) :=
  bytes_cyl [] (cores_stdin_depth cs)

/-- The argv enumeration contains every argv of the list. -/
theorem argv_free_In (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_argv ∈ argv_free cs := by
  intro hc
  have h := envp_enum_complete (cores_argv_depth cs) (cores_argv_entry_depth cs) []
    c.core_argv (cores_argv_depth_ge cs c hc)
    (fun e he => cores_argv_entry_depth_gt cs c e hc he)
  simpa [argv_free] using h

/-- The environment enumeration contains every environment of the list. -/
theorem envp_free_In (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_envp ∈ envp_free cs := by
  intro hc
  have h := envp_enum_complete (cores_envp_depth cs) (cores_entry_depth cs) []
    c.core_envp (cores_envp_depth_ge cs c hc)
    (fun e he => cores_entry_depth_gt cs c e hc he)
  simpa [envp_free] using h

/-- The file-system enumeration contains every file system of the list. -/
theorem fs_free_In (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_fs ∈ fs_free cs := by
  intro hc
  have h := fs_enum_complete (cores_fs_depth cs) (cores_fs_path_depth cs)
    (cores_fs_contents_depth cs) [] c.core_fs (cores_fs_depth_ge cs c hc)
    (fun e he => ⟨cores_fs_path_depth_gt cs c e hc he, cores_fs_contents_depth_gt cs c e hc he⟩)
  simpa [fs_free] using h

/-- The standard-input enumeration contains every standard input of the
list. -/
theorem stdin_free_In (cs : List FinCore) (c : FinCore) :
    c ∈ cs → c.core_stdin ∈ stdin_free cs := by
  intro hc
  have h := bytes_cyl_In (cores_stdin_depth cs) [] c.core_stdin (cores_stdin_depth_ge cs c hc)
  simpa [stdin_free] using h

/-- The argv enumeration weighs at most `1`. -/
theorem argv_free_sum_le (r q : Rat) :
    0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ cs : List FinCore, qsum (strings_point r q) (argv_free cs) ≤ 1 := by
  intro hr0 hr1 hq0 hq1 cs
  have h := envp_enum_sum_le r q hr0 hr1 hq0 hq1 (cores_argv_depth cs)
    (cores_argv_entry_depth cs) []
  have h1 : envp_factor r q ([] : List (List byte)) = 1 := rfl
  rw [h1] at h
  exact h

/-- The environment enumeration weighs at most `1`. -/
theorem envp_free_sum_le (r q : Rat) :
    0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ cs : List FinCore, qsum (strings_point r q) (envp_free cs) ≤ 1 := by
  intro hr0 hr1 hq0 hq1 cs
  have h := envp_enum_sum_le r q hr0 hr1 hq0 hq1 (cores_envp_depth cs)
    (cores_entry_depth cs) []
  have h1 : envp_factor r q ([] : List (List byte)) = 1 := rfl
  rw [h1] at h
  exact h

/-- The file-system enumeration weighs at most `1`. -/
theorem fs_free_sum_le (u v w : Rat) :
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
    ∀ cs : List FinCore, qsum (fs_point u v w) (fs_free cs) ≤ 1 := by
  intro hu0 hu1 hv0 hv1 hw0 hw1 cs
  have h := fs_enum_sum_le u v w hu0 hu1 hv0 hv1 hw0 hw1 (cores_fs_depth cs)
    (cores_fs_path_depth cs) (cores_fs_contents_depth cs) []
  have h1 : fs_factor u v w ([] : Fs.Fs) = 1 := rfl
  rw [h1] at h
  exact h

/-- The standard-input enumeration weighs at most `1`. -/
theorem stdin_free_sum_le (p : Rat) :
    0 ≤ p → p ≤ 1 →
    ∀ cs : List FinCore, qsum (fun s => geo_point p s.length) (stdin_free cs) ≤ 1 := by
  intro hp0 hp1 cs
  have h := bytes_cyl_sum_le p hp0 hp1 (cores_stdin_depth cs) []
  have h1 : geo_mass p ([] : List byte).length = 1 := by
    simp [geo_mass_closed_form, Qpow_0]
  rw [h1] at h
  exact h

/-! ## The cylinder bound over cores, and the whole-space certificate -/

/-- The cores the cylinder bound is about: argv extending `xs`,
environment extending `es`, file system extending `fs0` as a list, and
standard input extending `bs`. -/
def in_full_support_cylinder (xs es : List (List byte)) (fs0 : Fs.Fs) (bs : List byte)
    (c : FinCore) : Prop :=
  ∃ aext eext fext sext,
    c = FinCore.mkFinCore (xs ++ aext) (es ++ eext) (fs0 ++ fext) (bs ++ sext)

/-- The cylinder's mass: one continuation factor per coordinate. -/
def full_support_base_cylinder_mass (ra qa re qe u v w ps : Rat) (xs es : List (List byte))
    (fs0 : Fs.Fs) (bs : List byte) : Rat :=
  strings_factor ra qa xs * strings_factor re qe es * fs_factor u v w fs0
    * geo_mass ps bs.length

/-- The cylinder's mass with the eight rates visible. -/
theorem full_support_base_cylinder_mass_closed_form (ra qa re qe u v w ps : Rat)
    (xs es : List (List byte)) (fs0 : Fs.Fs) (bs : List byte) :
    full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs
      = (Qpow (1 - ra) xs.length * entries_geo_product qa xs)
        * (Qpow (1 - re) es.length * entries_geo_product qe es)
        * (Qpow (1 - u) fs0.length * fs_entries_product v w fs0)
        * (Qpow (1 - ps) bs.length * Qpow (1 / 256) bs.length) := by
  simp only [full_support_base_cylinder_mass, strings_factor, envp_factor_closed_form,
    fs_factor_closed_form, geo_mass_closed_form]

/-- The bound over cores: a duplicate-free list of cores lying in the
cylinder weighs at most the cylinder's mass.  Eight depths are read off
the list, the four enumerations at those depths contain it, and each is
bounded by its own cancellation lemma. -/
theorem base_weight_cylinder_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (xs es : List (List byte)) (fs0 : Fs.Fs) (bs : List byte) (cs : List FinCore),
      cs.Nodup →
      (∀ c, c ∈ cs → in_full_support_cylinder xs es fs0 bs c) →
      qsum (base_weight ra qa re qe u v w ps) cs
        ≤ full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1
    xs es fs0 bs cs hnd hcyl
  simp only [full_support_base_cylinder_mass, strings_factor]
  refine base_weight_product_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1 hre0 hre1
    hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1
    (envp_enum xs (cores_argv_depth cs) (cores_argv_entry_depth cs))
    (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
    (fs_enum fs0 (cores_fs_depth cs) (cores_fs_path_depth cs) (cores_fs_contents_depth cs))
    (bytes_cyl bs (cores_stdin_depth cs)) _ _ _ _ cs ?_ ?_ ?_ ?_ hnd ?_
  · exact envp_enum_sum_le ra qa hra0 hra1 hqa0 hqa1 _ _ xs
  · exact envp_enum_sum_le re qe hre0 hre1 hqe0 hqe1 _ _ es
  · exact fs_enum_sum_le u v w hu0 hu1 hv0 hv1 hw0 hw1 _ _ _ fs0
  · exact bytes_cyl_sum_le ps hps0 hps1 _ bs
  · intro c hc
    obtain ⟨aext, eext, fext, sext, heq⟩ := hcyl c hc
    have hargv := cores_argv_depth_ge cs c hc
    have henvp := cores_envp_depth_ge cs c hc
    have hfs := cores_fs_depth_ge cs c hc
    have hstdin := cores_stdin_depth_ge cs c hc
    rw [heq] at hargv henvp hfs hstdin
    simp only [List.length_append] at hargv henvp hfs hstdin
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [heq]
      refine envp_enum_complete _ _ xs aext (by omega) (fun e he => ?_)
      refine cores_argv_entry_depth_gt cs c e hc ?_
      simp only [heq]
      exact List.mem_append_right _ he
    · simp only [heq]
      refine envp_enum_complete _ _ es eext (by omega) (fun e he => ?_)
      refine cores_entry_depth_gt cs c e hc ?_
      simp only [heq]
      exact List.mem_append_right _ he
    · simp only [heq]
      refine fs_enum_complete _ _ _ fs0 fext (by omega) (fun e he => ⟨?_, ?_⟩)
      · refine cores_fs_path_depth_gt cs c e hc ?_
        simp only [heq]
        exact List.mem_append_right _ he
      · refine cores_fs_contents_depth_gt cs c e hc ?_
        simp only [heq]
        exact List.mem_append_right _ he
    · simp only [heq]
      exact bytes_cyl_In _ bs sext (by omega)

/-- Any duplicate-free list of cores at all weighs at most `1`: the
cylinder bound at the four empty prefixes, where every continuation
factor is `1`. -/
theorem base_weight_mass_le_1 (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ cs : List FinCore, cs.Nodup → qsum (base_weight ra qa re qe u v w ps) cs ≤ 1 := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 cs hnd
  have hmass : full_support_base_cylinder_mass ra qa re qe u v w ps [] [] [] [] = 1 := by
    have h1 : envp_factor ra qa ([] : List (List byte)) = 1 := rfl
    have h2 : envp_factor re qe ([] : List (List byte)) = 1 := rfl
    have h3 : fs_factor u v w ([] : Fs.Fs) = 1 := rfl
    have h4 : geo_mass ps ([] : List byte).length = 1 := by simp [geo_mass_closed_form, Qpow_0]
    simp only [full_support_base_cylinder_mass, strings_factor, h1, h2, h3, h4]
    grind
  refine Rat.le_trans (base_weight_cylinder_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1
    hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 [] [] [] [] cs hnd ?_) ?_
  · intro c _
    obtain ⟨argv, envp, fs, s⟩ := c
    exact ⟨argv, envp, fs, s, rfl⟩
  · rw [hmass]
    exact Rat.le_refl

/-- The export: a list of records with duplicate-free cores, all lying
in the cylinder, weighs at most the cylinder's mass. -/
theorem full_support_base_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs es : List (List byte)) (fs0 : Fs.Fs) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → in_full_support_cylinder xs es fs0 bs (fin_core f)) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs := by
  intro hnd hcyl
  rw [core_sum_map_fin_core]
  refine base_weight_cylinder_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs es fs0 bs _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hcyl f hf

/-- Upper certificate: every admissible list weighs at most the declared
mass `1`.  There is no "off the environment" disjunct to widen by,
because there is no environment to be off. -/
theorem full_support_base_mass_upper (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) := by
  intro hnd
  rw [core_sum_map_fin_core]
  exact base_weight_mass_le_1 ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 _ hnd

/-! ## The marginal bounds: one coordinate constrained, three charged `1` -/

/-- Cores with a fixed argv weigh at most that argv's own weight; the
other three coordinates are charged their whole declared mass. -/
theorem base_weight_argv_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (xs : List (List byte)) (cs : List FinCore),
      cs.Nodup → (∀ c, c ∈ cs → c.core_argv = xs) →
      qsum (base_weight ra qa re qe u v w ps) cs ≤ strings_point ra qa xs := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 xs cs
    hnd hall
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1
    hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 [xs] (envp_free cs) (fs_free cs)
    (stdin_free cs) (strings_point ra qa xs) 1 1 1 cs ?_ ?_ ?_ ?_ hnd ?_) ?_
  · rw [qsum_cons, qsum_nil]; grind
  · exact envp_free_sum_le re qe hre0 hre1 hqe0 hqe1 cs
  · exact fs_free_sum_le u v w hu0 hu1 hv0 hv1 hw0 hw1 cs
  · exact stdin_free_sum_le ps hps0 hps1 cs
  · exact fun c hc => ⟨List.mem_singleton.mpr (hall c hc), envp_free_In cs c hc,
      fs_free_In cs c hc, stdin_free_In cs c hc⟩
  · grind

/-- Cores with a fixed environment weigh at most that environment's own
weight. -/
theorem base_weight_envp_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (es : List (List byte)) (cs : List FinCore),
      cs.Nodup → (∀ c, c ∈ cs → c.core_envp = es) →
      qsum (base_weight ra qa re qe u v w ps) cs ≤ strings_point re qe es := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 es cs
    hnd hall
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1
    hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 (argv_free cs) [es] (fs_free cs)
    (stdin_free cs) 1 (strings_point re qe es) 1 1 cs ?_ ?_ ?_ ?_ hnd ?_) ?_
  · exact argv_free_sum_le ra qa hra0 hra1 hqa0 hqa1 cs
  · rw [qsum_cons, qsum_nil]; grind
  · exact fs_free_sum_le u v w hu0 hu1 hv0 hv1 hw0 hw1 cs
  · exact stdin_free_sum_le ps hps0 hps1 cs
  · exact fun c hc => ⟨argv_free_In cs c hc, List.mem_singleton.mpr (hall c hc),
      fs_free_In cs c hc, stdin_free_In cs c hc⟩
  · grind

/-- Cores with a fixed file system weigh at most that file system's own
weight. -/
theorem base_weight_fs_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (fs0 : Fs.Fs) (cs : List FinCore),
      cs.Nodup → (∀ c, c ∈ cs → c.core_fs = fs0) →
      qsum (base_weight ra qa re qe u v w ps) cs ≤ fs_point u v w fs0 := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 fs0 cs
    hnd hall
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1
    hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 (argv_free cs) (envp_free cs) [fs0]
    (stdin_free cs) 1 1 (fs_point u v w fs0) 1 cs ?_ ?_ ?_ ?_ hnd ?_) ?_
  · exact argv_free_sum_le ra qa hra0 hra1 hqa0 hqa1 cs
  · exact envp_free_sum_le re qe hre0 hre1 hqe0 hqe1 cs
  · rw [qsum_cons, qsum_nil]; grind
  · exact stdin_free_sum_le ps hps0 hps1 cs
  · exact fun c hc => ⟨argv_free_In cs c hc, envp_free_In cs c hc,
      List.mem_singleton.mpr (hall c hc), stdin_free_In cs c hc⟩
  · grind

/-- Cores whose standard input has one fixed length weigh at most
`ps * (1 - ps) ^ n`; no other coordinate is fixed. -/
theorem base_weight_stdin_slice_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (n : Nat) (cs : List FinCore),
      cs.Nodup → (∀ c, c ∈ cs → c.core_stdin.length = n) →
      qsum (base_weight ra qa re qe u v w ps) cs ≤ ps * Qpow (1 - ps) n := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 n cs
    hnd hall
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1
    hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 (argv_free cs) (envp_free cs)
    (fs_free cs) (byte_lists n) 1 1 1 (ps * Qpow (1 - ps) n) cs ?_ ?_ ?_ ?_ hnd ?_) ?_
  · exact argv_free_sum_le ra qa hra0 hra1 hqa0 hqa1 cs
  · exact envp_free_sum_le re qe hre0 hre1 hqe0 hqe1 cs
  · exact fs_free_sum_le u v w hu0 hu1 hv0 hv1 hw0 hw1 cs
  · rw [byte_lists_sum]; exact Rat.le_refl
  · refine fun c hc => ⟨argv_free_In cs c hc, envp_free_In cs c hc, fs_free_In cs c hc, ?_⟩
    rw [← hall c hc]
    exact byte_lists_complete c.core_stdin
  · grind

/-- Cores whose standard input is no longer than `n` weigh at most
`1 - (1 - ps) ^ (n + 1)`.  This misses the tail, which is what the
not-attained lemma is made of. -/
theorem base_weight_bound_by_max_length (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (n : Nat) (cs : List FinCore),
      cs.Nodup → (∀ c, c ∈ cs → c.core_stdin.length ≤ n) →
      qsum (base_weight ra qa re qe u v w ps) cs ≤ 1 - Qpow (1 - ps) (n + 1) := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 n cs
    hnd hall
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1
    hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 (argv_free cs) (envp_free cs)
    (fs_free cs) (short_inputs (n + 1)) 1 1 1 (1 - Qpow (1 - ps) (n + 1)) cs ?_ ?_ ?_ ?_
    hnd ?_) ?_
  · exact argv_free_sum_le ra qa hra0 hra1 hqa0 hqa1 cs
  · exact envp_free_sum_le re qe hre0 hre1 hqe0 hqe1 cs
  · exact fs_free_sum_le u v w hu0 hu1 hv0 hv1 hw0 hw1 cs
  · rw [short_inputs_sum, geo_prefix_sum_closed]; exact Rat.le_refl
  · refine fun c hc => ⟨argv_free_In cs c hc, envp_free_In cs c hc, fs_free_In cs c hc, ?_⟩
    exact short_inputs_complete (n + 1) c.core_stdin (by have := hall c hc; omega)
  · grind

/-! ## The file-contents marginal: one entry constrained, the rest free -/

/-- The cores the composability bound prices: the file at `pth` — the
first entry with that key, or nothing — extends `bs`.  Nothing else
about the file system is fixed. -/
def file_at_extends (pth : Fs.path) (bs : List byte) (c : FinCore) : Prop :=
  ∃ ext, fs_file pth c.core_fs = bs ++ ext

/-- Strip the first `n` bytes off the contents of the first entry keyed
`pth`, and leave everything else alone. -/
def fs_strip (pth : Fs.path) (n : Nat) : Fs.Fs → Fs.Fs
  | [] => []
  | (q, d) :: r =>
      if Fs.path_eqb pth q then (q, List.drop n d) :: r else (q, d) :: fs_strip pth n r

/-- The same strip on a core; the other three coordinates are untouched. -/
def core_strip (pth : Fs.path) (n : Nat) (c : FinCore) : FinCore :=
  FinCore.mkFinCore c.core_argv c.core_envp (fs_strip pth n c.core_fs) c.core_stdin

/-- Dropping a prefix's length off the concatenation leaves the suffix. -/
theorem skipn_length_app {A : Type} (l1 l2 : List A) :
    List.drop l1.length (l1 ++ l2) = l2 := List.drop_left

/-- A power at a sum of exponents is the product of the powers. -/
theorem Qpow_plus_exp (x : Rat) (m n : Nat) : Qpow x (m + n) = Qpow x m * Qpow x n := by
  induction m with
  | zero => simp only [Nat.zero_add, Qpow_0]; grind
  | succ m ih =>
    have hsum : m + 1 + n = (m + n) + 1 := by omega
    rw [hsum, Qpow_succ, Qpow_succ, ih]
    grind

/-- A byte string extending `bs` weighs the mass of `bs` times the
weight of what follows: the identity the injection pays with. -/
theorem geo_point_app (p : Rat) (bs ext : List byte) :
    geo_point p (bs ++ ext).length = geo_mass p bs.length * geo_point p ext.length := by
  rw [List.length_append, geo_point_closed_form, geo_mass_closed_form, geo_point_closed_form,
    Qpow_plus_exp, Qpow_plus_exp]
  grind

/-- Stripping nothing changes nothing. -/
theorem fs_strip_zero (pth : Fs.path) (fs : Fs.Fs) : fs_strip pth 0 fs = fs := by
  induction fs with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨q, d⟩ := e
    simp only [fs_strip]
    split
    · simp
    · rw [ih]

/-- A nonempty file at `pth` is a lookup hit at `pth`. -/
theorem fs_lookup_of_fs_file_cons (pth : Fs.path) (fs : Fs.Fs) (b : byte) (l : List byte) :
    fs_file pth fs = b :: l → Fs.fs_lookup fs pth = some (b :: l) := by
  intro h
  cases hlk : Fs.fs_lookup fs pth with
  | none => simp [fs_file, hlk] at h
  | some d =>
    simp only [fs_file, hlk] at h
    rw [h]

/-- The running product of a file system whose entry at `pth` extends
`bs` is the mass of `bs` times the running product of the stripped file
system. -/
theorem fs_factor_strip (u v w : Rat) (pth : Fs.path) (bs ext : List byte) (fs : Fs.Fs) :
    Fs.fs_lookup fs pth = some (bs ++ ext) →
    fs_factor u v w fs
      = geo_mass w bs.length * fs_factor u v w (fs_strip pth bs.length fs) := by
  induction fs with
  | nil => intro hlk; simp [Fs.fs_lookup] at hlk
  | cons e r ih =>
    obtain ⟨q, d⟩ := e
    intro hlk
    simp only [Fs.fs_lookup] at hlk
    simp only [fs_strip]
    cases hq : Fs.path_eqb pth q with
    | true =>
      simp only [hq, ite_true] at hlk ⊢
      have hd : d = bs ++ ext := Option.some.inj hlk
      subst hd
      simp only [fs_factor, skipn_length_app, geo_point_app]
      grind
    | false =>
      simp only [hq, Bool.false_eq_true, ite_false] at hlk ⊢
      simp only [fs_factor]
      rw [ih hlk]
      grind

/-- The strip is injective on the cores whose file at `pth` extends
`bs`. -/
theorem fs_strip_inj (pth : Fs.path) (bs : List byte) (fs1 fs2 : Fs.Fs)
    (ext1 ext2 : List byte) :
    Fs.fs_lookup fs1 pth = some (bs ++ ext1) → Fs.fs_lookup fs2 pth = some (bs ++ ext2) →
    fs_strip pth bs.length fs1 = fs_strip pth bs.length fs2 → fs1 = fs2 := by
  induction fs1 generalizing fs2 ext1 ext2 with
  | nil => intro h1 _ _; simp [Fs.fs_lookup] at h1
  | cons e1 r1 ih =>
    obtain ⟨q1, d1⟩ := e1
    intro h1 h2 hs
    cases fs2 with
    | nil => simp [Fs.fs_lookup] at h2
    | cons e2 r2 =>
      obtain ⟨q2, d2⟩ := e2
      simp only [Fs.fs_lookup] at h1 h2
      simp only [fs_strip] at hs
      cases hq1 : Fs.path_eqb pth q1 with
      | true =>
        simp only [hq1, ite_true] at h1 hs
        cases hq2 : Fs.path_eqb pth q2 with
        | true =>
          simp only [hq2, ite_true] at h2 hs
          simp only [List.cons.injEq, Prod.mk.injEq] at hs
          obtain ⟨⟨hq, hdrop⟩, hr⟩ := hs
          have hd1 : d1 = bs ++ ext1 := Option.some.inj h1
          have hd2 : d2 = bs ++ ext2 := Option.some.inj h2
          subst hd1
          subst hd2
          rw [skipn_length_app, skipn_length_app] at hdrop
          subst hq
          subst hdrop
          subst hr
          rfl
        | false =>
          simp only [hq2, Bool.false_eq_true, ite_false] at hs
          simp only [List.cons.injEq, Prod.mk.injEq] at hs
          obtain ⟨⟨hq, _⟩, _⟩ := hs
          rw [hq, hq2] at hq1
          simp at hq1
      | false =>
        simp only [hq1, Bool.false_eq_true, ite_false] at h1 hs
        cases hq2 : Fs.path_eqb pth q2 with
        | true =>
          simp only [hq2, ite_true] at hs
          simp only [List.cons.injEq, Prod.mk.injEq] at hs
          obtain ⟨⟨hq, _⟩, _⟩ := hs
          rw [← hq, hq1] at hq2
          simp at hq2
        | false =>
          simp only [hq2, Bool.false_eq_true, ite_false] at h2 hs
          simp only [List.cons.injEq, Prod.mk.injEq] at hs
          obtain ⟨⟨hq, hd⟩, hr⟩ := hs
          subst hq
          subst hd
          rw [ih r2 ext1 ext2 h1 h2 hr]

/-- The injection is weight-preserving up to the one factor the prefix
costs. -/
theorem base_weight_strip (ra qa re qe u v w ps : Rat) (pth : Fs.path) (bs : List byte)
    (c : FinCore) :
    file_at_extends pth bs c →
    base_weight ra qa re qe u v w ps c
      = geo_mass w bs.length
        * base_weight ra qa re qe u v w ps (core_strip pth bs.length c) := by
  intro hext
  obtain ⟨ext, hext⟩ := hext
  simp only [base_weight, core_strip]
  cases bs with
  | nil =>
    have h1 : geo_mass w ([] : List byte).length = 1 := by simp [geo_mass_closed_form, Qpow_0]
    simp only [List.length_nil, fs_strip_zero]
    grind
  | cons b bs' =>
    have hlk := fs_lookup_of_fs_file_cons pth c.core_fs b (bs' ++ ext) hext
    simp only [fs_point]
    rw [fs_factor_strip u v w pth (b :: bs') ext c.core_fs hlk]
    grind

/-- The strip is injective where the bound applies it. -/
theorem core_strip_inj (pth : Fs.path) (bs : List byte) (c1 c2 : FinCore) :
    file_at_extends pth bs c1 → file_at_extends pth bs c2 →
    core_strip pth bs.length c1 = core_strip pth bs.length c2 → c1 = c2 := by
  intro h1 h2 heq
  obtain ⟨ext1, h1⟩ := h1
  obtain ⟨ext2, h2⟩ := h2
  obtain ⟨a1, e1, f1, s1⟩ := c1
  obtain ⟨a2, e2, f2, s2⟩ := c2
  simp only [core_strip, FinCore.mkFinCore.injEq] at heq
  obtain ⟨ha, he, hf, hs⟩ := heq
  subst ha; subst he; subst hs
  refine congrArg (fun f => FinCore.mkFinCore a1 e1 f s1) ?_
  cases bs with
  | nil =>
    simp only [List.length_nil, fs_strip_zero] at hf
    exact hf
  | cons b bs' =>
    exact fs_strip_inj pth (b :: bs') f1 f2 ext1 ext2
      (fs_lookup_of_fs_file_cons pth f1 b (bs' ++ ext1) h1)
      (fs_lookup_of_fs_file_cons pth f2 b (bs' ++ ext2) h2) hf

/-- The strip preserves argv, which is what lets the composability bound
cite the argv marginal. -/
theorem core_strip_argv (pth : Fs.path) (n : Nat) (c : FinCore) :
    (core_strip pth n c).core_argv = c.core_argv := rfl

/-- The stripped list of a duplicate-free list is duplicate-free. -/
theorem NoDup_map_core_strip (pth : Fs.path) (bs : List byte) (cs : List FinCore) :
    (∀ c, c ∈ cs → file_at_extends pth bs c) → cs.Nodup →
    (cs.map (core_strip pth bs.length)).Nodup := by
  intro hall hnd
  refine NoDup_map_inj _ cs ?_ hnd
  intro x y hx hy heq
  exact core_strip_inj pth bs x y (hall x hx) (hall y hy) heq

/-- The list's weight is the prefix's mass times the stripped list's. -/
theorem qsum_base_weight_strip (ra qa re qe u v w ps : Rat) (pth : Fs.path) (bs : List byte)
    (cs : List FinCore) :
    (∀ c, c ∈ cs → file_at_extends pth bs c) →
    qsum (base_weight ra qa re qe u v w ps) cs
      = geo_mass w bs.length
        * qsum (base_weight ra qa re qe u v w ps) (cs.map (core_strip pth bs.length)) := by
  intro hall
  rw [qsum_map, ← qsum_scale (geo_mass w bs.length)
    (fun c => base_weight ra qa re qe u v w ps (core_strip pth bs.length c)) cs]
  exact qsum_ext _ _ cs
    (fun c hc => base_weight_strip ra qa re qe u v w ps pth bs c (hall c hc))

/-- The file-contents marginal: cores whose file at `pth` extends `bs`
weigh at most the mass of `bs` on the contents coordinate, with the
entry count, every other entry, the path's own bytes and the other three
coordinates all charged `1`. -/
theorem base_weight_file_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (pth : Fs.path) (bs : List byte) (cs : List FinCore),
      cs.Nodup → (∀ c, c ∈ cs → file_at_extends pth bs c) →
      qsum (base_weight ra qa re qe u v w ps) cs ≤ geo_mass w bs.length := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1
    pth bs cs hnd hall
  rw [qsum_base_weight_strip ra qa re qe u v w ps pth bs cs hall]
  have hmass : 0 ≤ geo_mass w bs.length := geo_mass_nonneg w bs.length hw1
  have hstripped : qsum (base_weight ra qa re qe u v w ps)
      (cs.map (core_strip pth bs.length)) ≤ 1 :=
    base_weight_mass_le_1 ra qa re qe u v w ps hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1
      hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 _ (NoDup_map_core_strip pth bs cs hall hnd)
  have h := Rat.mul_le_mul_of_nonneg_left hstripped hmass
  grind

/-- The composability bound: cores whose argv is `xs` and whose file at
`pth` extends `bs` weigh at most the argv's weight times the prefix's
mass. -/
theorem base_weight_argv_file_bound (ra qa re qe u v w ps : Rat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    ∀ (xs : List (List byte)) (pth : Fs.path) (bs : List byte) (cs : List FinCore),
      cs.Nodup →
      (∀ c, c ∈ cs → c.core_argv = xs ∧ file_at_extends pth bs c) →
      qsum (base_weight ra qa re qe u v w ps) cs
        ≤ strings_point ra qa xs * geo_mass w bs.length := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1
    xs pth bs cs hnd hall
  rw [qsum_base_weight_strip ra qa re qe u v w ps pth bs cs (fun c hc => (hall c hc).2)]
  have hmass : 0 ≤ geo_mass w bs.length := geo_mass_nonneg w bs.length hw1
  have hstripped : qsum (base_weight ra qa re qe u v w ps)
      (cs.map (core_strip pth bs.length)) ≤ strings_point ra qa xs := by
    refine base_weight_argv_bound ra qa re qe u v w ps hra0 hra1 hqa0 hqa1 hre0 hre1
      hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 xs _
      (NoDup_map_core_strip pth bs cs (fun c hc => (hall c hc).2) hnd) ?_
    intro c hc
    obtain ⟨c0, hc0, hceq⟩ := List.mem_map.mp hc
    rw [← hceq, core_strip_argv]
    exact (hall c0 hc0).1
  have h := Rat.mul_le_mul_of_nonneg_left hstripped hmass
  grind

/-! ## The marginal exports, on records -/

/-- Records with a fixed argv weigh at most that argv's own weight. -/
theorem full_support_base_argv_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs : List (List byte)) (l : List FinProcInput) :
    (l.map fin_core).Nodup → (∀ f, f ∈ l → f.fin_argv = xs) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ strings_point ra qa xs := by
  intro hnd hall
  rw [core_sum_map_fin_core]
  refine base_weight_argv_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hall f hf

/-- Records with a fixed environment weigh at most that environment's
own weight. -/
theorem full_support_base_envp_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (es : List (List byte)) (l : List FinProcInput) :
    (l.map fin_core).Nodup → (∀ f, f ∈ l → f.fin_envp = es) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ strings_point re qe es := by
  intro hnd hall
  rw [core_sum_map_fin_core]
  refine base_weight_envp_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 es _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hall f hf

/-- Records with a fixed file system weigh at most that file system's
own weight. -/
theorem full_support_base_fs_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (fs0 : Fs.Fs) (l : List FinProcInput) :
    (l.map fin_core).Nodup → (∀ f, f ∈ l → f.fin_image_fs = fs0) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ fs_point u v w fs0 := by
  intro hnd hall
  rw [core_sum_map_fin_core]
  refine base_weight_fs_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 fs0 _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hall f hf

/-- Records whose standard input has one fixed length weigh at most
`ps * (1 - ps) ^ n`. -/
theorem full_support_base_slice_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup → (∀ f, f ∈ l → f.fin_stdin.length = n) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ ps * Qpow (1 - ps) n := by
  intro hnd hall
  rw [core_sum_map_fin_core]
  refine base_weight_stdin_slice_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hall f hf

/-- Records whose standard input is no longer than `n` weigh at most
`1 - (1 - ps) ^ (n + 1)`. -/
theorem full_support_base_bound_by_max_length (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup → (∀ f, f ∈ l → f.fin_stdin.length ≤ n) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ 1 - Qpow (1 - ps) (n + 1) := by
  intro hnd hall
  rw [core_sum_map_fin_core]
  refine base_weight_bound_by_max_length ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hall f hf

/-- Records whose file at `pth` extends `bs` weigh at most the mass of
`bs` on the contents coordinate. -/
theorem full_support_base_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (pth : Fs.path) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup → (∀ f, f ∈ l → file_at_extends pth bs (fin_core f)) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ geo_mass w bs.length := by
  intro hnd hall
  rw [core_sum_map_fin_core]
  refine base_weight_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 pth bs _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hall f hf

/-- The composability bound on records: argv `xs` and a file at `pth`
extending `bs`. -/
theorem full_support_base_argv_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs : List (List byte)) (pth : Fs.path) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → f.fin_argv = xs ∧ file_at_extends pth bs (fin_core f)) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ strings_point ra qa xs * geo_mass w bs.length := by
  intro hnd hall
  rw [core_sum_map_fin_core]
  refine base_weight_argv_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs pth bs _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact ⟨(hall f hf).1, (hall f hf).2⟩

/-- The composability bound at the driver argv shape `[prog, pth]`, the
shape the file families' constructors build. -/
theorem full_support_base_path_argv_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (prog : List byte) (pth : Fs.path) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → f.fin_argv = path_argv prog pth ∧ file_at_extends pth bs (fin_core f)) →
    core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
      ≤ strings_point ra qa [prog, pth] * geo_mass w bs.length :=
  full_support_base_argv_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1
    Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 (path_argv prog pth) pth bs l

/-! ## The mass is a supremum and not a maximum -/

/-- For `ps < 1` no admissible list weighs the declared mass: the list's
own longest standard input is a horizon, and beyond it sits a positive
tail the list does not collect.  Only `ps < 1` is asked for. -/
theorem full_support_base_mass_not_attained (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) :
    ps < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
        < cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) := by
  intro hlt l hnd
  have hmass : cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) = 1 := rfl
  have hb := full_support_base_bound_by_max_length ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    (list_max (l.map (fun f => f.fin_stdin.length))) l hnd
    (fun f hf => list_max_ge _ _ (List.mem_map.mpr ⟨f, hf, rfl⟩))
  have hpos : 0 < Qpow (1 - ps) (list_max (l.map (fun f => f.fin_stdin.length)) + 1) :=
    Qpow_pos _ _ (by grind)
  rw [hmass]
  grind

/-- The same fact as a refusal of equality, which is the shape the
supremum argument is read in. -/
theorem full_support_base_mass_supremum_not_maximum (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) :
    ps < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      ¬ (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
          = cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
            Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) := by
  intro hlt l hnd heq
  have hne := full_support_base_mass_not_attained ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 hlt l hnd
  rw [heq] at hne
  exact Rat.lt_irrefl hne

/-! ## The lower certificate's file-system witness family -/

/-- Every list of exactly `m` pairs whose paths are shorter than `Lp`
and whose contents are shorter than `Lc`.  The bounds' enumeration is
not reused: the certificate needs a duplicate-free list. -/
def fss_len (Lp Lc : Nat) : Nat → List Fs.Fs
  | 0 => [[]]
  | m + 1 =>
      (short_inputs Lp).flatMap (fun pth =>
        (short_inputs Lc).flatMap (fun d =>
          (fss_len Lp Lc m).map (fun fs => (pth, d) :: fs)))

/-- The union of the entry-count slices below `M`. -/
def fss_upto (Lp Lc : Nat) : Nat → List Fs.Fs
  | 0 => []
  | M + 1 => fss_len Lp Lc M ++ fss_upto Lp Lc M

/-- Every member of a slice has that slice's entry count. -/
theorem fss_len_In_length (Lp Lc m : Nat) (fs : Fs.Fs) :
    fs ∈ fss_len Lp Lc m → fs.length = m := by
  induction m generalizing fs with
  | zero =>
    intro hfs
    simp only [fss_len, List.mem_singleton] at hfs
    rw [hfs]
    rfl
  | succ m ih =>
    intro hfs
    simp only [fss_len] at hfs
    obtain ⟨pth, _, hfs⟩ := List.mem_flatMap.mp hfs
    obtain ⟨d, _, hfs⟩ := List.mem_flatMap.mp hfs
    obtain ⟨fs', hin, heq⟩ := List.mem_map.mp hfs
    rw [← heq, List.length_cons, ih fs' hin]

/-- A slice is duplicate-free: a list of pairs determines its head and
its tail. -/
theorem fss_len_nodup (Lp Lc m : Nat) : (fss_len Lp Lc m).Nodup := by
  induction m with
  | zero =>
    simp only [fss_len]
    exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | succ m ih =>
    simp only [fss_len]
    refine NoDup_flat_map _ _ (short_inputs_nodup Lp) ?_ ?_
    · intro pth _
      refine NoDup_flat_map _ _ (short_inputs_nodup Lc) ?_ ?_
      · intro d _
        refine NoDup_map_inj _ _ ?_ ih
        intro x y _ _ heq
        exact (List.cons.injEq _ _ _ _ ▸ heq).2
      · intro d1 d2 fs _ _ h1 h2
        obtain ⟨x1, _, hx1⟩ := List.mem_map.mp h1
        obtain ⟨x2, _, hx2⟩ := List.mem_map.mp h2
        have h := hx1.trans hx2.symm
        simp only [List.cons.injEq, Prod.mk.injEq] at h
        exact h.1.2
    · intro p1 p2 fs _ _ h1 h2
      obtain ⟨d1, _, h1⟩ := List.mem_flatMap.mp h1
      obtain ⟨x1, _, hx1⟩ := List.mem_map.mp h1
      obtain ⟨d2, _, h2⟩ := List.mem_flatMap.mp h2
      obtain ⟨x2, _, hx2⟩ := List.mem_map.mp h2
      have h := hx1.trans hx2.symm
      simp only [List.cons.injEq, Prod.mk.injEq] at h
      exact h.1.1

/-- Every member of the union has fewer than `M` entries. -/
theorem fss_upto_In_length (Lp Lc M : Nat) (fs : Fs.Fs) :
    fs ∈ fss_upto Lp Lc M → fs.length < M := by
  induction M with
  | zero => intro hfs; simp only [fss_upto, List.not_mem_nil] at hfs
  | succ M ih =>
    intro hfs
    simp only [fss_upto, List.mem_append] at hfs
    rcases hfs with hfs | hfs
    · rw [fss_len_In_length Lp Lc M fs hfs]; omega
    · have := ih hfs; omega

/-- The union is duplicate-free: the slices are duplicate-free and
different slices hold different entry counts. -/
theorem fss_upto_nodup (Lp Lc M : Nat) : (fss_upto Lp Lc M).Nodup := by
  induction M with
  | zero => exact List.nodup_nil
  | succ M ih =>
    simp only [fss_upto]
    refine List.nodup_append.mpr ⟨fss_len_nodup Lp Lc M, ih, ?_⟩
    intro a ha b hb heq
    have h1 := fss_len_In_length Lp Lc M a ha
    have h2 := fss_upto_In_length Lp Lc M b hb
    rw [heq] at h1
    omega

/-- One full entry-count slice of file systems weighs a power whose base
is the product of what the path enumeration and the contents
enumeration collect, because each slot draws both. -/
theorem qsum_fs_entries_product_fss_len (v w : Rat) (Lp Lc m : Nat) :
    qsum (fs_entries_product v w) (fss_len Lp Lc m)
      = Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m := by
  induction m with
  | zero =>
    simp only [fss_len, qsum_cons, qsum_nil, fs_entries_product, Qpow_0]
    grind
  | succ m ih =>
    have inner : ∀ pth : Fs.path, pth ∈ short_inputs Lp →
        qsum (fs_entries_product v w) ((short_inputs Lc).flatMap (fun d =>
          (fss_len Lp Lc m).map (fun fs => (pth, d) :: fs)))
          = Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m
            * (1 - Qpow (1 - w) Lc) * geo_point v pth.length := by
      intro pth _
      have inner2 : ∀ d : List byte, d ∈ short_inputs Lc →
          qsum (fs_entries_product v w) ((fss_len Lp Lc m).map (fun fs => (pth, d) :: fs))
            = Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m
              * geo_point v pth.length * geo_point w d.length := by
        intro d _
        rw [qsum_map, qsum_ext (fun fs => fs_entries_product v w ((pth, d) :: fs))
          (fun fs => geo_point v pth.length * geo_point w d.length
            * fs_entries_product v w fs) (fss_len Lp Lc m) (fun fs _ => rfl), qsum_scale, ih]
        grind
      rw [qsum_flat_map, qsum_ext _ _ _ inner2, qsum_scale, short_inputs_sum,
        geo_prefix_sum_closed]
      grind
    simp only [fss_len]
    rw [qsum_flat_map, qsum_ext _ _ _ inner, qsum_scale, short_inputs_sum,
      geo_prefix_sum_closed, Qpow_succ]
    grind

/-- The same slice under the file-system law: the entry-count factor
times the slice's own power. -/
theorem qsum_fs_point_fss_len (u v w : Rat) (Lp Lc m : Nat) :
    qsum (fs_point u v w) (fss_len Lp Lc m)
      = u * Qpow (1 - u) m * Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m := by
  have hext : ∀ fs : Fs.Fs, fs ∈ fss_len Lp Lc m →
      fs_point u v w fs = u * Qpow (1 - u) m * fs_entries_product v w fs := by
    intro fs hfs
    rw [fs_point_closed_form, fss_len_In_length Lp Lc m fs hfs]
  rw [qsum_ext _ _ _ hext, qsum_scale, qsum_fs_entries_product_fss_len]

/-- The partial sum over entry counts is the environment coordinate's
`envp_prefix_sum` at the product base: the file-system coordinate is the
environment coordinate with a different slot total. -/
theorem qsum_fs_point_fss_upto (u v w : Rat) (Lp Lc M : Nat) :
    qsum (fs_point u v w) (fss_upto Lp Lc M)
      = envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [fss_upto, envp_prefix_sum]
    rw [qsum_app, ih, qsum_fs_point_fss_len]

/-! ## The margin arithmetic, four factors deep -/

/-- Two factors in the unit interval compose their margins: if each
falls short of `1` by at most its margin, the product falls short by at
most the sum.  The proof is one square: `x * y` exceeds `x + y - 1` by
`(1 - x) * (1 - y)`. -/
theorem Qprod_margin (x y a b : Rat) :
    0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 1 - a ≤ x → 1 - b ≤ y → 1 - (a + b) ≤ x * y := by
  intro hx0 hx1 hy0 hy1 ha hb
  have hsq : 0 ≤ (1 - x) * (1 - y) := Rat.mul_nonneg (by grind) (by grind)
  grind

/-- The unit interval is closed under multiplication. -/
theorem Qmult_unit (x y : Rat) :
    0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ x * y ∧ x * y ≤ 1 := by
  intro hx0 hx1 hy0 hy1
  refine ⟨Rat.mul_nonneg hx0 hy0, ?_⟩
  have h := fsb_mul_le_mul hx0 hx1 hy0 hy1
  grind

/-- The partial sum is nonnegative, term by term. -/
theorem envp_prefix_sum_nonneg (r G : Rat) (M : Nat) :
    0 ≤ r → r ≤ 1 → 0 ≤ G → 0 ≤ envp_prefix_sum r G M := by
  intro hr0 hr1 hG0
  induction M with
  | zero => simp only [envp_prefix_sum]; exact Rat.le_refl
  | succ M ih =>
    simp only [envp_prefix_sum]
    refine Rat.add_nonneg ?_ ih
    exact Rat.mul_nonneg (Rat.mul_nonneg hr0 (Qpow_nonneg _ _ (by grind)))
      (Qpow_nonneg _ _ hG0)

/-- The partial sum is under `1 - (1 - r) ^ M`, because each slot
collects at most `1`. -/
theorem envp_prefix_sum_le (r G : Rat) (M : Nat) :
    0 ≤ r → r ≤ 1 → 0 ≤ G → G ≤ 1 → envp_prefix_sum r G M ≤ 1 - Qpow (1 - r) M := by
  intro hr0 hr1 hG0 hG1
  induction M with
  | zero => simp only [envp_prefix_sum, Qpow_0]; grind
  | succ M ih =>
    have hrP : 0 ≤ r * Qpow (1 - r) M := Rat.mul_nonneg hr0 (Qpow_nonneg _ _ (by grind))
    have hterm : r * Qpow (1 - r) M * Qpow G M ≤ r * Qpow (1 - r) M * 1 :=
      fsb_mul_le_mul hrP Rat.le_refl (Qpow_nonneg G M hG0) (Qpow_le_1 G M hG0 hG1)
    simp only [envp_prefix_sum, Qpow_succ]
    grind

/-- The partial sum is in the unit interval. -/
theorem envp_prefix_sum_unit (r G : Rat) (M : Nat) :
    0 ≤ r → r ≤ 1 → 0 ≤ G → G ≤ 1 →
    0 ≤ envp_prefix_sum r G M ∧ envp_prefix_sum r G M ≤ 1 := by
  intro hr0 hr1 hG0 hG1
  refine ⟨envp_prefix_sum_nonneg r G M hr0 hr1 hG0, ?_⟩
  exact Rat.le_trans (envp_prefix_sum_le r G M hr0 hr1 hG0 hG1)
    (geo_head_unit r M hr0 hr1).2

/-- One string coordinate's margin: its partial sum at depths `(M, L)`
is within `M * (1 - q) ^ L + (1 - r) ^ M` of `1`.  No strict hypothesis
appears; the strictness is spent choosing the depths. -/
theorem strings_prefix_margin (r q : Rat) (L M : Nat) :
    0 ≤ r → r ≤ 1 → 0 ≤ q → q ≤ 1 →
    1 - (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M)
      ≤ envp_prefix_sum r (1 - Qpow (1 - q) L) M := by
  intro hr0 hr1 hq0 hq1
  obtain ⟨hx0, hx1⟩ := geo_tail_unit q L hq0 hq1
  obtain ⟨hG0, hG1⟩ := geo_head_unit q L hq0 hq1
  obtain ⟨hc0, hc1⟩ := geo_head_unit r M hr0 hr1
  refine Rat.le_trans ?_ (envp_prefix_sum_lower r (1 - Qpow (1 - q) L) M hr0 hr1 hG0 hG1)
  exact Qprod_margin _ _ _ _ (Qpow_nonneg _ _ hG0) (Qpow_le_1 _ _ hG0 hG1) hc0 hc1
    (Qpow_one_minus_lower _ M hx0 hx1) Rat.le_refl

/-- The file-system coordinate's margin: two entry-length shortfalls,
one per half of the pair, and one entry-count tail. -/
theorem fs_prefix_margin (u v w : Rat) (Lp Lc M : Nat) :
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
    1 - (Qnat M * Qpow (1 - v) Lp + Qnat M * Qpow (1 - w) Lc + Qpow (1 - u) M)
      ≤ envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M := by
  intro hu0 hu1 hv0 hv1 hw0 hw1
  obtain ⟨hxv0, hxv1⟩ := geo_tail_unit v Lp hv0 hv1
  obtain ⟨hGv0, hGv1⟩ := geo_head_unit v Lp hv0 hv1
  obtain ⟨hxw0, hxw1⟩ := geo_tail_unit w Lc hw0 hw1
  obtain ⟨hGw0, hGw1⟩ := geo_head_unit w Lc hw0 hw1
  obtain ⟨hc0, hc1⟩ := geo_head_unit u M hu0 hu1
  obtain ⟨hG0, hG1⟩ := Qmult_unit _ _ hGv0 hGv1 hGw0 hGw1
  refine Rat.le_trans ?_ (envp_prefix_sum_lower u _ M hu0 hu1 hG0 hG1)
  refine Qprod_margin _ _ _ _ (Qpow_nonneg _ _ hG0) (Qpow_le_1 _ _ hG0 hG1) hc0 hc1 ?_
    Rat.le_refl
  rw [Qpow_mult]
  exact Qprod_margin _ _ _ _ (Qpow_nonneg _ _ hGv0) (Qpow_le_1 _ _ hGv0 hGv1)
    (Qpow_nonneg _ _ hGw0) (Qpow_le_1 _ _ hGw0 hGw1)
    (Qpow_one_minus_lower _ M hxv0 hxv1) (Qpow_one_minus_lower _ M hxw0 hxw1)

/-- The certificate's margin arithmetic with the eight depths still
free: if the eight tails together come in under `eps`, the witness's
partial sum is within `eps` of `1`.  Four factors, each in the unit
interval, each within its own margin. -/
theorem full_support_margin_at_depths (ra qa re qe u v w ps eps : Rat)
    (Ma La Me Le Mf Lp Lc k : Nat) :
    0 ≤ ra → ra ≤ 1 → 0 ≤ qa → qa ≤ 1 → 0 ≤ re → re ≤ 1 → 0 ≤ qe → qe ≤ 1 →
    0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 ≤ ps → ps ≤ 1 →
    (Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
      + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
      + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
      + Qpow (1 - ps) k ≤ eps) →
    1 - eps
      ≤ envp_prefix_sum ra (1 - Qpow (1 - qa) La) Ma
        * envp_prefix_sum re (1 - Qpow (1 - qe) Le) Me
        * envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) Mf
        * (1 - Qpow (1 - ps) k) := by
  intro hra0 hra1 hqa0 hqa1 hre0 hre1 hqe0 hqe1 hu0 hu1 hv0 hv1 hw0 hw1 hps0 hps1 hsum
  obtain ⟨hGa0, hGa1⟩ := geo_head_unit qa La hqa0 hqa1
  obtain ⟨hGe0, hGe1⟩ := geo_head_unit qe Le hqe0 hqe1
  obtain ⟨hGv0, hGv1⟩ := geo_head_unit v Lp hv0 hv1
  obtain ⟨hGw0, hGw1⟩ := geo_head_unit w Lc hw0 hw1
  obtain ⟨hGf0, hGf1⟩ := Qmult_unit _ _ hGv0 hGv1 hGw0 hGw1
  obtain ⟨hSa0, hSa1⟩ := envp_prefix_sum_unit ra _ Ma hra0 hra1 hGa0 hGa1
  obtain ⟨hSe0, hSe1⟩ := envp_prefix_sum_unit re _ Me hre0 hre1 hGe0 hGe1
  obtain ⟨hSf0, hSf1⟩ := envp_prefix_sum_unit u _ Mf hu0 hu1 hGf0 hGf1
  obtain ⟨hSs0, hSs1⟩ := geo_head_unit ps k hps0 hps1
  obtain ⟨hSae0, hSae1⟩ := Qmult_unit _ _ hSa0 hSa1 hSe0 hSe1
  obtain ⟨hSaef0, hSaef1⟩ := Qmult_unit _ _ hSae0 hSae1 hSf0 hSf1
  have hstep : (1 : Rat) - eps
      ≤ 1 - (Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
        + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
        + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
        + Qpow (1 - ps) k) := by grind
  refine Rat.le_trans hstep ?_
  refine Qprod_margin _ _ _ _ hSaef0 hSaef1 hSs0 hSs1 ?_ Rat.le_refl
  refine Qprod_margin _ _ _ _ hSae0 hSae1 hSf0 hSf1 ?_
    (fs_prefix_margin u v w Lp Lc Mf hu0 hu1 hv0 hv1 hw0 hw1)
  exact Qprod_margin _ _ _ _ hSa0 hSa1 hSe0 hSe1
    (strings_prefix_margin ra qa La Ma hra0 hra1 hqa0 hqa1)
    (strings_prefix_margin re qe Le Me hre0 hre1 hqe0 hqe1)

/-- An entry-length depth is chosen after the entry count it has to
cover: `M` slots each shorter than `delta / (M + 1)` cost under
`delta`. -/
theorem entry_depth_for (q delta : Rat) (M : Nat) :
    0 < q → q ≤ 1 → 0 < delta → ∃ L : Nat, Qnat M * Qpow (1 - q) L ≤ delta := by
  intro hq hq1 hd
  have hM := Qnat_nonneg M
  have hD : 0 < Qnat M + 1 := by grind
  have hinv : 0 < (Qnat M + 1)⁻¹ := Rat.inv_pos.mpr hD
  obtain ⟨L, hL⟩ := geo_gap_small q (delta * (Qnat M + 1)⁻¹) hq hq1 (Rat.mul_pos hd hinv)
  refine ⟨L, ?_⟩
  have hcancel : (Qnat M + 1) * (Qnat M + 1)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hD)
  have hMD : Qnat M * (Qnat M + 1)⁻¹ ≤ 1 := by
    have h1 : Qnat M * (Qnat M + 1)⁻¹ ≤ (Qnat M + 1) * (Qnat M + 1)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hinv)
    grind
  have hstep : Qnat M * Qpow (1 - q) L ≤ Qnat M * (delta * (Qnat M + 1)⁻¹) :=
    Rat.mul_le_mul_of_nonneg_left hL hM
  have hstep2 : Qnat M * (Qnat M + 1)⁻¹ * delta ≤ 1 * delta :=
    Rat.mul_le_mul_of_nonneg_right hMD (Rat.le_of_lt hd)
  grind

/-- The depths that meet the margin: each strictness buys one depth,
eight in all, and each is asked for an eighth of the margin. -/
theorem full_support_depths_above (ra qa re qe u v w ps eps : Rat) :
    0 < ra → ra ≤ 1 → 0 < qa → qa ≤ 1 → 0 < re → re ≤ 1 → 0 < qe → qe ≤ 1 →
    0 < u → u ≤ 1 → 0 < v → v ≤ 1 → 0 < w → w ≤ 1 → 0 < ps → ps ≤ 1 → 0 < eps →
    ∃ Ma La Me Le Mf Lp Lc k : Nat,
      Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
        + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
        + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
        + Qpow (1 - ps) k ≤ eps := by
  intro hra hra1 hqa hqa1 hre hre1 hqe hqe1 hu hu1 hv hv1 hw hw1 hps hps1 heps
  have heps8 : 0 < eps * (1 / 8 : Rat) := Rat.mul_pos heps (by decide +kernel)
  obtain ⟨Ma, hMa⟩ := geo_gap_small ra (eps * (1 / 8)) hra hra1 heps8
  obtain ⟨La, hLa⟩ := entry_depth_for qa (eps * (1 / 8)) Ma hqa hqa1 heps8
  obtain ⟨Me, hMe⟩ := geo_gap_small re (eps * (1 / 8)) hre hre1 heps8
  obtain ⟨Le, hLe⟩ := entry_depth_for qe (eps * (1 / 8)) Me hqe hqe1 heps8
  obtain ⟨Mf, hMf⟩ := geo_gap_small u (eps * (1 / 8)) hu hu1 heps8
  obtain ⟨Lp, hLp⟩ := entry_depth_for v (eps * (1 / 8)) Mf hv hv1 heps8
  obtain ⟨Lc, hLc⟩ := entry_depth_for w (eps * (1 / 8)) Mf hw hw1 heps8
  obtain ⟨k, hk⟩ := geo_gap_small ps (eps * (1 / 8)) hps hps1 heps8
  exact ⟨Ma, La, Me, Le, Mf, Lp, Lc, k, by grind⟩

/-! ## The witness, and the certificate -/

/-- The witness family: one record per quadruple drawn from the four
prefix families.  Nothing in it is claimed valid. -/
def full_support_lower_witness (Ma La Me Le Mf Lp Lc k : Nat) : List FinProcInput :=
  (full_support_product (envps_upto La Ma) (envps_upto Le Me) (fss_upto Lp Lc Mf)
    (short_inputs k)).map core_input

/-- The witness's cores are the product enumeration itself. -/
theorem map_fin_core_full_support_lower_witness (Ma La Me Le Mf Lp Lc k : Nat) :
    (full_support_lower_witness Ma La Me Le Mf Lp Lc k).map fin_core
      = full_support_product (envps_upto La Ma) (envps_upto Le Me) (fss_upto Lp Lc Mf)
        (short_inputs k) :=
  map_fin_core_core_input _

/-- The witness is admissible: its cores are duplicate-free, because all
four coordinates are. -/
theorem full_support_lower_witness_nodup (Ma La Me Le Mf Lp Lc k : Nat) :
    ((full_support_lower_witness Ma La Me Le Mf Lp Lc k).map fin_core).Nodup := by
  rw [map_fin_core_full_support_lower_witness]
  exact NoDup_full_support_product _ _ _ _ (envps_upto_nodup La Ma) (envps_upto_nodup Le Me)
    (fss_upto_nodup Lp Lc Mf) (short_inputs_nodup k)

/-- The witness at each choice of the eight depths: an admissible list
weighing exactly the product of the four coordinates' partial sums.
Unconditional arithmetic. -/
theorem full_support_base_mass_lower_witness (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Ma La Me Le Mf Lp Lc k : Nat) :
    ((full_support_lower_witness Ma La Me Le Mf Lp Lc k).map fin_core).Nodup
    ∧ core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
        (full_support_lower_witness Ma La Me Le Mf Lp Lc k)
      = envp_prefix_sum ra (1 - Qpow (1 - qa) La) Ma
        * envp_prefix_sum re (1 - Qpow (1 - qe) Le) Me
        * envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) Mf
        * (1 - Qpow (1 - ps) k) := by
  refine ⟨full_support_lower_witness_nodup Ma La Me Le Mf Lp Lc k, ?_⟩
  have hw : cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)
      = base_weight ra qa re qe u v w ps := rfl
  rw [core_sum_map_fin_core, hw, map_fin_core_full_support_lower_witness,
    qsum_full_support_product]
  simp only [strings_point]
  rw [qsum_envp_point_envps_upto, qsum_envp_point_envps_upto, qsum_fs_point_fss_upto,
    short_inputs_sum, geo_prefix_sum_closed]

/-- The lower certificate: for every margin `eps` there is an admissible
list weighing at least the declared mass minus that margin.  With the
upper certificate above it, the declared `1` is the least upper bound of
the admissible partial sums.  All eight strict inequalities are
hypotheses here and not tightenings of the constructor, so every
degenerate member a consumer has already built stays a member. -/
theorem full_support_base_mass_lower_certificate (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) (eps : Rat) :
    0 < ra → 0 < qa → 0 < re → 0 < qe → 0 < u → 0 < v → 0 < w → 0 < ps → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) - eps
        ≤ core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
            Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l := by
  intro hra hqa hre hqe hu hv hw hps heps
  obtain ⟨Ma, La, Me, Le, Mf, Lp, Lc, k, hsum⟩ :=
    full_support_depths_above ra qa re qe u v w ps eps hra Hra1 hqa Hqa1 hre Hre1 hqe Hqe1
      hu Hu1 hv Hv1 hw Hw1 hps Hps1 heps
  refine ⟨full_support_lower_witness Ma La Me Le Mf Lp Lc k,
    full_support_lower_witness_nodup Ma La Me Le Mf Lp Lc k, ?_⟩
  rw [(full_support_base_mass_lower_witness ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Ma La Me Le Mf Lp Lc k).2]
  have hmass : cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) = 1 := rfl
  rw [hmass]
  exact full_support_margin_at_depths ra qa re qe u v w ps eps Ma La Me Le Mf Lp Lc k
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 hsum

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
