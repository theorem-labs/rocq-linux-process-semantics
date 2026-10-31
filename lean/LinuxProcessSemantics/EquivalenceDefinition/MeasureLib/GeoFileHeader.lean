-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Calibrated
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFile

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-!

# MeasureLib — geometric file contents behind a fixed header

This file holds Rocq `theories/EquivalenceDefinition/MeasureLib.v` lines
8986-10041, the combinator that weighs the bytes of one file AFTER a fixed
header.

A driver that parses a header before it hands anything to the library under
test rejects nearly every file `file_geometric` weighs, so a bound over the
whole-file family prices the reject path. This family takes the header as a
parameter and weighs only the payload: a matching core whose file is
`hdr ++ t` weighs `geo_point p t.length`, a matching core whose file does not
begin with `hdr` weighs zero, and the declared mass is `1`.

It is the whole-file family composed with `t ↦ hdr ++ t`. That map is
injective, so the block identity carries over through `qsum_map` and every
byte-list sum is reused as it stands. What is proved here is the weight's
rewrite rules, its nonnegativity, the shifted block identity, and the depth
step of the cylinder bound.

At the empty header the family is `file_geometric` pointwise, and the header
bites: a core whose file misses the header weighs zero while the mass stays
`1`.
-/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## Splitting a header off a byte list -/

/-- `some t` exactly when `d = hdr ++ t`. One decidable byte comparison per
header byte, so that it computes on closed instances. -/
def strip_prefix : List byte → List byte → Option (List byte)
  | [], d => some d
  | _ :: _, [] => none
  | h :: hdr', b :: d' => if h = b then strip_prefix hdr' d' else none

/-- Stripping a header off a list that was built from it gives the rest. -/
theorem strip_prefix_app (hdr t : List byte) : strip_prefix hdr (hdr ++ t) = some t := by
  induction hdr with
  | nil => rfl
  | cons h hdr ih =>
    show (if h = h then strip_prefix hdr (hdr ++ t) else none) = some t
    rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : h = h))]
    exact ih

/-- A successful strip says what the list was. -/
theorem strip_prefix_Some (hdr d t : List byte) :
    strip_prefix hdr d = some t → d = hdr ++ t := by
  induction hdr generalizing d with
  | nil =>
    intro h
    have : d = t := Option.some.inj h
    rw [this]
    rfl
  | cons hb hdr ih =>
    cases d with
    | nil => intro h; exact absurd h (by simp [strip_prefix])
    | cons b d =>
      intro h
      show b :: d = hb :: (hdr ++ t)
      have h' : (if hb = b then strip_prefix hdr d else none) = some t := h
      by_cases hbb : hb = b
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hbb)] at h'
        rw [← hbb, ih d h']
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hbb)] at h'
        exact absurd h' (by simp)

/-- A failed strip says no payload extends the header to the list. -/
theorem strip_prefix_None (hdr d : List byte) :
    strip_prefix hdr d = none → ∀ t, d ≠ hdr ++ t := by
  intro h t heq
  rw [heq, strip_prefix_app] at h
  exact absurd h (by simp)

/-- ... and conversely: no extension makes the strip fail. -/
theorem strip_prefix_None_of_no_extension (hdr d : List byte) :
    (∀ t, d ≠ hdr ++ t) → strip_prefix hdr d = none := by
  intro h
  cases hs : strip_prefix hdr d with
  | none => rfl
  | some t => exact absurd (strip_prefix_Some hdr d t hs) (h t)

/-- The empty header strips nothing. -/
theorem strip_prefix_nil (d : List byte) : strip_prefix [] d = some d := rfl

/-! ## The embedding -/

/-- `file_core` composed with `t ↦ hdr ++ t`, with `t` last so the partial
application is that map. Every enumeration below is pushed through it. -/
def file_prefix_core (hdr : List byte) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (t : List byte) : FinCore :=
  file_core argv envp fs0 pth s (hdr ++ t)

/-- The file of a shifted template is the header followed by the payload. -/
theorem fs_file_file_prefix_core (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s t : List byte) :
    fs_file pth (file_prefix_core hdr argv envp fs0 pth s t).core_fs = hdr ++ t :=
  fs_file_file_core argv envp fs0 pth s (hdr ++ t)

/-- The shifted template is injective in the payload. This is the fact the
counting and duplicate-freedom arguments spend. -/
theorem file_prefix_core_inj (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s t1 t2 : List byte) :
    file_prefix_core hdr argv envp fs0 pth s t1
      = file_prefix_core hdr argv envp fs0 pth s t2 → t1 = t2 := by
  intro heq
  exact List.append_cancel_left
    (file_core_inj argv envp fs0 pth s (hdr ++ t1) (hdr ++ t2) heq)

/-! ## The weight -/

/-- The environment test is `file_geo_weight`'s, unchanged. What differs is
what is read off a matching core: the payload past the header, or nothing if
the header is not there. -/
def file_prefix_geo_weight (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) : Rat :=
  if c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) then
    match strip_prefix hdr (fs_file pth c.core_fs) with
    | some t => geo_point p t.length
    | none => 0
  else 0

/-- The weight at a shifted template: the payload's geometric point mass. -/
theorem file_prefix_geo_weight_match (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s t : List byte) :
    file_prefix_geo_weight hdr p argv envp fs0 pth s
        (file_prefix_core hdr argv envp fs0 pth s t) = geo_point p t.length := by
  have hf : fs_file pth (file_prefix_core hdr argv envp fs0 pth s t).core_fs = hdr ++ t :=
    fs_file_file_prefix_core hdr argv envp fs0 pth s t
  have hc : file_prefix_core hdr argv envp fs0 pth s t
      = file_core argv envp fs0 pth s (hdr ++ t) := rfl
  unfold file_prefix_geo_weight
  rw [hf, ite_eq_left_of_eq_true _ _ (eq_true hc), strip_prefix_app]

/-- A core that is not the template weighs zero. -/
theorem file_prefix_geo_weight_mismatch (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs) →
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  intro hne
  unfold file_prefix_geo_weight
  rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]

/-- A core whose file does not strip weighs zero. -/
theorem file_prefix_geo_weight_off_header (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    strip_prefix hdr (fs_file pth c.core_fs) = none →
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  intro hn
  unfold file_prefix_geo_weight
  rw [hn]
  split <;> rfl

/-- The same, in the form a caller states it: no payload makes the file
`hdr ++ t`. -/
theorem file_prefix_geo_weight_off_header_zero (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    (∀ t, fs_file pth c.core_fs ≠ hdr ++ t) →
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  intro hno
  exact file_prefix_geo_weight_off_header hdr p argv envp fs0 pth s c
    (strip_prefix_None_of_no_extension hdr (fs_file pth c.core_fs) hno)

/-- The weight is nonnegative when the stop probability is a probability. -/
theorem file_prefix_geo_weight_nonneg (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    0 ≤ p → p ≤ 1 → ∀ c, 0 ≤ file_prefix_geo_weight hdr p argv envp fs0 pth s c := by
  intro hp0 hp1 c
  unfold file_prefix_geo_weight
  split
  · split
    · exact geo_point_nonneg p _ hp0 hp1
    · exact Rat.le_refl
  · exact Rat.le_refl

/-- The distribution. Mass `1` is declared: it is the geometric mass of the
payload. `file_geometric_prefix_mass_upper` and
`file_geometric_prefix_mass_lower_certificate` are the two halves of the
certificate that the declaration is honest. -/
def file_geometric_prefix (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    CoreDistribution :=
  CoreDistribution.mkCoreDistribution (file_prefix_geo_weight hdr p argv envp fs0 pth s) 1
    (file_prefix_geo_weight_nonneg hdr p argv envp fs0 pth s Hp0 Hp1)

/-! ## The empty header: `file_geometric`, pointwise -/

/-- At the empty header the payload is the file, and the weight is
`file_geo_weight`'s by conversion. -/
theorem file_prefix_geo_weight_nil (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    file_prefix_geo_weight [] p argv envp fs0 pth s c
      = file_geo_weight p argv envp fs0 pth s c := by
  unfold file_prefix_geo_weight file_geo_weight
  split <;> rfl

/-- The empty-header family weighs every core as `file_geometric` does. -/
theorem file_geometric_prefix_nil_pointwise (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (c : FinCore) :
    cd_weight (file_geometric_prefix [] p argv envp fs0 pth s Hp0 Hp1) c
      = cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1) c := by
  show file_prefix_geo_weight [] p argv envp fs0 pth s c
    = file_geo_weight p argv envp fs0 pth s c
  exact file_prefix_geo_weight_nil p argv envp fs0 pth s c

/-- ... and declares the same mass. -/
theorem file_geometric_prefix_nil_mass (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    cd_mass (file_geometric_prefix [] p argv envp fs0 pth s Hp0 Hp1)
      = cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1) := rfl

/-! ## The block identity, shifted -/

/-- A block of cores obtained by mapping the shifted template over a list of
payloads weighs what that list of payloads weighs under `geo_point`. The
header contributes no factor, which is the whole design. -/
theorem qsum_file_prefix_block (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (B : List (List byte)) :
    qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
        (B.map (file_prefix_core hdr argv envp fs0 pth s))
      = qsum (fun t => geo_point p t.length) B := by
  rw [qsum_map]
  exact qsum_ext _ _ B (fun t _ => file_prefix_geo_weight_match hdr p argv envp fs0 pth s t)

/-! ## The payload cylinder, and the enumeration that bounds it -/

/-- The cores this bound is about: the fixed environment, and a file whose
PAYLOAD extends `bs`, so the file itself is `hdr ++ bs ++ ext`. -/
def in_file_prefix_cylinder (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (bs : List byte) (c : FinCore) : Prop :=
  ∃ ext, c = file_prefix_core hdr argv envp fs0 pth s (bs ++ ext)

/-- It is `in_file_cylinder` over `hdr ++ bs`. -/
theorem in_file_prefix_cylinder_iff (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s bs : List byte) (c : FinCore) :
    in_file_prefix_cylinder hdr argv envp fs0 pth s bs c
      ↔ in_file_cylinder argv envp fs0 pth s (hdr ++ bs) c := by
  unfold in_file_prefix_cylinder in_file_cylinder file_prefix_core
  constructor
  · rintro ⟨ext, rfl⟩
    exact ⟨ext, by rw [List.append_assoc]⟩
  · rintro ⟨ext, rfl⟩
    exact ⟨ext, by rw [List.append_assoc]⟩

/-- The depth to enumerate PAYLOADS to: the longest file in the list, less
the header. -/
def cores_file_prefix_depth (hdr : List byte) (pth : Fs.path) (cs : List FinCore) : Nat :=
  cores_file_depth pth cs - hdr.length

/-- Every payload occurring in the list is no longer than that depth. -/
theorem cores_file_prefix_depth_ge (hdr : List byte) (pth : Fs.path) (cs : List FinCore)
    (c : FinCore) (t : List byte) :
    c ∈ cs → fs_file pth c.core_fs = hdr ++ t →
    t.length ≤ cores_file_prefix_depth hdr pth cs := by
  intro hc ht
  unfold cores_file_prefix_depth
  have hd := cores_file_depth_ge pth cs c hc
  rw [ht, List.length_append] at hd
  omega

/-- The bound over cores: the enumeration is `bytes_cyl` over payloads mapped
through the shifted embedding, and `bytes_cyl_sum_le` bounds it unchanged. -/
theorem file_prefix_geo_weight_cylinder_bound (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    0 ≤ p → p ≤ 1 →
    ∀ (bs : List byte) (cs : List FinCore),
      cs.Nodup →
      (∀ c, c ∈ cs → in_file_prefix_cylinder hdr argv envp fs0 pth s bs c) →
      qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s) cs ≤ geo_mass p bs.length := by
  intro hp0 hp1 bs cs hnd hcyl
  have hincl : cs ⊆ (bytes_cyl bs (cores_file_prefix_depth hdr pth cs)).map
      (file_prefix_core hdr argv envp fs0 pth s) := by
    intro c hc
    obtain ⟨ext, hext⟩ := hcyl c hc
    have hd := cores_file_prefix_depth_ge hdr pth cs c (bs ++ ext) hc
      (by rw [hext]; exact fs_file_file_prefix_core hdr argv envp fs0 pth s (bs ++ ext))
    rw [List.length_append] at hd
    rw [hext]
    exact List.mem_map.mpr ⟨bs ++ ext, bytes_cyl_In _ bs ext (by omega), rfl⟩
  refine Rat.le_trans (qsum_core_incl_le _ cs _
    (file_prefix_geo_weight_nonneg hdr p argv envp fs0 pth s hp0 hp1) hnd hincl) ?_
  rw [qsum_file_prefix_block]
  exact bytes_cyl_sum_le p hp0 hp1 _ bs

/-! ## The exports -/

/-- The payload cylinder's mass is the whole-file family's number at the same
payload prefix: the header costs nothing. -/
def file_geometric_prefix_cylinder_mass (p : Rat) (bs : List byte) : Rat :=
  file_geometric_cylinder_mass p bs

/-- The cylinder mass in closed form. -/
theorem file_geometric_prefix_cylinder_mass_closed_form (p : Rat) (bs : List byte) :
    file_geometric_prefix_cylinder_mass p bs
      = Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length :=
  file_geometric_cylinder_mass_closed_form p bs

/-- A list of records with duplicate-free cores, all in the cylinder over a
payload prefix behind the header, weighs at most that cylinder's mass. A fire
set described by "after the header, the input begins with these bytes" is
charged a number that does not pay for the header. -/
theorem file_geometric_prefix_bound (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)) →
    core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ file_geometric_prefix_cylinder_mass p bs := by
  intro hnd hcyl
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l
    ≤ file_geometric_prefix_cylinder_mass p bs
  rw [core_sum_map_fin_core]
  show qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s) (l.map fin_core)
    ≤ geo_mass p bs.length
  refine file_prefix_geo_weight_cylinder_bound hdr p argv envp fs0 pth s Hp0 Hp1 bs _ hnd ?_
  intro c hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
  rw [← hfc]
  exact hcyl f hf

/-! ## The membership tests as booleans -/

/-- Does the core's file strip? -/
def matches_file_header (hdr : List byte) (pth : Fs.path) (c : FinCore) : Bool :=
  match strip_prefix hdr (fs_file pth c.core_fs) with
  | some _ => true
  | none => false

/-- The environment half is `matches_file_env` unchanged; the header half
asks whether the file strips. -/
def matches_file_prefix_env (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) : Bool :=
  matches_file_env argv envp fs0 pth s c && matches_file_header hdr pth c

/-- A core the test rejects misses the environment or misses the header. -/
theorem matches_file_prefix_env_false (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    matches_file_prefix_env hdr argv envp fs0 pth s c = false →
    c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs)
      ∨ strip_prefix hdr (fs_file pth c.core_fs) = none := by
  intro h
  unfold matches_file_prefix_env at h
  by_cases henv : matches_file_env argv envp fs0 pth s c = true
  · right
    rw [henv, Bool.true_and] at h
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none => rfl
    | some t =>
      unfold matches_file_header at h
      rw [hs] at h
      exact absurd h (by simp)
  · left
    simp only [Bool.not_eq_true] at henv
    exact matches_file_env_false argv envp fs0 pth s c henv

/-- ... and therefore weighs zero. -/
theorem file_prefix_geo_weight_unmatched (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    matches_file_prefix_env hdr argv envp fs0 pth s c = false →
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  intro h
  rcases matches_file_prefix_env_false hdr argv envp fs0 pth s c h with hne | hn
  · exact file_prefix_geo_weight_mismatch hdr p argv envp fs0 pth s c hne
  · exact file_prefix_geo_weight_off_header hdr p argv envp fs0 pth s c hn

/-- A core the test accepts is the shifted template at some payload. -/
theorem matches_file_prefix_env_true (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    matches_file_prefix_env hdr argv envp fs0 pth s c = true →
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t := by
  intro h
  unfold matches_file_prefix_env at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨henv, hh⟩ := h
  have hc := matches_file_env_true argv envp fs0 pth s c henv
  cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
  | none =>
    unfold matches_file_header at hh
    rw [hs] at hh
    exact absurd hh (by simp)
  | some t =>
    refine ⟨t, ?_⟩
    unfold file_prefix_core
    rw [← strip_prefix_Some hdr (fs_file pth c.core_fs) t hs]
    exact hc

/-- The cylinder bound, slackened the only way it can be: each record is in
the cylinder or weighs nothing — off the environment, or its file misses the
header. -/
theorem file_geometric_prefix_bound_or_off_environment (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l →
      in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)
      ∨ matches_file_prefix_env hdr argv envp fs0 pth s (fin_core f) = false) →
    core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ file_geometric_prefix_cylinder_mass p bs := by
  intro hnd hor
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l
    ≤ file_geometric_prefix_cylinder_mass p bs
  rw [core_sum_map_fin_core,
    qsum_filter (file_prefix_geo_weight hdr p argv envp fs0 pth s)
      (matches_file_prefix_env hdr argv envp fs0 pth s) (l.map fin_core)
      (fun c hc => file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c hc)]
  show qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
      ((l.map fin_core).filter (matches_file_prefix_env hdr argv envp fs0 pth s))
    ≤ geo_mass p bs.length
  refine file_prefix_geo_weight_cylinder_bound hdr p argv envp fs0 pth s Hp0 Hp1 bs _
    (List.Pairwise.filter _ hnd) ?_
  intro c hc
  rw [List.mem_filter] at hc
  obtain ⟨hin, hm⟩ := hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hin
  rcases hor f hf with hcyl | hoff
  · rw [← hfc]; exact hcyl
  · rw [hfc] at hoff
    rw [hoff] at hm
    exact absurd hm (by simp)

/-- Upper certificate: every admissible list weighs at most the declared mass
`1`. The disjunction is exhaustive at the empty payload prefix. -/
theorem file_geometric_prefix_mass_upper (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) := by
  intro hnd
  have hmass : cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)
      = file_geometric_prefix_cylinder_mass p [] := rfl
  rw [hmass]
  refine file_geometric_prefix_bound_or_off_environment hdr p argv envp fs0 pth s
    Hp0 Hp1 [] l hnd ?_
  intro f hf
  by_cases hm : matches_file_prefix_env hdr argv envp fs0 pth s (fin_core f) = true
  · left
    obtain ⟨t, ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s (fin_core f) hm
    exact ⟨t, ht⟩
  · right
    simp only [Bool.not_eq_true] at hm
    exact hm

/-! ## The counting lemma and the payload-length slice -/

/-- A list of records with duplicate-free cores, every core the shifted
template at a payload of length exactly `n`, has at most `256 ^ n` elements. -/
theorem injective_core_list_in_file_prefix_cylinder_length_bound (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
            ∧ t.length = n) →
    l.length ≤ 256 ^ n := by
  intro hnd hall
  have hsub : (l.map fin_core) ⊆ (byte_lists n).map (file_prefix_core hdr argv envp fs0 pth s) := by
    intro c hc
    obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
    obtain ⟨t, ht, hlen⟩ := hall f hf
    refine List.mem_map.mpr ⟨t, ?_, ?_⟩
    · rw [← hlen]; exact byte_lists_complete t
    · rw [← ht]; exact hfc
  have hle := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_map] at hle
  rwa [byte_lists_length] at hle

/-- ... and attained at every `n`, where injectivity of the shifted template
is spent. -/
theorem injective_core_list_in_file_prefix_cylinder_length_bound_attained (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (n : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ (∀ f, f ∈ l → ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
              ∧ t.length = n)
      ∧ l.length = 256 ^ n := by
  refine ⟨(byte_lists n).map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t)),
    ?_, ?_, ?_⟩
  · rw [List.map_map]
    have hcomp : (fin_core ∘ fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
        = file_prefix_core hdr argv envp fs0 pth s := by
      funext t
      exact fin_core_core_input _
    rw [hcomp]
    exact NoDup_map_inj _ _
      (fun x y _ _ h => file_prefix_core_inj hdr argv envp fs0 pth s x y h)
      (byte_lists_nodup n)
  · intro f hf
    obtain ⟨t, hin, hft⟩ := List.mem_map.mp hf
    refine ⟨t, ?_, byte_lists_In_length n t hin⟩
    rw [← hft]
    exact fin_core_core_input _
  · rw [List.length_map, byte_lists_length]

/-- The payload-length slice: a list drawn from one payload-length slice
weighs at most `p * (1 - p) ^ n`, the same constant the whole-file family has
at FILE length `n`. -/
theorem file_geometric_prefix_slice_bound (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
            ∧ t.length = n) →
    core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ p * Qpow (1 - p) n := by
  intro hnd hall
  have hconst : qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s) (l.map fin_core)
      = Qnat (l.map fin_core).length * geo_point p n := by
    refine qsum_const _ _ _ ?_
    intro c hc
    obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
    obtain ⟨t, ht, hlen⟩ := hall f hf
    rw [← hfc, ht, file_prefix_geo_weight_match, hlen]
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core, hconst, ← geo_slice_total p n, List.length_map]
  exact Rat.mul_le_mul_of_nonneg_right
    (Qnat_le l.length (256 ^ n)
      (injective_core_list_in_file_prefix_cylinder_length_bound hdr argv envp fs0 pth s n l
        hnd hall))
    (geo_point_nonneg p n Hp0 Hp1)

/-- The slice constant is reached. -/
theorem file_geometric_prefix_slice_bound_attained (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ (∀ f, f ∈ l → ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
              ∧ t.length = n)
      ∧ core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
          = p * Qpow (1 - p) n := by
  obtain ⟨l, hnd, hall, hlen⟩ :=
    injective_core_list_in_file_prefix_cylinder_length_bound_attained hdr argv envp fs0 pth s n
  refine ⟨l, hnd, hall, ?_⟩
  have hconst : qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s) (l.map fin_core)
      = Qnat (l.map fin_core).length * geo_point p n := by
    refine qsum_const _ _ _ ?_
    intro c hc
    obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hc
    obtain ⟨t, ht, hlength⟩ := hall f hf
    rw [← hfc, ht, file_prefix_geo_weight_match, hlength]
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l = p * Qpow (1 - p) n
  rw [core_sum_map_fin_core, hconst, List.length_map, hlen]
  exact geo_slice_total p n

/-- ... so no smaller constant bounds the slice. -/
theorem file_geometric_prefix_slice_bound_sharp (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (K : Rat) :
    (∀ l : List FinProcInput, (l.map fin_core).Nodup →
      (∀ f, f ∈ l → ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
              ∧ t.length = n) →
      core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l ≤ K) →
    p * Qpow (1 - p) n ≤ K := by
  intro hbound
  obtain ⟨l, hnd, hall, hsum⟩ :=
    file_geometric_prefix_slice_bound_attained hdr p argv envp fs0 pth s Hp0 Hp1 n
  rw [← hsum]
  exact hbound l hnd hall

/-! ## The slice, stated on the FILE's length -/

/-- The counting lemma on CORES rather than records. The wider slice
statement below counts a FILTERED list of cores, which has no record list
behind it. -/
theorem file_prefix_core_list_length_bound (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (n : Nat) (cs : List FinCore) :
    cs.Nodup →
    (∀ c, c ∈ cs → ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) →
    cs.length ≤ 256 ^ n := by
  intro hnd hall
  have hsub : cs ⊆ (byte_lists n).map (file_prefix_core hdr argv envp fs0 pth s) := by
    intro c hc
    obtain ⟨t, ht, hlen⟩ := hall c hc
    refine List.mem_map.mpr ⟨t, ?_, ht.symm⟩
    rw [← hlen]
    exact byte_lists_complete t
  have hle := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_map] at hle
  rwa [byte_lists_length] at hle

/-- A record whose core is the shifted template at `t` and whose file has
length `hdr.length + n` has a payload of length `n`. -/
theorem file_prefix_payload_length (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (f : FinProcInput) (t : List byte)
    (n : Nat) :
    fin_core f = file_prefix_core hdr argv envp fs0 pth s t →
    (fs_file pth f.fin_image_fs).length = hdr.length + n →
    t.length = n := by
  intro hf hlen
  have h : (fs_file pth f.fin_image_fs).length = (hdr ++ t).length := by
    rw [← fs_file_file_prefix_core hdr argv envp fs0 pth s t, ← hf]
    rfl
  rw [hlen, List.length_append] at h
  omega

/-- The wider slice statement, in the whole-file family's shape: every record
matches the environment and carries a FILE of length `hdr.length + n`, with no
premise that the file starts with the header. A core whose file has the right
length but the wrong header weighs zero, so filtering it out changes
nothing. -/
theorem file_geometric_prefix_slice_bound_by_file_length (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l →
      fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs)
      ∧ (fs_file pth f.fin_image_fs).length = hdr.length + n) →
    core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ p * Qpow (1 - p) n := by
  intro hnd hall
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core,
    qsum_filter (file_prefix_geo_weight hdr p argv envp fs0 pth s)
      (matches_file_prefix_env hdr argv envp fs0 pth s) (l.map fin_core)
      (fun c hc => file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c hc)]
  have hslice : ∀ c,
      c ∈ (l.map fin_core).filter (matches_file_prefix_env hdr argv envp fs0 pth s) →
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n := by
    intro c hc
    rw [List.mem_filter] at hc
    obtain ⟨hin, hm⟩ := hc
    obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hin
    obtain ⟨t, ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s c hm
    refine ⟨t, ht, ?_⟩
    exact file_prefix_payload_length hdr argv envp fs0 pth s f t n
      (by rw [hfc]; exact ht) (hall f hf).2
  have hconst : qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
      ((l.map fin_core).filter (matches_file_prefix_env hdr argv envp fs0 pth s))
      = Qnat ((l.map fin_core).filter
          (matches_file_prefix_env hdr argv envp fs0 pth s)).length * geo_point p n := by
    refine qsum_const _ _ _ ?_
    intro c hc
    obtain ⟨t, ht, hlen⟩ := hslice c hc
    rw [ht, file_prefix_geo_weight_match, hlen]
  rw [hconst, ← geo_slice_total p n]
  exact Rat.mul_le_mul_of_nonneg_right
    (Qnat_le _ _ (file_prefix_core_list_length_bound hdr argv envp fs0 pth s n _
      (List.Pairwise.filter _ hnd) hslice))
    (geo_point_nonneg p n Hp0 Hp1)

/-! ## The lower certificate -/

/-- The witness family: one record per payload shorter than `k`, behind the
header. `short_inputs` is reused; only the embedding is this family's. -/
def file_prefix_geo_lower_witness (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (k : Nat) : List FinProcInput :=
  (short_inputs k).map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))

/-- Its cores are the short payloads behind the header. -/
theorem map_fin_core_file_prefix_geo_lower_witness (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (k : Nat) :
    (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k).map fin_core
      = (short_inputs k).map (file_prefix_core hdr argv envp fs0 pth s) := by
  unfold file_prefix_geo_lower_witness
  rw [List.map_map]
  exact List.map_congr_left (fun t _ => fin_core_core_input _)

/-- The witness family is admissible: its cores are duplicate-free. -/
theorem file_prefix_geo_lower_witness_nodup (hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (k : Nat) :
    ((file_prefix_geo_lower_witness hdr argv envp fs0 pth s k).map fin_core).Nodup := by
  rw [map_fin_core_file_prefix_geo_lower_witness]
  exact NoDup_map_inj _ _
    (fun x y _ _ h => file_prefix_core_inj hdr argv envp fs0 pth s x y h)
    (short_inputs_nodup k)

/-- Its weight is the geometric partial sum over payload lengths. -/
theorem qsum_file_prefix_short_inputs (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (k : Nat) :
    qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
        ((short_inputs k).map (file_prefix_core hdr argv envp fs0 pth s))
      = geo_prefix_sum p k := by
  rw [qsum_file_prefix_block]
  exact short_inputs_sum p k

/-- The witness family, with what it weighs in closed form. -/
theorem file_geometric_prefix_mass_lower_witness (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ((file_prefix_geo_lower_witness hdr argv envp fs0 pth s k).map fin_core).Nodup
    ∧ core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1))
        (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k)
        = 1 - Qpow (1 - p) k := by
  refine ⟨file_prefix_geo_lower_witness_nodup hdr argv envp fs0 pth s k, ?_⟩
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
      (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k) = 1 - Qpow (1 - p) k
  rw [core_sum_map_fin_core, map_fin_core_file_prefix_geo_lower_witness,
    qsum_file_prefix_short_inputs, geo_prefix_sum_closed]

/-- ... stated as the existence of an admissible list at each horizon. -/
theorem file_geometric_prefix_mass_lower_prefix (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
          = 1 - Qpow (1 - p) k :=
  ⟨file_prefix_geo_lower_witness hdr argv envp fs0 pth s k,
    file_geometric_prefix_mass_lower_witness hdr p argv envp fs0 pth s Hp0 Hp1 k⟩

/-- The lower certificate, with `0 < p` spent in `geo_gap_small` and nowhere
else, exactly as for the whole-file family. -/
theorem file_geometric_prefix_mass_lower_certificate (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat) :
    0 < p → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) - eps
          ≤ core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l := by
  intro hpos heps
  obtain ⟨k, hk⟩ := geo_gap_small p eps hpos Hp1 heps
  obtain ⟨l, hnd, hsum⟩ :=
    file_geometric_prefix_mass_lower_prefix hdr p argv envp fs0 pth s Hp0 Hp1 k
  refine ⟨l, hnd, ?_⟩
  rw [hsum]
  show (1 : Rat) - eps ≤ 1 - Qpow (1 - p) k
  grind

/-! ## ... and this mass is a supremum and not a maximum -/

/-- A list confined to files of length at most `hdr.length + n` — payloads of
length at most `n` — weighs at most the partial sum at that horizon. The
hypothesis is on the FILE's length, which is what a task has. -/
theorem file_geometric_prefix_bound_by_max_length (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → (fs_file pth f.fin_image_fs).length ≤ hdr.length + n) →
    core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ 1 - Qpow (1 - p) (n + 1) := by
  intro hnd hlen
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l
    ≤ 1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core,
    qsum_filter (file_prefix_geo_weight hdr p argv envp fs0 pth s)
      (matches_file_prefix_env hdr argv envp fs0 pth s) (l.map fin_core)
      (fun c hc => file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c hc)]
  have hincl : (l.map fin_core).filter (matches_file_prefix_env hdr argv envp fs0 pth s)
      ⊆ (short_inputs (n + 1)).map (file_prefix_core hdr argv envp fs0 pth s) := by
    intro c hc
    rw [List.mem_filter] at hc
    obtain ⟨hin, hm⟩ := hc
    obtain ⟨f, hf, hfc⟩ := List.mem_map.mp hin
    obtain ⟨t, ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s c hm
    refine List.mem_map.mpr ⟨t, ?_, ht.symm⟩
    apply short_inputs_complete
    have hle := hlen f hf
    have hc' : (fs_file pth f.fin_image_fs).length = (hdr ++ t).length := by
      rw [← fs_file_file_prefix_core hdr argv envp fs0 pth s t, ← ht, ← hfc]
      rfl
    rw [List.length_append] at hc'
    omega
  refine Rat.le_trans (qsum_core_incl_le _ _ _
    (file_prefix_geo_weight_nonneg hdr p argv envp fs0 pth s Hp0 Hp1)
    (List.Pairwise.filter _ hnd) hincl) ?_
  rw [qsum_file_prefix_short_inputs, geo_prefix_sum_closed]
  exact Rat.le_refl

/-- The horizon bound is reached by the witness family at that horizon. -/
theorem file_geometric_prefix_bound_by_max_length_attained (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    (∀ f, f ∈ file_prefix_geo_lower_witness hdr argv envp fs0 pth s (n + 1) →
      (fs_file pth f.fin_image_fs).length ≤ hdr.length + n)
    ∧ core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1))
        (file_prefix_geo_lower_witness hdr argv envp fs0 pth s (n + 1))
        = 1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (file_geometric_prefix_mass_lower_witness hdr p argv envp fs0 pth s
    Hp0 Hp1 (n + 1)).2⟩
  intro f hf
  unfold file_prefix_geo_lower_witness at hf
  obtain ⟨t, hin, hft⟩ := List.mem_map.mp hf
  rw [← hft]
  show (fs_file pth (file_prefix_core hdr argv envp fs0 pth s t).core_fs).length
    ≤ hdr.length + n
  rw [fs_file_file_prefix_core, List.length_append]
  have := short_inputs_In_length (n + 1) t hin
  omega

/-- No admissible list reaches the declared mass while `p < 1`. -/
theorem file_geometric_prefix_mass_not_attained (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
        < cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) := by
  intro hlt l hnd
  have hmax : ∀ f, f ∈ l →
      (fs_file pth f.fin_image_fs).length
        ≤ hdr.length + cores_file_depth pth (l.map fin_core) := by
    intro f hf
    have hge := cores_file_depth_ge pth (l.map fin_core) (fin_core f)
      (List.mem_map.mpr ⟨f, hf, rfl⟩)
    have hfs : (fin_core f).core_fs = f.fin_image_fs := rfl
    rw [hfs] at hge
    omega
  have hb : core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l
      ≤ 1 - Qpow (1 - p) (cores_file_depth pth (l.map fin_core) + 1) :=
    file_geometric_prefix_bound_by_max_length hdr p argv envp fs0 pth s Hp0 Hp1
      (cores_file_depth pth (l.map fin_core)) l hnd hmax
  have hpos : 0 < Qpow (1 - p) (cores_file_depth pth (l.map fin_core) + 1) :=
    Qpow_pos (1 - p) _ (by grind)
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l < (1 : Rat)
  grind

/-- The mass is a supremum and not a maximum. -/
theorem file_geometric_prefix_mass_supremum_not_maximum (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      ¬ (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
          = cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) := by
  intro hlt l hnd heq
  have hne := file_geometric_prefix_mass_not_attained hdr p argv envp fs0 pth s Hp0 Hp1 hlt l hnd
  rw [heq] at hne
  exact Rat.lt_irrefl hne

/-! ## Non-vacuity: the header bites, and the payload carries mass -/

/-- A core whose argv misses the fixed one weighs zero. -/
theorem file_prefix_geo_weight_off_environment_zero (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    c.core_argv ≠ argv → file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  intro hne
  refine file_prefix_geo_weight_mismatch hdr p argv envp fs0 pth s c ?_
  intro heq
  exact hne (congrArg FinCore.core_argv heq)

/-- The header bites, in general: a core whose file does not start with the
header weighs zero, and the declared mass is still `1`. The second conjunct
is what makes the first a statement about a normalised family. -/
theorem file_geometric_prefix_off_header_zero (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore) :
    (∀ t, fs_file pth c.core_fs ≠ hdr ++ t) →
    cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c = 0
    ∧ cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) = 1 := by
  intro hno
  refine ⟨?_, rfl⟩
  show file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0
  exact file_prefix_geo_weight_off_header_zero hdr p argv envp fs0 pth s c hno

/-- A one-byte header. -/
def file_example_hdr : List byte := [Z_to_bv 8 104]

/-- The core over the empty environment whose file is exactly that header.
`file_example_core`'s file is empty, so it does NOT start with the header. -/
def file_example_hdr_core : FinCore :=
  file_core [] [] [] file_example_path [] file_example_hdr

/-- The header bites, exhibited on cores the whole-file family treats alike.
The empty-file core weighs ZERO here, the exact-header core weighs
positively, the declared mass is `1`, and the whole-file family's positive
weight on the first core stands beside it, so the difference is visibly the
header and nothing else. -/
theorem file_geometric_prefix_header_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p →
    cd_weight (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1) file_example_core = 0
    ∧ 0 < cd_weight (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1) file_example_hdr_core
    ∧ cd_mass (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1) = 1
    ∧ 0 < cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
        file_example_core := by
  intro hlt
  refine ⟨?_, ?_, rfl, (file_geometric_fs_bites p Hp0 Hp1 hlt).2⟩
  · show file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
      file_example_core = 0
    refine file_prefix_geo_weight_off_header _ _ _ _ _ _ _ _ ?_
    rw [show fs_file file_example_path file_example_core.core_fs = []
      from fs_file_file_core [] [] [] file_example_path [] []]
    rfl
  · show 0 < file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
      file_example_hdr_core
    have hc : file_example_hdr_core
        = file_prefix_core file_example_hdr [] [] [] file_example_path [] [] := rfl
    rw [hc, file_prefix_geo_weight_match]
    have h1 : geo_point p ([] : List byte).length = p := by
      rw [geo_point_closed_form, List.length_nil, Qpow_0, Qpow_0]
      grind
    rw [h1]
    exact hlt

/-- ... and the family is not a constant either: positive on the exact-header
core, zero off the fixed argv. -/
theorem file_geometric_prefix_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p →
    0 < cd_weight (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1) file_example_hdr_core
    ∧ cd_weight (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1) geo_example_other = 0 := by
  intro hlt
  refine ⟨(file_geometric_prefix_header_bites p Hp0 Hp1 hlt).2.1, ?_⟩
  show file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
    geo_example_other = 0
  refine file_prefix_geo_weight_off_environment_zero _ _ _ _ _ _ _ _ ?_
  show ([[Z_to_bv 8 65]] : List (List byte)) ≠ []
  simp

/-! ## Non-vacuity: the mass is reached at `p_stop = 1`, and `Nodup` is
load-bearing -/

/-- The member at `p_stop = 1`: the point mass on the exact-header file. -/
def file_prefix_point_cd : CoreDistribution :=
  file_geometric_prefix file_example_hdr 1 [] [] [] file_example_path [] Qle_0_1 Rat.le_refl

/-- The record carrying that core. -/
def file_hdr_input : FinProcInput := core_input file_example_hdr_core

/-- One record reaches the declared mass at `p_stop = 1`. The closing step
compares closed `Rat` terms, so `decide +kernel` has the kernel evaluate the
comparison. -/
theorem file_prefix_point_cd_mass_attained :
    ([file_hdr_input].map fin_core).Nodup
    ∧ core_sum (cd_weight file_prefix_point_cd) [file_hdr_input]
        = cd_mass file_prefix_point_cd := by
  refine ⟨by simp, ?_⟩
  have hfc : fin_core file_hdr_input = file_example_hdr_core := fin_core_core_input _
  have hc : file_example_hdr_core
      = file_prefix_core file_example_hdr [] [] [] file_example_path [] [] := rfl
  show file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
      (fin_core file_hdr_input) + 0 = 1
  rw [hfc, hc, file_prefix_geo_weight_match, geo_point_closed_form, List.length_nil,
    Qpow_0, Qpow_0]
  grind

/-- Duplicate-freedom is load-bearing in `file_geometric_prefix_bound`: the
same record twice is in the cylinder and breaks the bound. -/
theorem file_geometric_prefix_bound_needs_nodup :
    ¬ ([file_hdr_input, file_hdr_input].map fin_core).Nodup
    ∧ (∀ f, f ∈ [file_hdr_input, file_hdr_input] →
        in_file_prefix_cylinder file_example_hdr [] [] [] file_example_path [] []
          (fin_core f))
    ∧ ¬ (core_sum (cd_weight file_prefix_point_cd) [file_hdr_input, file_hdr_input]
          ≤ file_geometric_prefix_cylinder_mass 1 []) := by
  have hfc : fin_core file_hdr_input = file_example_hdr_core := fin_core_core_input _
  have hc : file_example_hdr_core
      = file_prefix_core file_example_hdr [] [] [] file_example_path [] [] := rfl
  have hw : file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
      (fin_core file_hdr_input) = 1 := by
    rw [hfc, hc, file_prefix_geo_weight_match, geo_point_closed_form, List.length_nil,
      Qpow_0, Qpow_0]
    grind
  refine ⟨by simp, ?_, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨[], by rw [hfc]; exact hc⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨[], by rw [hfc]; exact hc⟩
      · exact absurd hf (by simp)
  · have hm : file_geometric_prefix_cylinder_mass 1 ([] : List byte) = 1 := by
      show file_geometric_cylinder_mass 1 ([] : List byte) = 1
      rw [file_geometric_cylinder_mass_closed_form]
      simp only [List.length_nil, Qpow_0]
      grind
    show ¬ (file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
        (fin_core file_hdr_input)
      + (file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
        (fin_core file_hdr_input) + 0)
      ≤ file_geometric_prefix_cylinder_mass 1 [])
    rw [hw, hm]
    exact (by decide +kernel : ¬ ((1 : Rat) + (1 + 0) ≤ 1))

/-! ## The two degenerate endpoints -/

/-- At `p_stop = 0` the weight vanishes identically. -/
theorem file_prefix_geo_weight_zero_at_zero_p (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    file_prefix_geo_weight hdr 0 argv envp fs0 pth s c = 0 := by
  unfold file_prefix_geo_weight
  split
  · split
    · rw [geo_point_closed_form]
      grind
    · rfl
  · rfl

/-- So the lower certificate needs `0 < p_stop`: at zero every admissible
list weighs nothing while the declared mass stays `1`. -/
theorem file_geometric_prefix_mass_lower_needs_positive (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    (∀ l : List FinProcInput,
      core_sum (cd_weight (file_geometric_prefix hdr 0 argv envp fs0 pth s
        Rat.le_refl Qle_0_1)) l = 0)
    ∧ ¬ (cd_mass (file_geometric_prefix hdr 0 argv envp fs0 pth s Rat.le_refl Qle_0_1)
          - (1 / 2) ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    refine core_sum_zero_weight _ l ?_
    intro c
    exact file_prefix_geo_weight_zero_at_zero_p hdr argv envp fs0 pth s c
  · show ¬ ((1 : Rat) - (1 / 2) ≤ 0)
    decide +kernel

/-- At `p_stop = 1` every core whose file is not EXACTLY the header weighs
zero: a longer payload by the geometric collapse, a file missing the header
by the header's own bite. -/
theorem file_prefix_geo_weight_collapses_at_one_p (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    fs_file pth c.core_fs ≠ hdr →
    file_prefix_geo_weight hdr 1 argv envp fs0 pth s c = 0 := by
  intro hne
  cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
  | none => exact file_prefix_geo_weight_off_header hdr 1 argv envp fs0 pth s c hs
  | some t =>
    have ht := strip_prefix_Some hdr (fs_file pth c.core_fs) t hs
    cases t with
    | nil => exact absurd (by rw [ht, List.append_nil]) hne
    | cons b t =>
      by_cases hmatch : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
      · have hc : c = file_prefix_core hdr argv envp fs0 pth s (b :: t) := by
          unfold file_prefix_core
          rw [← ht]
          exact hmatch
        rw [hc, file_prefix_geo_weight_match, geo_point_closed_form,
          show (b :: t).length = t.length + 1 from rfl, Qpow_succ]
        grind
      · exact file_prefix_geo_weight_mismatch hdr 1 argv envp fs0 pth s c hmatch

/-- The family goes blind to the payload at `p_stop = 1` without going
quiet, which is the failure mode that would go unnoticed. -/
theorem file_geometric_prefix_needs_p_below_one (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    fs_file pth c.core_fs ≠ hdr →
    cd_weight (file_geometric_prefix hdr 1 argv envp fs0 pth s Qle_0_1 Rat.le_refl) c = 0 := by
  intro hne
  show file_prefix_geo_weight hdr 1 argv envp fs0 pth s c = 0
  exact file_prefix_geo_weight_collapses_at_one_p hdr argv envp fs0 pth s c hne

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
