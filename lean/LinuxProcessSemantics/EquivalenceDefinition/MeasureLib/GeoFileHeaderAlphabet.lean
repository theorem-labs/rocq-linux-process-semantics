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

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-!

# EquivalenceDefinition.MeasureLib.GeoFileHeaderAlphabet — geometric file contents behind a fixed header, over an alphabet

This file holds Rocq `theories/EquivalenceDefinition/MeasureLib.v:10456-11450`,
the combinator that spreads a file's payload behind a fixed header over a
fixed alphabet of bytes rather than over all 256 of them: the weight, the
distribution, the cylinder and slice bounds, the lower certificate, the
proof that the declared mass is a supremum and not a maximum, the examples
that show the alphabet bites, and the two degenerate endpoints at
`p = 0` and `p = 1`.

Rocq `Q` is Lean `Rat`, whose values are reduced, so every statement Rocq
makes over `Qeq` is made here over `=`.  All 59 declarations of the span
are ported; none is left unported.
-/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## The weight -/

/-- `file_prefix_geo_weight` with one more test on the payload — every
byte in the alphabet — and the alphabet's ratio in place of `1 / 256`.
A matching core whose file is `hdr ++ t` with `t` over the alphabet
weighs `p * ((1 - p) * alpha_ratio) ^ t.length`; a payload with a byte
outside the alphabet weighs zero, as does a file that misses the header
or a core off the environment. -/
def file_prefix_over_geo_weight (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (c : FinCore) : Rat :=
  if c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) then
    match strip_prefix hdr (fs_file pth c.core_fs) with
    | some t => if alpha_only alpha t = true then alpha_geo_point alpha p t.length else 0
    | none => 0
  else 0

/-- At a payload over the alphabet the weight is the alphabet-geometric
weight of that payload's length. -/
theorem file_prefix_over_geo_weight_match (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s t : List byte) :
    alpha_only alpha t = true →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
      (file_prefix_core hdr argv envp fs0 pth s t)
      = alpha_geo_point alpha p t.length := by
  intro Ha
  have Hc : file_prefix_core hdr argv envp fs0 pth s t
      = file_core argv envp fs0 pth s (hdr ++ t) := rfl
  unfold file_prefix_over_geo_weight
  rw [fs_file_file_prefix_core, ite_eq_left Hc, strip_prefix_app]
  exact ite_eq_left Ha

/-- Zero on a payload outside the alphabet — the rule this family adds. -/
theorem file_prefix_over_geo_weight_off_alphabet (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s t : List byte) :
    alpha_only alpha t = false →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
      (file_prefix_core hdr argv envp fs0 pth s t) = 0 := by
  intro Ha
  have Hc : file_prefix_core hdr argv envp fs0 pth s t
      = file_core argv envp fs0 pth s (hdr ++ t) := rfl
  unfold file_prefix_over_geo_weight
  rw [fs_file_file_prefix_core, ite_eq_left Hc, strip_prefix_app]
  exact ite_eq_right (by rw [Ha]; exact Bool.false_ne_true)

/-- A core that is not the environment's own core at its file contents
weighs zero. -/
theorem file_prefix_over_geo_weight_mismatch (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs) →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  intro Hne
  unfold file_prefix_over_geo_weight
  exact ite_eq_right Hne

/-- A file that the header cannot be stripped from weighs zero. -/
theorem file_prefix_over_geo_weight_off_header (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    strip_prefix hdr (fs_file pth c.core_fs) = none →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  intro Hn
  unfold file_prefix_over_geo_weight
  rw [Hn]
  split <;> rfl

/-- The same, stated as "the file is no extension of the header". -/
theorem file_prefix_over_geo_weight_off_header_zero (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    (∀ t, fs_file pth c.core_fs ≠ hdr ++ t) →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  intro Hno
  exact file_prefix_over_geo_weight_off_header alpha hdr p argv envp fs0 pth s c
    (strip_prefix_None_of_no_extension hdr (fs_file pth c.core_fs) Hno)

/-- Every value of the weight is nonnegative. -/
theorem file_prefix_over_geo_weight_nonneg (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    0 ≤ p → p ≤ 1 →
    ∀ c, 0 ≤ file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c := by
  intro Hp0 Hp1 c
  unfold file_prefix_over_geo_weight
  split
  · split
    · split
      · exact alpha_geo_point_nonneg alpha p _ Hp0 Hp1
      · exact Rat.le_refl
    · exact Rat.le_refl
  · exact Rat.le_refl

/-- The weight is at most the alphabet-geometric weight of the payload at
every payload, alphabet or not: the `≤` form of the block identity, which
needs no hypothesis on the payloads enumerated. -/
theorem file_prefix_over_geo_weight_le_point (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s t : List byte) :
    0 ≤ p → p ≤ 1 →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
      (file_prefix_core hdr argv envp fs0 pth s t)
      ≤ alpha_geo_point alpha p t.length := by
  intro Hp0 Hp1
  cases Ha : alpha_only alpha t with
  | true =>
    rw [file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t Ha]
    exact Rat.le_refl
  | false =>
    rw [file_prefix_over_geo_weight_off_alphabet alpha hdr p argv envp fs0 pth s t Ha]
    exact alpha_geo_point_nonneg alpha p t.length Hp0 Hp1

/-- The distribution.  The alphabet's duplicate-freedom and non-emptiness
are constructor arguments, as the side conditions on `p` are: the
constructor itself needs neither, but every certificate below does. -/
def file_geometric_prefix_over (alpha : List byte) (_Hnd : alpha.Nodup) (_Hne : alpha ≠ [])
    (hdr : List byte) (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  CoreDistribution.mkCoreDistribution
    (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) 1
    (file_prefix_over_geo_weight_nonneg alpha hdr p argv envp fs0 pth s Hp0 Hp1)

/-! ## The full alphabet: `file_geometric_prefix`, pointwise -/

/-- Over all the bytes the weight is the 256-byte header weight. -/
theorem file_prefix_over_geo_weight_all_bytes (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    file_prefix_over_geo_weight all_bytes hdr p argv envp fs0 pth s c
      = file_prefix_geo_weight hdr p argv envp fs0 pth s c := by
  unfold file_prefix_over_geo_weight file_prefix_geo_weight
  cases Hs : strip_prefix hdr (fs_file pth c.core_fs) with
  | none => rfl
  | some t => simp only [alpha_only_all_bytes, ite_true, alpha_geo_point_all_bytes]

/-- The distribution over all the bytes weighs every core as
`file_geometric_prefix` does. -/
theorem file_geometric_prefix_over_all_bytes_pointwise (Hnd : all_bytes.Nodup)
    (Hne : all_bytes ≠ []) (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (c : FinCore) :
    cd_weight (file_geometric_prefix_over all_bytes Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1) c
      = cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c :=
  file_prefix_over_geo_weight_all_bytes hdr p argv envp fs0 pth s c

/-- ... and declares the same mass. -/
theorem file_geometric_prefix_over_all_bytes_mass (Hnd : all_bytes.Nodup)
    (Hne : all_bytes ≠ []) (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    cd_mass (file_geometric_prefix_over all_bytes Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1)
      = cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) := rfl

/-! ## The block identity, over the alphabet -/

/-- A block of payloads all over the alphabet sums to the sum of their
alphabet-geometric weights. -/
theorem qsum_file_prefix_over_block (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (B : List (List byte)) :
    (∀ t ∈ B, alpha_only alpha t = true) →
    qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (B.map (file_prefix_core hdr argv envp fs0 pth s))
      = qsum (fun t => alpha_geo_point alpha p t.length) B := by
  intro HB
  rw [qsum_map]
  refine qsum_ext _ _ B ?_
  intro t Ht
  exact file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t (HB t Ht)

/-- The `≤` form, with no hypothesis on the payloads enumerated. -/
theorem qsum_file_prefix_over_block_le (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (B : List (List byte)) :
    0 ≤ p → p ≤ 1 →
    qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (B.map (file_prefix_core hdr argv envp fs0 pth s))
      ≤ qsum (fun t => alpha_geo_point alpha p t.length) B := by
  intro Hp0 Hp1
  rw [qsum_map]
  refine qsum_mono _ _ B ?_
  intro t _
  exact file_prefix_over_geo_weight_le_point alpha hdr p argv envp fs0 pth s t Hp0 Hp1

/-! ## The payload cylinder, and the enumeration that bounds it -/

/-- The membership test of the cylinder, carrying the alphabet for the
filter: the environment's header test, and a payload over the alphabet. -/
def matches_file_prefix_over_env (alpha hdr : List byte) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) : Bool :=
  matches_file_prefix_env hdr argv envp fs0 pth s c
  && (match strip_prefix hdr (fs_file pth c.core_fs) with
      | some t => alpha_only alpha t
      | none => false)

/-- A core the test rejects weighs zero. -/
theorem file_prefix_over_geo_weight_unmatched (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    matches_file_prefix_over_env alpha hdr argv envp fs0 pth s c = false →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  intro H
  unfold matches_file_prefix_over_env at H
  rcases Bool.and_eq_false_iff.mp H with H | H
  · rcases matches_file_prefix_env_false hdr argv envp fs0 pth s c H with Hne | Hn
    · exact file_prefix_over_geo_weight_mismatch alpha hdr p argv envp fs0 pth s c Hne
    · exact file_prefix_over_geo_weight_off_header alpha hdr p argv envp fs0 pth s c Hn
  · by_cases Hc : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
    · cases Hs : strip_prefix hdr (fs_file pth c.core_fs) with
      | none => exact file_prefix_over_geo_weight_off_header alpha hdr p argv envp fs0 pth s c Hs
      | some t =>
        have H' : alpha_only alpha t = false := by rw [Hs] at H; exact H
        have HS := strip_prefix_Some hdr (fs_file pth c.core_fs) t Hs
        have Hceq : c = file_prefix_core hdr argv envp fs0 pth s t :=
          Hc.trans (by rw [HS]; rfl)
        rw [Hceq]
        exact file_prefix_over_geo_weight_off_alphabet alpha hdr p argv envp fs0 pth s t H'
    · exact file_prefix_over_geo_weight_mismatch alpha hdr p argv envp fs0 pth s c Hc

/-- A core the test accepts is a header core with a payload over the
alphabet. -/
theorem matches_file_prefix_over_env_true (alpha hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    matches_file_prefix_over_env alpha hdr argv envp fs0 pth s c = true →
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ alpha_only alpha t = true := by
  intro H
  unfold matches_file_prefix_over_env at H
  obtain ⟨Henv, Ha⟩ := Bool.and_eq_true_iff.mp H
  obtain ⟨t, Ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s c Henv
  refine ⟨t, Ht, ?_⟩
  rw [Ht, fs_file_file_prefix_core, strip_prefix_app] at Ha
  exact Ha

/-- The bound over cores.  The list is first filtered to the cores that
weigh anything; the survivors are payloads over the alphabet extending
`bs`, which `alpha_cyl` enumerates, and the enumeration is bounded by the
`≤` block identity and `alpha_cyl_sum_le`.  No hypothesis on `bs`: a
prefix that leaves the alphabet gives an empty filter. -/
theorem file_prefix_over_geo_weight_cylinder_bound (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    alpha ≠ [] → 0 ≤ p → p ≤ 1 →
    ∀ (bs : List byte) (cs : List FinCore),
      cs.Nodup →
      (∀ c ∈ cs, in_file_prefix_cylinder hdr argv envp fs0 pth s bs c) →
      qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) cs
        ≤ alpha_geo_mass alpha p bs.length := by
  intro Hne Hp0 Hp1 bs cs Hnd Hcyl
  rw [qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
    (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) cs
    (fun c hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c hc)]
  refine Rat.le_trans
    (qsum_core_incl_le _ _
      ((alpha_cyl alpha bs (cores_file_prefix_depth hdr pth cs)).map
        (file_prefix_core hdr argv envp fs0 pth s))
      (file_prefix_over_geo_weight_nonneg alpha hdr p argv envp fs0 pth s Hp0 Hp1)
      (List.Nodup.sublist List.filter_sublist Hnd) ?_)
    (Rat.le_trans
      (qsum_file_prefix_over_block_le alpha hdr p argv envp fs0 pth s _ Hp0 Hp1)
      (alpha_cyl_sum_le alpha p Hne Hp0 Hp1 _ bs))
  intro c Hc
  rw [List.mem_filter] at Hc
  obtain ⟨Hin, Hm⟩ := Hc
  obtain ⟨ext, Hext⟩ := Hcyl c Hin
  obtain ⟨t, Ht, Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
  have Hteq : t = bs ++ ext :=
    file_prefix_core_inj hdr argv envp fs0 pth s t (bs ++ ext) (by rw [← Ht, ← Hext])
  subst Hteq
  rw [alpha_only_app] at Ha
  obtain ⟨_, Hae⟩ := Bool.and_eq_true_iff.mp Ha
  have Hd : (bs ++ ext).length ≤ cores_file_prefix_depth hdr pth cs :=
    cores_file_prefix_depth_ge hdr pth cs c (bs ++ ext) Hin
      (by rw [Hext, fs_file_file_prefix_core])
  rw [List.length_append] at Hd
  rw [Hext]
  exact List.mem_map_of_mem (alpha_cyl_In alpha _ bs ext Hae (by omega))

/-! ## The exports -/

/-- The mass a payload cylinder of depth `bs.length` carries. -/
def file_geometric_prefix_over_cylinder_mass (alpha : List byte) (p : Rat)
    (bs : List byte) : Rat :=
  alpha_geo_mass alpha p bs.length

/-- Its closed form: the stop-complement power times the ratio power. -/
theorem file_geometric_prefix_over_cylinder_mass_closed_form (alpha : List byte) (p : Rat)
    (bs : List byte) :
    file_geometric_prefix_over_cylinder_mass alpha p bs
      = Qpow (1 - p) bs.length * Qpow (alpha_ratio alpha) bs.length :=
  alpha_geo_mass_closed_form alpha p bs.length

/-- Over all the bytes it is the 256-byte cylinder mass. -/
theorem file_geometric_prefix_over_cylinder_mass_all_bytes (p : Rat) (bs : List byte) :
    file_geometric_prefix_over_cylinder_mass all_bytes p bs
      = file_geometric_prefix_cylinder_mass p bs := by
  unfold file_geometric_prefix_over_cylinder_mass
  rw [alpha_geo_mass_all_bytes]
  rfl

/-- Records whose cores lie in the cylinder weigh at most the cylinder's
mass. -/
theorem file_geometric_prefix_over_bound (alpha : List byte) (Hnd : alpha.Nodup)
    (Hne : alpha ≠ []) (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)) →
    core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1)) l
      ≤ file_geometric_prefix_over_cylinder_mass alpha p bs := by
  intro Hndl Hcyl
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core]
  refine file_prefix_over_geo_weight_cylinder_bound alpha hdr p argv envp fs0 pth s
    Hne Hp0 Hp1 bs _ Hndl ?_
  intro c Hc
  obtain ⟨f, Hin, Hf⟩ := List.mem_map.mp Hc
  exact Hf ▸ Hcyl f Hin

/-- The same bound when every record is either in the cylinder or off the
environment altogether. -/
theorem file_geometric_prefix_over_bound_or_off_environment (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)
      ∨ matches_file_prefix_over_env alpha hdr argv envp fs0 pth s (fin_core f) = false) →
    core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1)) l
      ≤ file_geometric_prefix_over_cylinder_mass alpha p bs := by
  intro Hndl Hor
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core,
    qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) (l.map fin_core)
      (fun c hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c hc)]
  refine file_prefix_over_geo_weight_cylinder_bound alpha hdr p argv envp fs0 pth s
    Hne Hp0 Hp1 bs _ (List.Nodup.sublist List.filter_sublist Hndl) ?_
  intro c Hc
  rw [List.mem_filter] at Hc
  obtain ⟨Hin, Hm⟩ := Hc
  obtain ⟨f, Hinl, Hf⟩ := List.mem_map.mp Hin
  rcases Hor f Hinl with Hcyl | Hoff
  · exact Hf ▸ Hcyl
  · rw [Hf] at Hoff
    rw [Hoff] at Hm
    exact absurd Hm Bool.false_ne_true

/-- Any duplicate-free list weighs at most the declared mass. -/
theorem file_geometric_prefix_over_mass_upper (alpha : List byte) (Hnd : alpha.Nodup)
    (Hne : alpha ≠ []) (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1)) l
      ≤ cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
          fs0 pth s Hp0 Hp1) := by
  intro Hndl
  have h1 : file_geometric_prefix_over_cylinder_mass alpha p [] = 1 := by
    unfold file_geometric_prefix_over_cylinder_mass alpha_geo_mass
    exact Qpow_0 _
  have hb := file_geometric_prefix_over_bound_or_off_environment alpha Hnd Hne hdr p argv envp
    fs0 pth s Hp0 Hp1 [] l Hndl ?_
  · rw [h1] at hb
    exact hb
  intro f _
  cases Hm : matches_file_prefix_over_env alpha hdr argv envp fs0 pth s (fin_core f) with
  | true =>
    obtain ⟨t, Ht, _⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s
      (fin_core f) Hm
    exact Or.inl ⟨t, Ht⟩
  | false => exact Or.inr rfl

/-! ## The counting lemma and the payload-length slice, over the alphabet -/

/-- A duplicate-free list of header cores all of payload length `n` over
the alphabet has at most `alpha.length ^ n` entries. -/
theorem file_prefix_over_core_list_length_bound (alpha hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (n : Nat) (cs : List FinCore) :
    cs.Nodup →
    (∀ c ∈ cs, ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t
      ∧ t.length = n ∧ alpha_only alpha t = true) →
    cs.length ≤ alpha.length ^ n := by
  intro Hnd Hall
  have Hle : cs.length
      ≤ ((alpha_lists alpha n).map (file_prefix_core hdr argv envp fs0 pth s)).length := by
    refine List.Nodup.length_le_of_subset Hnd ?_
    intro c Hc
    obtain ⟨t, Ht, Hlen, Ha⟩ := Hall c Hc
    refine List.mem_map.mpr ⟨t, ?_, Ht.symm⟩
    exact Hlen ▸ alpha_lists_complete alpha t Ha
  rw [List.length_map, alpha_lists_length] at Hle
  exact Hle

/-- The same count, for records read through their cores. -/
theorem injective_core_list_in_file_prefix_over_cylinder_length_bound
    (alpha hdr : List byte) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
      ∧ t.length = n ∧ alpha_only alpha t = true) →
    l.length ≤ alpha.length ^ n := by
  intro Hnd Hall
  have H := file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n
    (l.map fin_core) Hnd (by
      intro c Hc
      obtain ⟨f, Hin, Hf⟩ := List.mem_map.mp Hc
      obtain ⟨t, Ht⟩ := Hall f Hin
      exact ⟨t, Hf ▸ Ht⟩)
  rwa [List.length_map] at H

/-- And the count is attained: the whole alphabet slice is such a list. -/
theorem injective_core_list_in_file_prefix_over_cylinder_length_bound_attained
    (alpha hdr : List byte) :
    alpha.Nodup →
    ∀ (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
      (n : Nat),
      ∃ l : List FinProcInput,
        (l.map fin_core).Nodup
        ∧ (∀ f ∈ l, ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
            ∧ t.length = n ∧ alpha_only alpha t = true)
        ∧ l.length = alpha.length ^ n := by
  intro Hnd argv envp fs0 pth s n
  refine ⟨(alpha_lists alpha n).map
    (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t)), ?_, ?_, ?_⟩
  · rw [List.map_map]
    have Hc : (fin_core ∘ fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
        = file_prefix_core hdr argv envp fs0 pth s := by
      funext t
      exact fin_core_core_input _
    rw [Hc]
    exact NoDup_map_inj _ _
      (fun x y _ _ Heq => file_prefix_core_inj hdr argv envp fs0 pth s x y Heq)
      (alpha_lists_nodup alpha Hnd n)
  · intro f Hf
    obtain ⟨t, Hin, Hft⟩ := List.mem_map.mp Hf
    subst Hft
    exact ⟨t, fin_core_core_input _, alpha_lists_In_length alpha n t Hin,
      alpha_lists_In_alpha alpha n t Hin⟩
  · rw [List.length_map, alpha_lists_length]

/-- The payload-length slice, with no premise that the payloads are over
the alphabet: the ones that are not weigh zero and are filtered away, and
the survivors number at most `alpha.length ^ n`. -/
theorem file_geometric_prefix_over_slice_bound (alpha : List byte) (Hnd : alpha.Nodup)
    (Hne : alpha ≠ []) (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
      ∧ t.length = n) →
    core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1)) l
      ≤ p * Qpow (1 - p) n := by
  intro Hndl Hall
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core,
    qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) (l.map fin_core)
      (fun c hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c hc)]
  have Hslice : ∀ c ∈ (l.map fin_core).filter
      (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s),
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t
        ∧ t.length = n ∧ alpha_only alpha t = true := by
    intro c Hc
    rw [List.mem_filter] at Hc
    obtain ⟨Hin, Hm⟩ := Hc
    obtain ⟨f, Hinl, Hf⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht, Hlen⟩ := Hall f Hinl
    obtain ⟨t', Ht', Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
    have Hteq : t' = t :=
      file_prefix_core_inj hdr argv envp fs0 pth s t' t (by rw [← Ht', ← Hf]; exact Ht)
    subst Hteq
    exact ⟨t', Ht', Hlen, Ha⟩
  rw [qsum_const _ _ (alpha_geo_point alpha p n) (by
    intro c Hc
    obtain ⟨t, Ht, Hlen, Ha⟩ := Hslice c Hc
    rw [Ht, file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t Ha, Hlen])]
  rw [← alpha_slice_total alpha p n Hne]
  refine Rat.mul_le_mul_of_nonneg_right ?_ (alpha_geo_point_nonneg alpha p n Hp0 Hp1)
  refine Qnat_le _ _ ?_
  exact file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n _
    (List.Nodup.sublist List.filter_sublist Hndl) Hslice

/-- The same slice stated in the whole-file shape: environment matched and
file length `hdr.length + n`, with no premise on the header or the
alphabet. -/
theorem file_geometric_prefix_over_slice_bound_by_file_length (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs)
      ∧ (fs_file pth f.fin_image_fs).length = hdr.length + n) →
    core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1)) l
      ≤ p * Qpow (1 - p) n := by
  intro Hndl Hall
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core,
    qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) (l.map fin_core)
      (fun c hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c hc)]
  have Hslice : ∀ c ∈ (l.map fin_core).filter
      (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s),
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t
        ∧ t.length = n ∧ alpha_only alpha t = true := by
    intro c Hc
    rw [List.mem_filter] at Hc
    obtain ⟨Hin, Hm⟩ := Hc
    obtain ⟨f, Hinl, Hf⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht, Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
    refine ⟨t, Ht, ?_, Ha⟩
    exact file_prefix_payload_length hdr argv envp fs0 pth s f t n
      (by rw [Hf]; exact Ht) (Hall f Hinl).2
  rw [qsum_const _ _ (alpha_geo_point alpha p n) (by
    intro c Hc
    obtain ⟨t, Ht, Hlen, Ha⟩ := Hslice c Hc
    rw [Ht, file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t Ha, Hlen])]
  rw [← alpha_slice_total alpha p n Hne]
  refine Rat.mul_le_mul_of_nonneg_right ?_ (alpha_geo_point_nonneg alpha p n Hp0 Hp1)
  refine Qnat_le _ _ ?_
  exact file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n _
    (List.Nodup.sublist List.filter_sublist Hndl) Hslice

/-- The slice bound is attained. -/
theorem file_geometric_prefix_over_slice_bound_attained (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ (∀ f ∈ l, ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
          ∧ t.length = n)
      ∧ core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv
          envp fs0 pth s Hp0 Hp1)) l = p * Qpow (1 - p) n := by
  obtain ⟨l, Hndl, Hall, Hlen⟩ :=
    injective_core_list_in_file_prefix_over_cylinder_length_bound_attained alpha hdr Hnd
      argv envp fs0 pth s n
  refine ⟨l, Hndl, ?_, ?_⟩
  · intro f Hf
    obtain ⟨t, Ht, Hl, _⟩ := Hall f Hf
    exact ⟨t, Ht, Hl⟩
  · show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l = _
    rw [core_sum_map_fin_core]
    rw [qsum_const _ _ (alpha_geo_point alpha p n) (by
      intro c Hc
      obtain ⟨f, Hin, Hf⟩ := List.mem_map.mp Hc
      obtain ⟨t, Ht, Hlength, Ha⟩ := Hall f Hin
      rw [← Hf, Ht, file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t Ha,
        Hlength])]
    rw [List.length_map, Hlen]
    exact alpha_slice_total alpha p n Hne

/-- So no smaller bound holds for the slice. -/
theorem file_geometric_prefix_over_slice_bound_sharp (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (K : Rat) :
    (∀ l : List FinProcInput, (l.map fin_core).Nodup →
      (∀ f ∈ l, ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
        ∧ t.length = n) →
      core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv
        envp fs0 pth s Hp0 Hp1)) l ≤ K) →
    p * Qpow (1 - p) n ≤ K := by
  intro Hbound
  obtain ⟨l, Hndl, Hall, Hsum⟩ := file_geometric_prefix_over_slice_bound_attained alpha
    Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n
  rw [← Hsum]
  exact Hbound l Hndl Hall

/-! ## The lower certificate -/

/-- The witness family: every payload shorter than `k` over the alphabet,
wrapped as a record. -/
def file_prefix_over_geo_lower_witness (alpha hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (k : Nat) : List FinProcInput :=
  (alpha_short_inputs alpha k).map
    (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))

/-- Its cores are exactly the header cores of those payloads. -/
theorem map_fin_core_file_prefix_over_geo_lower_witness (alpha hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (k : Nat) :
    (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k).map fin_core
      = (alpha_short_inputs alpha k).map (file_prefix_core hdr argv envp fs0 pth s) := by
  unfold file_prefix_over_geo_lower_witness
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro t _
  exact fin_core_core_input _

/-- Those cores are duplicate-free. -/
theorem file_prefix_over_geo_lower_witness_nodup (alpha : List byte) :
    alpha.Nodup →
    ∀ (hdr : List byte) (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
      (s : List byte) (k : Nat),
      ((file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k).map
        fin_core).Nodup := by
  intro Hnd hdr argv envp fs0 pth s k
  rw [map_fin_core_file_prefix_over_geo_lower_witness]
  exact NoDup_map_inj _ _
    (fun x y _ _ Heq => file_prefix_core_inj hdr argv envp fs0 pth s x y Heq)
    (alpha_short_inputs_nodup alpha Hnd k)

/-- Their weights sum to the geometric prefix sum. -/
theorem qsum_file_prefix_over_short_inputs (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (k : Nat) :
    alpha ≠ [] →
    qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      ((alpha_short_inputs alpha k).map (file_prefix_core hdr argv envp fs0 pth s))
      = geo_prefix_sum p k := by
  intro Hne
  rw [qsum_file_prefix_over_block alpha hdr p argv envp fs0 pth s _
    (fun t Ht => alpha_short_inputs_In_alpha alpha k t Ht)]
  exact alpha_short_inputs_sum alpha p k Hne

/-- The witness is duplicate-free and weighs `1 - (1 - p) ^ k`. -/
theorem file_geometric_prefix_over_mass_lower_witness (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ((file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k).map fin_core).Nodup
    ∧ core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
        fs0 pth s Hp0 Hp1))
        (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k)
        = 1 - Qpow (1 - p) k := by
  refine ⟨file_prefix_over_geo_lower_witness_nodup alpha Hnd hdr argv envp fs0 pth s k, ?_⟩
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) _ = _
  rw [core_sum_map_fin_core, map_fin_core_file_prefix_over_geo_lower_witness,
    qsum_file_prefix_over_short_inputs alpha hdr p argv envp fs0 pth s k Hne]
  exact geo_prefix_sum_closed p k

/-- So every geometric prefix of the mass is reached by some list. -/
theorem file_geometric_prefix_over_mass_lower_prefix (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv
          envp fs0 pth s Hp0 Hp1)) l = 1 - Qpow (1 - p) k :=
  ⟨file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k,
    file_geometric_prefix_over_mass_lower_witness alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1 k⟩

/-- The lower certificate: for every positive slack some list comes within
it of the declared mass. -/
theorem file_geometric_prefix_over_mass_lower_certificate (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat) :
    0 < p → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1) - eps
        ≤ core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv
            envp fs0 pth s Hp0 Hp1)) l := by
  intro Hpos Heps
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hpos Hp1 Heps
  obtain ⟨l, Hndl, Hsum⟩ := file_geometric_prefix_over_mass_lower_prefix alpha Hnd Hne hdr p
    argv envp fs0 pth s Hp0 Hp1 k
  refine ⟨l, Hndl, ?_⟩
  rw [Hsum]
  show (1 : Rat) - eps ≤ 1 - Qpow (1 - p) k
  calc (1 : Rat) - eps = 1 + -eps := Rat.sub_eq_add_neg 1 eps
    _ ≤ 1 + -Qpow (1 - p) k := Rat.add_le_add_left.mpr (Rat.neg_le_neg Hk)
    _ = 1 - Qpow (1 - p) k := (Rat.sub_eq_add_neg 1 (Qpow (1 - p) k)).symm

/-! ## The mass is a supremum and not a maximum -/

/-- A list whose files are no longer than `hdr.length + n` weighs at most
`1 - (1 - p) ^ (n + 1)`. -/
theorem file_geometric_prefix_over_bound_by_max_length (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, (fs_file pth f.fin_image_fs).length ≤ hdr.length + n) →
    core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1)) l
      ≤ 1 - Qpow (1 - p) (n + 1) := by
  intro Hndl Hlen
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core,
    qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) (l.map fin_core)
      (fun c hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c hc)]
  refine Rat.le_trans
    (qsum_core_incl_le _ _
      ((alpha_short_inputs alpha (n + 1)).map (file_prefix_core hdr argv envp fs0 pth s))
      (file_prefix_over_geo_weight_nonneg alpha hdr p argv envp fs0 pth s Hp0 Hp1)
      (List.Nodup.sublist List.filter_sublist Hndl) ?_) ?_
  · intro c Hc
    rw [List.mem_filter] at Hc
    obtain ⟨Hin, Hm⟩ := Hc
    obtain ⟨f, Hinl, Hf⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht, Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
    refine List.mem_map.mpr ⟨t, ?_, Ht.symm⟩
    refine alpha_short_inputs_complete alpha (n + 1) t Ha ?_
    have Hle := Hlen f Hinl
    have Hc' : fs_file pth c.core_fs = hdr ++ t := by
      rw [Ht]; exact fs_file_file_prefix_core hdr argv envp fs0 pth s t
    rw [← Hf] at Hc'
    have Hc'' : fs_file pth f.fin_image_fs = hdr ++ t := Hc'
    rw [Hc'', List.length_append] at Hle
    omega
  · rw [qsum_file_prefix_over_short_inputs alpha hdr p argv envp fs0 pth s (n + 1) Hne,
      geo_prefix_sum_closed]
    exact Rat.le_refl

/-- That bound is attained by the witness family of depth `n + 1`. -/
theorem file_geometric_prefix_over_bound_by_max_length_attained (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    (∀ f ∈ file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s (n + 1),
      (fs_file pth f.fin_image_fs).length ≤ hdr.length + n)
    ∧ core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
        fs0 pth s Hp0 Hp1))
        (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s (n + 1))
        = 1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (file_geometric_prefix_over_mass_lower_witness alpha Hnd Hne hdr p argv envp
    fs0 pth s Hp0 Hp1 (n + 1)).2⟩
  intro f Hf
  unfold file_prefix_over_geo_lower_witness at Hf
  obtain ⟨t, Hin, Hft⟩ := List.mem_map.mp Hf
  subst Hft
  show (fs_file pth (file_prefix_core hdr argv envp fs0 pth s t).core_fs).length
    ≤ hdr.length + n
  rw [fs_file_file_prefix_core, List.length_append]
  have := alpha_short_inputs_In_length alpha (n + 1) t Hin
  omega

/-- Below `p = 1` no finite list reaches the declared mass. -/
theorem file_geometric_prefix_over_mass_not_attained (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput,
      (l.map fin_core).Nodup →
      core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
        fs0 pth s Hp0 Hp1)) l
        < cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
            Hp0 Hp1) := by
  intro Hlt l Hndl
  show _ < (1 : Rat)
  have Hle : core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1)) l
      ≤ 1 - Qpow (1 - p) (list_max (l.map (fun f => (fs_file pth f.fin_image_fs).length)) + 1) := by
    refine file_geometric_prefix_over_bound_by_max_length alpha Hnd Hne hdr p argv envp
      fs0 pth s Hp0 Hp1 _ l Hndl ?_
    intro f Hf
    have Hm : (fs_file pth f.fin_image_fs).length
        ∈ l.map (fun f => (fs_file pth f.fin_image_fs).length) := List.mem_map_of_mem Hf
    have Hb := list_max_ge _ _ Hm
    omega
  have Hpos : 0 < Qpow (1 - p)
      (list_max (l.map (fun f => (fs_file pth f.fin_image_fs).length)) + 1) :=
    Qpow_pos _ _ ((Rat.lt_iff_sub_pos p 1).mp Hlt)
  have Hlt2 : (1 : Rat)
      - Qpow (1 - p) (list_max (l.map (fun f => (fs_file pth f.fin_image_fs).length)) + 1)
      < 1 := by
    refine (Rat.lt_iff_sub_pos _ _).mpr ?_
    have Hid : (1 : Rat)
        - (1 - Qpow (1 - p)
            (list_max (l.map (fun f => (fs_file pth f.fin_image_fs).length)) + 1))
        = Qpow (1 - p)
            (list_max (l.map (fun f => (fs_file pth f.fin_image_fs).length)) + 1) := by
      grind
    rw [Hid]
    exact Hpos
  exact Rat.not_le.mp (fun Hge => Rat.not_le.mpr Hlt2 (Rat.le_trans Hge Hle))

/-- So the mass is a supremum and never an equality. -/
theorem file_geometric_prefix_over_mass_supremum_not_maximum (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput,
      (l.map fin_core).Nodup →
      ¬ (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
          fs0 pth s Hp0 Hp1)) l
          = cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
              Hp0 Hp1)) := by
  intro Hlt l Hndl
  exact Rat.ne_of_lt (file_geometric_prefix_over_mass_not_attained alpha Hnd Hne hdr p argv
    envp fs0 pth s Hp0 Hp1 Hlt l Hndl)

/-! ## Non-vacuity: the alphabet bites -/

/-- A core whose argv is not the environment's weighs zero. -/
theorem file_prefix_over_geo_weight_off_environment_zero (alpha hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    c.core_argv ≠ argv →
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  intro Hne
  refine file_prefix_over_geo_weight_mismatch alpha hdr p argv envp fs0 pth s c ?_
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- A file that misses the header weighs zero while the declared mass
stays `1`. -/
theorem file_geometric_prefix_over_off_header_zero (alpha : List byte) (Hnd : alpha.Nodup)
    (Hne : alpha ≠ []) (hdr : List byte) (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (c : FinCore) :
    (∀ t, fs_file pth c.core_fs ≠ hdr ++ t) →
    cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1) c = 0
    ∧ cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1) = 1 := by
  intro Hno
  exact ⟨file_prefix_over_geo_weight_off_header_zero alpha hdr p argv envp fs0 pth s c Hno,
    rfl⟩

/-- The alphabet bites in general: a payload with a byte outside the
alphabet weighs zero while the declared mass stays `1`. -/
theorem file_geometric_prefix_over_off_alphabet_zero (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte) (p : Rat)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (t : List byte) :
    alpha_only alpha t = false →
    cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1) (file_prefix_core hdr argv envp fs0 pth s t) = 0
    ∧ cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1) = 1 := by
  intro Ha
  exact ⟨file_prefix_over_geo_weight_off_alphabet alpha hdr p argv envp fs0 pth s t Ha, rfl⟩

/-- A one-byte alphabet. -/
def file_example_alpha : List byte := [Z_to_bv 8 65]

/-- It is duplicate-free. -/
theorem file_example_alpha_nodup : file_example_alpha.Nodup := by
  simp [file_example_alpha]

/-- It is not empty. -/
theorem file_example_alpha_ne : file_example_alpha ≠ [] := by
  simp [file_example_alpha]

/-- A payload in that alphabet, behind the one-byte example header. -/
def file_example_in_alpha_core : FinCore :=
  file_prefix_core file_example_hdr [] [] [] file_example_path [] [Z_to_bv 8 65]

/-- A payload outside that alphabet, behind the same header. -/
def file_example_off_alpha_core : FinCore :=
  file_prefix_core file_example_hdr [] [] [] file_example_path [] [Z_to_bv 8 66]

/-- The alphabet bites, exhibited: the off-alphabet core — which the
256-byte header family weighs positively — weighs zero, the in-alphabet
core weighs positively, and the declared mass is `1`. -/
theorem file_geometric_prefix_over_alphabet_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p → p < 1 →
    cd_weight (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
      file_example_alpha_ne file_example_hdr p [] [] [] file_example_path [] Hp0 Hp1)
      file_example_off_alpha_core = 0
    ∧ 0 < cd_weight (file_geometric_prefix_over file_example_alpha
        file_example_alpha_nodup file_example_alpha_ne file_example_hdr p [] [] []
        file_example_path [] Hp0 Hp1) file_example_in_alpha_core
    ∧ cd_mass (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
        file_example_alpha_ne file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1) = 1
    ∧ 0 < cd_weight (file_geometric_prefix file_example_hdr p [] [] []
        file_example_path [] Hp0 Hp1) file_example_off_alpha_core := by
  intro Hpos Hlt
  refine ⟨?_, ?_, rfl, ?_⟩
  · show file_prefix_over_geo_weight file_example_alpha file_example_hdr p [] [] []
      file_example_path [] file_example_off_alpha_core = 0
    exact file_prefix_over_geo_weight_off_alphabet file_example_alpha file_example_hdr p
      [] [] [] file_example_path [] [Z_to_bv 8 66] (by decide)
  · show 0 < file_prefix_over_geo_weight file_example_alpha file_example_hdr p [] [] []
      file_example_path [] file_example_in_alpha_core
    rw [show file_example_in_alpha_core
        = file_prefix_core file_example_hdr [] [] [] file_example_path [] [Z_to_bv 8 65] from rfl,
      file_prefix_over_geo_weight_match file_example_alpha file_example_hdr p [] [] []
        file_example_path [] [Z_to_bv 8 65] (by decide)]
    exact alpha_geo_point_pos file_example_alpha p _ Hpos Hlt file_example_alpha_ne
  · show 0 < file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
      file_example_off_alpha_core
    rw [show file_example_off_alpha_core
        = file_prefix_core file_example_hdr [] [] [] file_example_path [] [Z_to_bv 8 66] from rfl,
      file_prefix_geo_weight_match]
    exact geo_point_pos p _ Hpos Hlt

/-- The family bites both ways: positive on an in-alphabet core, zero off
the environment. -/
theorem file_geometric_prefix_over_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p → p < 1 →
    0 < cd_weight (file_geometric_prefix_over file_example_alpha
      file_example_alpha_nodup file_example_alpha_ne file_example_hdr p [] [] []
      file_example_path [] Hp0 Hp1) file_example_in_alpha_core
    ∧ cd_weight (file_geometric_prefix_over file_example_alpha
        file_example_alpha_nodup file_example_alpha_ne file_example_hdr p [] [] []
        file_example_path [] Hp0 Hp1) geo_example_other = 0 := by
  intro Hpos Hlt
  refine ⟨(file_geometric_prefix_over_alphabet_bites p Hp0 Hp1 Hpos Hlt).2.1, ?_⟩
  show file_prefix_over_geo_weight file_example_alpha file_example_hdr p [] [] []
    file_example_path [] geo_example_other = 0
  exact file_prefix_over_geo_weight_off_environment_zero file_example_alpha
    file_example_hdr p [] [] [] file_example_path [] geo_example_other (by decide)

/-! ## The mass is reached at `p = 1`, and duplicate-freedom is load-bearing -/

/-- The family at `p = 1`: all the mass on the bare header. -/
def file_prefix_over_point_cd : CoreDistribution :=
  file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
    file_example_alpha_ne file_example_hdr 1 [] [] [] file_example_path []
    Qle_0_1 (Rat.le_refl)

/-- One record reaches the declared mass there. -/
theorem file_prefix_over_point_cd_mass_attained :
    ([file_hdr_input].map fin_core).Nodup
    ∧ core_sum (cd_weight file_prefix_over_point_cd) [file_hdr_input]
      = cd_mass file_prefix_over_point_cd := by
  refine ⟨by simp, ?_⟩
  decide +kernel

/-- Without duplicate-freedom the cylinder bound is false: the same record
twice is in the cylinder and weighs twice the bound. -/
theorem file_geometric_prefix_over_bound_needs_nodup :
    ¬ ([file_hdr_input, file_hdr_input].map fin_core).Nodup
    ∧ (∀ f ∈ [file_hdr_input, file_hdr_input],
        in_file_prefix_cylinder file_example_hdr [] [] [] file_example_path [] []
          (fin_core f))
    ∧ ¬ (core_sum (cd_weight file_prefix_over_point_cd)
        [file_hdr_input, file_hdr_input]
        ≤ file_geometric_prefix_over_cylinder_mass file_example_alpha 1 []) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro f Hf
    rcases List.mem_cons.mp Hf with rfl | Hf
    · exact ⟨[], rfl⟩
    · rcases List.mem_cons.mp Hf with rfl | Hf
      · exact ⟨[], rfl⟩
      · exact absurd Hf (by simp)
  · decide +kernel

/-! ## The two degenerate endpoints, both pinned -/

/-- At `p = 0` every weight is zero. -/
theorem file_prefix_over_geo_weight_zero_at_zero_p (alpha hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    file_prefix_over_geo_weight alpha hdr 0 argv envp fs0 pth s c = 0 := by
  unfold file_prefix_over_geo_weight
  split
  · split
    · split
      · unfold alpha_geo_point
        exact Rat.zero_mul _
      · rfl
    · rfl
  · rfl

/-- So at `p = 0` no list can certify the declared mass `1`. -/
theorem file_geometric_prefix_over_mass_lower_needs_positive (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    (∀ l : List FinProcInput,
      core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr 0 argv envp
        fs0 pth s Rat.le_refl Qle_0_1)) l = 0)
    ∧ ¬ (cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr 0 argv envp fs0 pth s
        Rat.le_refl Qle_0_1) - 1 / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    show core_sum (file_prefix_over_geo_weight alpha hdr 0 argv envp fs0 pth s) l = 0
    exact core_sum_zero_weight _ l
      (fun c => file_prefix_over_geo_weight_zero_at_zero_p alpha hdr argv envp fs0 pth s c)
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    decide +kernel

/-- At `p = 1` every file longer than the header weighs zero. -/
theorem file_prefix_over_geo_weight_collapses_at_one_p (alpha hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    fs_file pth c.core_fs ≠ hdr →
    file_prefix_over_geo_weight alpha hdr 1 argv envp fs0 pth s c = 0 := by
  intro Hne
  by_cases Hc : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  · cases Hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none => exact file_prefix_over_geo_weight_off_header alpha hdr 1 argv envp fs0 pth s c Hs
    | some t =>
      have HS := strip_prefix_Some hdr (fs_file pth c.core_fs) t Hs
      have Hceq : c = file_prefix_core hdr argv envp fs0 pth s t :=
        Hc.trans (by rw [HS]; rfl)
      by_cases Ha : alpha_only alpha t = true
      · rw [Hceq, file_prefix_over_geo_weight_match alpha hdr 1 argv envp fs0 pth s t Ha]
        cases t with
        | nil => exact absurd (HS.trans (List.append_nil hdr)) Hne
        | cons b t' =>
          unfold alpha_geo_point alpha_geo_mass
          rw [List.length_cons, Qpow_succ]
          grind
      · rw [Hceq]
        exact file_prefix_over_geo_weight_off_alphabet alpha hdr 1 argv envp fs0 pth s t
          (Bool.not_eq_true _ ▸ Ha)
  · exact file_prefix_over_geo_weight_mismatch alpha hdr 1 argv envp fs0 pth s c Hc

/-- So at `p = 1` the distribution puts nothing past the bare header. -/
theorem file_geometric_prefix_over_needs_p_below_one (alpha : List byte)
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List byte)
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (c : FinCore) :
    fs_file pth c.core_fs ≠ hdr →
    cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr 1 argv envp fs0 pth s
      Qle_0_1 (Rat.le_refl)) c = 0 := by
  intro Hne'
  exact file_prefix_over_geo_weight_collapses_at_one_p alpha hdr argv envp fs0 pth s c Hne'

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
