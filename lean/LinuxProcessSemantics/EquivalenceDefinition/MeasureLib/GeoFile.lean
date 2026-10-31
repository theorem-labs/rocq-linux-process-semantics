-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Calibrated

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058

# EquivalenceDefinition.MeasureLib.GeoFile — geometric file contents over a fixed environment

This file holds Rocq `theories/EquivalenceDefinition/MeasureLib.v` lines 8096-8985:
the combinator that spreads mass over the contents of ONE file, at a fixed path,
inside an otherwise fixed launch-time environment.  It carries the weight
`file_geo_weight`, the distribution `file_geometric`, the prefix-cylinder bound,
the length slice and its attainment, the lower certificate, the proof that the
declared mass is a supremum and not a maximum, the two cores that show the family
is neither silent nor constant, and the two degenerate endpoints.

The source is the Rocq file; its long arguments stay there.

`fs_file`, `file_core`, `fs_file_file_core` and `file_core_inj` are Rocq lines
8016-8094 and belong to `MeasureLib/Calibrated.lean`, which this file imports.

Rocq `Q` is `Rat`, so Rocq's `Qeq` is Lean's `=`.  Rocq `1 # 256` is `1 / 256`.
Rocq's `List.list_max` has no Lean twin, so `cores_file_depth` writes out the
`List.foldr max 0` that Rocq's `list_max` is a name for. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Measure

/-! ## The weight -/

/-- Zero unless the core is the template `file_core` with its own file contents
plugged in; otherwise the geometric weight of that file's LENGTH.

It is `geo_weight` with the varying coordinate moved from the standard input to
the contents of the file at `pth`.  The memoryless source is unchanged, so
`geo_mass`, `geo_slice_total` and `geo_prefix_sum` are reused rather than proved
again.  `argv` and `pth` are independent parameters and nothing here ties them:
a caller that varies a file the program never opens still gets declared mass `1`
and distinct positive weights, and still measures nothing. -/
def file_geo_weight (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) : Rat :=
  if c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) then
    geo_point p (fs_file pth c.core_fs).length
  else 0

/-- The weight at a core built by the template: the geometric point weight of the
contents' length.  A rewrite rule, so that no proof below names `decide` or the
`FinCore_eq_dec` instance. -/
theorem file_geo_weight_match (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s d : List byte) :
    file_geo_weight p argv envp fs0 pth s (file_core argv envp fs0 pth s d)
      = geo_point p d.length := by
  unfold file_geo_weight
  split
  · rw [fs_file_file_core]
  · rename_i hne
    exact absurd
      (congrArg (file_core argv envp fs0 pth s)
        (fs_file_file_core argv envp fs0 pth s d).symm) hne

/-- The weight away from the template is zero. -/
theorem file_geo_weight_mismatch (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) :
    c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs) →
    file_geo_weight p argv envp fs0 pth s c = 0 := by
  intro hne
  unfold file_geo_weight
  split
  · rename_i heq
    exact absurd heq hne
  · rfl

/-- The weight is never negative, for a stopping probability in `[0, 1]`. -/
theorem file_geo_weight_nonneg (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    ∀ c, 0 ≤ file_geo_weight p argv envp fs0 pth s c := by
  intro c
  unfold file_geo_weight
  split
  · exact geo_point_nonneg p (fs_file pth c.core_fs).length Hp0 Hp1
  · exact Rat.le_refl

/-- The distribution.  Mass `1` is DECLARED, as everywhere in this library, and
`file_geometric_mass_upper` is the proof that owes something to it.  Declaring `1`
is what keeps a mixture of this family with the others at total mass `1` under
`cd_scale` by shares summing to `1`.  `0 < p` is not a constructor argument;
`file_geometric_mass_lower_certificate` asks for it in its own statement. -/
def file_geometric (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution where
  cd_weight := file_geo_weight p argv envp fs0 pth s
  cd_mass := 1
  cd_nonneg := file_geo_weight_nonneg p argv envp fs0 pth s Hp0 Hp1

/-! ## The block identity: the byte-list sums, read on cores -/

/-- A block of cores obtained by mapping the template over a list of byte lists
weighs exactly what that list of byte lists weighs under `geo_point`.  Every
enumeration below is such a block, and the three byte-list sums they are charged
against already exist, so this one lemma is the whole translation. -/
theorem qsum_file_block (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (B : List (List byte)) :
    qsum (file_geo_weight p argv envp fs0 pth s) (B.map (file_core argv envp fs0 pth s))
      = qsum (fun d => geo_point p d.length) B := by
  rw [qsum_map]
  apply qsum_ext
  intro d _
  exact file_geo_weight_match p argv envp fs0 pth s d

/-! ## The prefix cylinder, and the enumeration that bounds it -/

/-- The cores the cylinder bound is about: the fixed environment, and file
contents EXTENDING `bs`.  One existential rather than a conjunction of an
environment test and a prefix test, because that is the form both the
construction and the enumeration want. -/
def in_file_cylinder (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (bs : List byte) (c : FinCore) : Prop :=
  ∃ ext, c = file_core argv envp fs0 pth s (bs ++ ext)

/-- The depth to enumerate to, read off the task's own list: the longest file
contents occurring in it.  Rocq writes `List.list_max`, which is `List.foldr max 0`;
core Lean has no `list_max`, so the fold is written out. -/
def cores_file_depth (pth : Fs.path) (cs : List FinCore) : Nat :=
  List.foldr max 0 (cs.map (fun c => (fs_file pth c.core_fs).length))

/-- Every core of the list has file contents no longer than that depth. -/
theorem cores_file_depth_ge (pth : Fs.path) (cs : List FinCore) (c : FinCore) :
    c ∈ cs → (fs_file pth c.core_fs).length ≤ cores_file_depth pth cs := by
  intro hc
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    have hstep : cores_file_depth pth (a :: cs)
        = max (fs_file pth a.core_fs).length (cores_file_depth pth cs) := rfl
    rw [hstep]
    rcases List.mem_cons.mp hc with heq | h
    · rw [heq]
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- THE BOUND OVER CORES: any duplicate-free list of cores lying in the cylinder
over the prefix `bs` weighs at most the cylinder's mass.  The enumeration is
`bytes_cyl` mapped through the template, and the cancellation that bounds it is
`bytes_cyl_sum_le`, both already proved for the byte lists. -/
theorem file_geo_weight_cylinder_bound (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (bs : List byte) (cs : List FinCore) :
    cs.Nodup → (∀ c ∈ cs, in_file_cylinder argv envp fs0 pth s bs c) →
    qsum (file_geo_weight p argv envp fs0 pth s) cs ≤ geo_mass p bs.length := by
  intro Hnd Hcyl
  have hsub : cs ⊆ (bytes_cyl bs (cores_file_depth pth cs)).map
      (file_core argv envp fs0 pth s) := by
    intro c hc
    obtain ⟨ext, hext⟩ := Hcyl c hc
    have hd := cores_file_depth_ge pth cs c hc
    rw [hext] at hd ⊢
    rw [fs_file_file_core, List.length_append] at hd
    exact List.mem_map_of_mem (bytes_cyl_In (cores_file_depth pth cs) bs ext (by omega))
  calc qsum (file_geo_weight p argv envp fs0 pth s) cs
      ≤ qsum (file_geo_weight p argv envp fs0 pth s)
          ((bytes_cyl bs (cores_file_depth pth cs)).map (file_core argv envp fs0 pth s)) :=
        qsum_core_incl_le _ _ _ (file_geo_weight_nonneg p argv envp fs0 pth s Hp0 Hp1) Hnd hsub
    _ = qsum (fun d => geo_point p d.length) (bytes_cyl bs (cores_file_depth pth cs)) :=
        qsum_file_block p argv envp fs0 pth s _
    _ ≤ geo_mass p bs.length :=
        bytes_cyl_sum_le p Hp0 Hp1 (cores_file_depth pth cs) bs

/-! ## The exports -/

/-- The cylinder's mass.  It is `stdin_geometric`'s number at the same prefix
length: the source spreading the file's bytes is the same memoryless source, so
moving an argument from standard input to the input file changes which cores are
spoken about and not what they cost. -/
def file_geometric_cylinder_mass (p : Rat) (bs : List byte) : Rat :=
  geo_mass p bs.length

/-- The cylinder mass in closed form. -/
theorem file_geometric_cylinder_mass_closed_form (p : Rat) (bs : List byte) :
    file_geometric_cylinder_mass p bs = Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length :=
  geo_mass_closed_form p bs.length

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in the
cylinder over a file-contents prefix `bs`, weighs at most that cylinder's mass.
The hypothesis is the one `Measure.weight_bound_T` carries, and
`core_sum_map_fin_core` is the only step between them.  This is what the family
exists for: a fire set described by "the input file begins with these bytes" is
charged a number that depends on the file. -/
theorem file_geometric_bound (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List byte)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_file_cylinder argv envp fs0 pth s bs (fin_core f)) →
    core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ file_geometric_cylinder_mass p bs := by
  intro Hnd Hcyl
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ geo_mass p bs.length
  rw [core_sum_map_fin_core]
  refine file_geo_weight_cylinder_bound p argv envp fs0 pth s Hp0 Hp1 bs _ Hnd ?_
  intro c hc
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
  exact Hcyl f hf

/-- The environment test as a boolean, so that `List.filter` can use it.  This
decides an equality of CORES, which `FinCore_eq_dec` decides outright, and no
rational is involved. -/
def matches_file_env (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (c : FinCore) : Bool :=
  decide (c = file_core argv envp fs0 pth s (fs_file pth c.core_fs))

/-- A false test means the core is not the template with its own contents. -/
theorem matches_file_env_false (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) :
    matches_file_env argv envp fs0 pth s c = false →
    c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs) :=
  fun h => of_decide_eq_false h

/-- A true test means the core is the template with its own contents. -/
theorem matches_file_env_true (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) :
    matches_file_env argv envp fs0 pth s c = true →
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) :=
  fun h => of_decide_eq_true h

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE: each record is in the
cylinder OR its core misses the fixed environment entirely and therefore weighs
nothing.  Both forms stay; neither weakens the other, and the widening saves a
consumer the same dozen non-obvious lines every time. -/
theorem file_geometric_bound_or_off_environment (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_file_cylinder argv envp fs0 pth s bs (fin_core f)
        ∨ matches_file_env argv envp fs0 pth s (fin_core f) = false) →
    core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ file_geometric_cylinder_mass p bs := by
  intro Hnd Hor
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ geo_mass p bs.length
  rw [core_sum_map_fin_core]
  have hz : ∀ c, matches_file_env argv envp fs0 pth s c = false →
      file_geo_weight p argv envp fs0 pth s c = 0 := by
    intro c hc
    exact file_geo_weight_mismatch p argv envp fs0 pth s c
      (matches_file_env_false argv envp fs0 pth s c hc)
  rw [qsum_filter _ (matches_file_env argv envp fs0 pth s) _ hz]
  refine file_geo_weight_cylinder_bound p argv envp fs0 pth s Hp0 Hp1 bs _
    (List.Nodup.sublist List.filter_sublist Hnd) ?_
  intro c hc
  rw [List.mem_filter] at hc
  obtain ⟨hin, hm⟩ := hc
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hin
  rcases Hor f hf with hcyl | hoff
  · exact hcyl
  · rw [hoff] at hm
    exact absurd hm (by decide)

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared mass `1`.
It is the disjunctive bound at the EMPTY prefix, and the content is that the
disjunction is EXHAUSTIVE there: a core either matches the fixed environment, in
which case its file contents are `[] ++ themselves`, or it does not.  The
cylinder mass over the empty prefix is `1` because `Qpow` at exponent zero is. -/
theorem file_geometric_mass_upper (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1) := by
  intro Hnd
  have hmass : file_geometric_cylinder_mass p ([] : List byte) = 1 := by
    unfold file_geometric_cylinder_mass geo_mass
    exact Qpow_0 _
  show core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l ≤ (1 : Rat)
  rw [← hmass]
  refine file_geometric_bound_or_off_environment p argv envp fs0 pth s Hp0 Hp1 [] l Hnd ?_
  intro f _
  cases hb : matches_file_env argv envp fs0 pth s (fin_core f) with
  | false => exact Or.inr rfl
  | true =>
    refine Or.inl ⟨fs_file pth (fin_core f).core_fs, ?_⟩
    exact matches_file_env_true argv envp fs0 pth s (fin_core f) hb

/-! ## The counting lemma and the length slice -/

/-- A list of records with duplicate-free CORES, every core matching the fixed
environment and carrying file contents of length exactly `n`, has at most `256 ^ n`
elements.  Such a core is determined by its file contents, `byte_lists n`
enumerates the length-`n` byte lists, and duplicate-freedom turns the injection
into a cardinality bound.  Unlike the envp-varying family, this slice is finite,
because the environment is fixed. -/
theorem injective_core_list_in_file_cylinder_length_bound
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs)
        ∧ (fs_file pth f.fin_image_fs).length = n) →
    l.length ≤ 256 ^ n := by
  intro Hnd Hall
  have hle : (l.map fin_core).length
      ≤ ((byte_lists n).map (file_core argv envp fs0 pth s)).length := by
    refine List.Nodup.length_le_of_subset Hnd ?_
    intro c hc
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
    obtain ⟨henv, hlen⟩ := Hall f hf
    refine List.mem_map.mpr ⟨fs_file pth f.fin_image_fs, ?_, henv.symm⟩
    rw [← hlen]
    exact byte_lists_complete _
  rw [List.length_map, List.length_map, byte_lists_length] at hle
  exact hle

/-- THE BOUND IS ATTAINED AT EVERY `n`: over any launch-time environment, any base
file system and any path there is an admissible list of exactly `256 ^ n` records,
one per length-`n` file contents.  This is where `file_core_inj` is spent: the
enumeration has to be duplicate-free ON CORES, and it is only because distinct
contents give distinct cores. -/
theorem injective_core_list_in_file_cylinder_length_bound_attained
    (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte)
    (n : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ (∀ f ∈ l, fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs)
          ∧ (fs_file pth f.fin_image_fs).length = n)
      ∧ l.length = 256 ^ n := by
  refine ⟨(byte_lists n).map (fun d => core_input (file_core argv envp fs0 pth s d)),
    ?_, ?_, ?_⟩
  · have hmap : (((byte_lists n).map
        (fun d => core_input (file_core argv envp fs0 pth s d))).map fin_core)
        = (byte_lists n).map (file_core argv envp fs0 pth s) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro d _
      exact fin_core_core_input _
    rw [hmap]
    apply NoDup_map_inj
    · intro x y _ _ heq
      exact file_core_inj argv envp fs0 pth s x y heq
    · exact byte_lists_nodup n
  · intro f hf
    obtain ⟨d, hd, hdf⟩ := List.mem_map.mp hf
    have h1 : fin_core f = file_core argv envp fs0 pth s d := by
      rw [← hdf]
      exact fin_core_core_input _
    have h2 : fs_file pth f.fin_image_fs = d := by
      rw [← hdf]
      exact fs_file_file_core argv envp fs0 pth s d
    refine ⟨?_, ?_⟩
    · rw [h1, h2]
    · rw [h2]
      exact byte_lists_In_length n d hd
  · rw [List.length_map, byte_lists_length]

/-- THE LENGTH SLICE: a list drawn from one file-length slice weighs at most
`p * (1 - p) ^ n`, the geometric distribution over LENGTHS with no `1/256` left in
it.  The counting lemma supplies the count, `qsum_const` observes that every core
in a slice weighs the same, and `geo_slice_total` is the cancellation. -/
theorem file_geometric_slice_bound (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs)
        ∧ (fs_file pth f.fin_image_fs).length = n) →
    core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ p * Qpow (1 - p) n := by
  intro Hnd Hall
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  have hc : ∀ c ∈ l.map fin_core,
      file_geo_weight p argv envp fs0 pth s c = geo_point p n := by
    intro c hcm
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hcm
    obtain ⟨henv, hlen⟩ := Hall f hf
    rw [henv, file_geo_weight_match, hlen]
  rw [qsum_const _ _ _ hc, ← geo_slice_total p n]
  refine Rat.mul_le_mul_of_nonneg_right ?_ (geo_point_nonneg p n Hp0 Hp1)
  apply Qnat_le
  rw [List.length_map]
  exact injective_core_list_in_file_cylinder_length_bound argv envp fs0 pth s n l Hnd Hall

/-- THE SLICE BOUND'S CONSTANT IS REACHED, at every `n`: the full slice is
admissible and weighs `p * (1 - p) ^ n` exactly.  Pinning that a duplicate-free
slice has at most `256 ^ n` elements says the counting is right; pinning that the
bound those elements imply is reached says the EXPORT is right. -/
theorem file_geometric_slice_bound_attained (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ (∀ f ∈ l, fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs)
          ∧ (fs_file pth f.fin_image_fs).length = n)
      ∧ core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
          = p * Qpow (1 - p) n := by
  obtain ⟨l, Hnd, Hall, Hlen⟩ :=
    injective_core_list_in_file_cylinder_length_bound_attained argv envp fs0 pth s n
  refine ⟨l, Hnd, Hall, ?_⟩
  show core_sum (file_geo_weight p argv envp fs0 pth s) l = p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  have hc : ∀ c ∈ l.map fin_core,
      file_geo_weight p argv envp fs0 pth s c = geo_point p n := by
    intro c hcm
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hcm
    obtain ⟨henv, hlen⟩ := Hall f hf
    rw [henv, file_geo_weight_match, hlen]
  rw [qsum_const _ _ _ hc, List.length_map, Hlen]
  exact geo_slice_total p n

/-- ... and so NO SMALLER CONSTANT IS A SLICE BOUND.  The contrapositive shape is
deliberate: it is quantified over every candidate `K` a future version of this
file might try to prove instead, so it stays true as a regression test rather
than as a fact about today's proof. -/
theorem file_geometric_slice_bound_sharp (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (n : Nat) (K : Rat) :
    (∀ l : List FinProcInput, (l.map fin_core).Nodup →
      (∀ f ∈ l, fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs)
          ∧ (fs_file pth f.fin_image_fs).length = n) →
      core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l ≤ K) →
    p * Qpow (1 - p) n ≤ K := by
  intro Hbound
  obtain ⟨l, Hnd, Hall, Hsum⟩ :=
    file_geometric_slice_bound_attained p argv envp fs0 pth s Hp0 Hp1 n
  rw [← Hsum]
  exact Hbound l Hnd Hall

/-! ## The lower certificate -/

/-- THE WITNESS FAMILY: over a fixed environment, one record per file contents
SHORTER than `k`.  `short_inputs` is the same length-bounded enumeration of byte
lists the standard-input certificate uses; only the embedding into cores is this
family's.  These records are not claimed valid and not claimed rejected; the
certificate is arithmetic about the declared mass. -/
def file_geo_lower_witness (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (k : Nat) : List FinProcInput :=
  (short_inputs k).map (fun d => core_input (file_core argv envp fs0 pth s d))

/-- The witness family's cores are the template over `short_inputs k`. -/
theorem map_fin_core_file_geo_lower_witness (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (k : Nat) :
    (file_geo_lower_witness argv envp fs0 pth s k).map fin_core
      = (short_inputs k).map (file_core argv envp fs0 pth s) := by
  unfold file_geo_lower_witness
  rw [List.map_map]
  apply List.map_congr_left
  intro d _
  exact fin_core_core_input _

/-- The witness family has duplicate-free cores, by injectivity of the template. -/
theorem file_geo_lower_witness_nodup (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (k : Nat) :
    ((file_geo_lower_witness argv envp fs0 pth s k).map fin_core).Nodup := by
  rw [map_fin_core_file_geo_lower_witness]
  apply NoDup_map_inj
  · intro x y _ _ heq
    exact file_core_inj argv envp fs0 pth s x y heq
  · exact short_inputs_nodup k

/-- ... and it weighs the partial sum of the geometric series over lengths.  Both
halves are proved elsewhere, so this is two rewrites and no induction. -/
theorem qsum_file_short_inputs (p : Rat) (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (k : Nat) :
    qsum (file_geo_weight p argv envp fs0 pth s)
        ((short_inputs k).map (file_core argv envp fs0 pth s))
      = geo_prefix_sum p k := by
  rw [qsum_file_block]
  exact short_inputs_sum p k

/-- THE WITNESS, at each `k`: an admissible list weighing exactly `1 - (1 - p) ^ k`.
The target is that rather than the declared mass because the mass is not
available: for `p < 1` no finite list attains it. -/
theorem file_geometric_mass_lower_witness (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ((file_geo_lower_witness argv envp fs0 pth s k).map fin_core).Nodup
    ∧ core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1))
        (file_geo_lower_witness argv envp fs0 pth s k)
        = 1 - Qpow (1 - p) k := by
  refine ⟨file_geo_lower_witness_nodup argv envp fs0 pth s k, ?_⟩
  show core_sum (file_geo_weight p argv envp fs0 pth s)
      (file_geo_lower_witness argv envp fs0 pth s k) = 1 - Qpow (1 - p) k
  rw [core_sum_map_fin_core, map_fin_core_file_geo_lower_witness, qsum_file_short_inputs]
  exact geo_prefix_sum_closed p k

/-- The same fact in the shape the certificate vocabulary uses: SOME admissible
list weighs the target. -/
theorem file_geometric_mass_lower_prefix (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
          = 1 - Qpow (1 - p) k :=
  ⟨file_geo_lower_witness argv envp fs0 pth s k,
    file_geometric_mass_lower_witness p argv envp fs0 pth s Hp0 Hp1 k⟩

/-- THE LOWER CERTIFICATE: for every margin `eps` there is an admissible list
weighing at least the declared mass minus that margin.  With
`file_geometric_mass_upper`, the declared `1` is the least upper bound of the
admissible partial sums.  `0 < p` is a hypothesis of this lemma and not a
tightening of the constructor; it is spent once, inside `geo_gap_small`, choosing
the `k` whose tail is under `eps`. -/
theorem file_geometric_mass_lower_certificate (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat) :
    0 < p → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1) - eps
          ≤ core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l := by
  intro Hpos Heps
  obtain ⟨k, hk⟩ := geo_gap_small p eps Hpos Hp1 Heps
  obtain ⟨l, hnd, hsum⟩ :=
    file_geometric_mass_lower_prefix p argv envp fs0 pth s Hp0 Hp1 k
  refine ⟨l, hnd, ?_⟩
  rw [hsum]
  show (1 : Rat) - eps ≤ 1 - Qpow (1 - p) k
  have hneg : -eps ≤ -(Qpow (1 - p) k) := Rat.neg_le_neg_iff.mpr hk
  calc (1 : Rat) - eps = 1 + -eps := Rat.sub_eq_add_neg 1 eps
    _ ≤ 1 + -(Qpow (1 - p) k) := Rat.add_le_add_left.mpr hneg
    _ = 1 - Qpow (1 - p) k := (Rat.sub_eq_add_neg 1 (Qpow (1 - p) k)).symm

/-! ## ... and this mass is a SUPREMUM and not a maximum -/

/-- A list confined to file contents of length at most `n` weighs at most
`1 - (1 - p) ^ (n + 1)`, the partial sum at its own horizon.  It MISSES THE TAIL,
and the tail is the whole point. -/
theorem file_geometric_bound_by_max_length (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, (fs_file pth f.fin_image_fs).length ≤ n) →
    core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ 1 - Qpow (1 - p) (n + 1) := by
  intro Hnd Hlen
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ 1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  have hz : ∀ c, matches_file_env argv envp fs0 pth s c = false →
      file_geo_weight p argv envp fs0 pth s c = 0 := by
    intro c hc
    exact file_geo_weight_mismatch p argv envp fs0 pth s c
      (matches_file_env_false argv envp fs0 pth s c hc)
  rw [qsum_filter _ (matches_file_env argv envp fs0 pth s) _ hz]
  have hsub : ((l.map fin_core).filter (matches_file_env argv envp fs0 pth s))
      ⊆ (short_inputs (n + 1)).map (file_core argv envp fs0 pth s) := by
    intro c hc
    rw [List.mem_filter] at hc
    obtain ⟨hin, hm⟩ := hc
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hin
    refine List.mem_map.mpr ⟨fs_file pth (fin_core f).core_fs, ?_, ?_⟩
    · apply short_inputs_complete
      exact Nat.lt_succ_of_le (Hlen f hf)
    · exact (matches_file_env_true argv envp fs0 pth s (fin_core f) hm).symm
  calc qsum (file_geo_weight p argv envp fs0 pth s)
        ((l.map fin_core).filter (matches_file_env argv envp fs0 pth s))
      ≤ qsum (file_geo_weight p argv envp fs0 pth s)
          ((short_inputs (n + 1)).map (file_core argv envp fs0 pth s)) :=
        qsum_core_incl_le _ _ _ (file_geo_weight_nonneg p argv envp fs0 pth s Hp0 Hp1)
          (List.Nodup.sublist List.filter_sublist Hnd) hsub
    _ = geo_prefix_sum p (n + 1) := qsum_file_short_inputs p argv envp fs0 pth s (n + 1)
    _ = 1 - Qpow (1 - p) (n + 1) := geo_prefix_sum_closed p (n + 1)

/-- ... AND THAT BOUND IS EXACTLY TIGHT: the witness family at `k = n + 1` is a
list of file contents of length at most `n`, and it weighs the bound exactly.  So
the shortfall below is the distribution's and not the proof's. -/
theorem file_geometric_bound_by_max_length_attained (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    (∀ f ∈ file_geo_lower_witness argv envp fs0 pth s (n + 1),
        (fs_file pth f.fin_image_fs).length ≤ n)
    ∧ core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1))
        (file_geo_lower_witness argv envp fs0 pth s (n + 1))
        = 1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (file_geometric_mass_lower_witness p argv envp fs0 pth s Hp0 Hp1 (n + 1)).2⟩
  intro f hf
  unfold file_geo_lower_witness at hf
  obtain ⟨d, hd, hdf⟩ := List.mem_map.mp hf
  have h2 : fs_file pth f.fin_image_fs = d := by
    rw [← hdf]
    exact fs_file_file_core argv envp fs0 pth s d
  rw [h2]
  have hlt := short_inputs_In_length (n + 1) d hd
  omega

/-- For `p < 1` NO admissible list weighs the declared mass: every one of them
weighs strictly less.  The horizon is the list's own longest file contents, which
is the only place the FINITENESS of the list is needed: beyond it sits a positive
tail the list does not collect.  At `p = 1` it is false, and
`file_point_cd_mass_attained` is the list that refutes it. -/
theorem file_geometric_mass_not_attained (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
        < cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1) := by
  intro Hlt l Hnd
  have hb : core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
      ≤ 1 - Qpow (1 - p) (cores_file_depth pth (l.map fin_core) + 1) := by
    refine file_geometric_bound_by_max_length p argv envp fs0 pth s Hp0 Hp1
      (cores_file_depth pth (l.map fin_core)) l Hnd ?_
    intro f hf
    exact cores_file_depth_ge pth (l.map fin_core) (fin_core f) (List.mem_map_of_mem hf)
  have hpos : 0 < Qpow (1 - p) (cores_file_depth pth (l.map fin_core) + 1) := by
    apply Qpow_pos
    exact (Rat.lt_iff_sub_pos p 1).mp Hlt
  have hstrict : (1 : Rat) - Qpow (1 - p) (cores_file_depth pth (l.map fin_core) + 1) < 1 := by
    rw [Rat.sub_lt_iff]
    have h1 : (1 : Rat) + 0
        < 1 + Qpow (1 - p) (cores_file_depth pth (l.map fin_core) + 1) :=
      Rat.add_lt_add_left.mpr hpos
    rw [Rat.add_zero] at h1
    exact h1
  show core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l < (1 : Rat)
  refine Rat.not_le.mp ?_
  intro hle
  exact Rat.not_le.mpr hstrict (Rat.le_trans hle hb)

/-- The same fact under the name a reader looks for. -/
theorem file_geometric_mass_supremum_not_maximum (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    p < 1 →
    ∀ l : List FinProcInput, (l.map fin_core).Nodup →
      ¬ (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
          = cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1)) := by
  intro Hlt l Hnd heq
  have h := file_geometric_mass_not_attained p argv envp fs0 pth s Hp0 Hp1 Hlt l Hnd
  rw [heq] at h
  exact Rat.lt_irrefl h

/-! ## Non-vacuity: the input file really carries mass -/

/-- `geo_weight`'s file-system instance: a core whose file system is not the fixed
one weighs nothing.  Stated because the bite below needs it and the standard-input
family had only the argv and envp instances. -/
theorem geo_weight_off_fs_zero (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (c : FinCore) : c.core_fs ≠ fs → geo_weight p argv envp fs c = 0 := by
  intro hne
  apply geo_weight_mismatch
  intro heq
  exact hne (congrArg FinCore.core_fs heq)

/-- A core whose argv misses the fixed one weighs nothing under this family. -/
theorem file_geo_weight_off_environment_zero (p : Rat) (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) (c : FinCore) :
    c.core_argv ≠ argv → file_geo_weight p argv envp fs0 pth s c = 0 := by
  intro hne
  apply file_geo_weight_mismatch
  intro heq
  exact hne (congrArg FinCore.core_argv heq)

/-- The one-byte path `i`.  It is a point of `Fs.path`, not a claim about any
program. -/
def file_example_path : Fs.path := [Z_to_bv 8 105]

/-- The core over the empty launch-time environment whose file at
`file_example_path` is empty.  Chosen so that the two families disagree on it. -/
def file_example_core : FinCore :=
  file_core [] [] [] file_example_path [] []

/-- THE BITE THE FAMILY EXISTS FOR, both halves on ONE core.  `stdin_geometric`
over the empty file system weighs `file_example_core` exactly zero, because that
core's file system is not the fixed one: it HAS the input file in it.
`file_geometric` weighs the same core strictly positively.

That is the gap restated as a theorem.  Under a distribution built from
`stdin_geometric` alone every weighted core carries the same file system, so a
per-input predicate about program behaviour holds at all weighted cores or at
none, and the least provable bound is `0` or `1`.  Under this family the file's
bytes carry mass, so intermediate values are available.  It does NOT say that any
particular task's bound is thereby sharper. -/
theorem file_geometric_fs_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p →
    cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) file_example_core = 0
    ∧ 0 < cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
            file_example_core := by
  intro Hlt
  refine ⟨?_, ?_⟩
  · show geo_weight p [] [] [] file_example_core = 0
    apply geo_weight_off_fs_zero
    show Fs.fs_set [] file_example_path [] ≠ []
    exact List.cons_ne_nil _ _
  · show 0 < file_geo_weight p [] [] [] file_example_path []
        (file_core [] [] [] file_example_path [] [])
    rw [file_geo_weight_match, List.length_nil]
    unfold geo_point geo_mass
    rw [Qpow_0, Rat.mul_one]
    exact Hlt

/-- ... and the family is not a constant either: a core whose argv misses the
fixed one weighs exactly zero.  Both halves are needed: without the second,
"weight zero off the fixed environment" would be a claim only the definition
makes; without the first, every bound above would hold of a distribution that
weighs nothing. -/
theorem file_geometric_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p →
    0 < cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
          file_example_core
    ∧ cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
        geo_example_other = 0 := by
  intro Hlt
  refine ⟨(file_geometric_fs_bites p Hp0 Hp1 Hlt).2, ?_⟩
  show file_geo_weight p [] [] [] file_example_path [] geo_example_other = 0
  apply file_geo_weight_off_environment_zero
  show geo_example_other.core_argv ≠ []
  exact List.cons_ne_nil _ _

/-! ## Non-vacuity: the mass is reached at `p = 1`, and duplicate-freedom is
load-bearing -/

/-- The member of the family at `p = 1`: stop immediately, always.  It is the
point mass on the empty file, the constructor admits it, and it makes the two
refutations below closed arithmetic instead of open terms. -/
def file_point_cd : CoreDistribution :=
  file_geometric 1 [] [] [] file_example_path [] Qle_0_1 Rat.le_refl

/-- The one record over `file_example_core`. -/
def file_empty_input : FinProcInput := core_input file_example_core

/-- The declared mass `1` is not padding at this instance: a one-element
admissible list reaches it OUTRIGHT.  That is special to `p = 1`, where the tail
past the empty file is empty, and it is why `file_geometric_mass_not_attained`
cannot drop its `p < 1`. -/
theorem file_point_cd_mass_attained :
    (([file_empty_input].map fin_core)).Nodup
    ∧ core_sum (cd_weight file_point_cd) [file_empty_input] = cd_mass file_point_cd := by
  have hw : file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input)
      = 1 := by
    show file_geo_weight 1 [] [] [] file_example_path []
        (file_core [] [] [] file_example_path [] []) = 1
    rw [file_geo_weight_match, List.length_nil]
    unfold geo_point geo_mass
    rw [Qpow_0]
    decide +kernel
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.map_nil]
    exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · show file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input) + 0
        = (1 : Rat)
    rw [hw]
    decide +kernel

/-- THE DUPLICATE-FREEDOM HYPOTHESIS IS LOAD-BEARING for this family's cylinder
bound: offer the same core twice, as two records, and the list is duplicate-free
as a list of RECORDS, both records lie in the cylinder over the empty prefix, and
the sum is `2` against a cylinder mass of `1`.  All three conjuncts are needed. -/
theorem file_geometric_bound_needs_nodup :
    ¬ (([file_empty_input, file_empty_input].map fin_core).Nodup)
    ∧ (∀ f ∈ [file_empty_input, file_empty_input],
        in_file_cylinder [] [] [] file_example_path [] [] (fin_core f))
    ∧ ¬ (core_sum (cd_weight file_point_cd) [file_empty_input, file_empty_input]
          ≤ file_geometric_cylinder_mass 1 []) := by
  have hw : file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input)
      = 1 := by
    show file_geo_weight 1 [] [] [] file_example_path []
        (file_core [] [] [] file_example_path [] []) = 1
    rw [file_geo_weight_match, List.length_nil]
    unfold geo_point geo_mass
    rw [Qpow_0]
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · intro hnd
    rw [List.map_cons, List.map_cons, List.map_nil] at hnd
    exact (List.nodup_cons.mp hnd).1 (by simp)
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf2
    · exact ⟨[], fin_core_core_input _⟩
    · rcases List.mem_cons.mp hf2 with rfl | hf3
      · exact ⟨[], fin_core_core_input _⟩
      · simp at hf3
  · intro hle
    have e1 : core_sum (cd_weight file_point_cd) [file_empty_input, file_empty_input]
        = 1 + (1 + 0) := by
      show file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input)
          + (file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input) + 0)
          = 1 + (1 + 0)
      rw [hw]
    have e2 : file_geometric_cylinder_mass 1 ([] : List byte) = 1 := by
      unfold file_geometric_cylinder_mass geo_mass
      exact Qpow_0 _
    rw [e1, e2] at hle
    exact absurd hle (by decide +kernel)

/-! ## The two degenerate endpoints, both pinned -/

/-- At `p = 0` the weight vanishes identically. -/
theorem file_geo_weight_zero_at_zero_p (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) :
    file_geo_weight 0 argv envp fs0 pth s c = 0 := by
  unfold file_geo_weight
  split
  · unfold geo_point
    exact Rat.zero_mul _
  · rfl

/-- ... so at `p = 0` every list weighs nothing while the declared mass stays `1`,
and the lower certificate is false.  This is the vanishing failure mode. -/
theorem file_geometric_mass_lower_needs_positive (argv envp : List (List byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List byte) :
    (∀ l : List FinProcInput,
       core_sum (cd_weight (file_geometric 0 argv envp fs0 pth s Rat.le_refl Qle_0_1)) l = 0)
    ∧ ¬ (cd_mass (file_geometric 0 argv envp fs0 pth s Rat.le_refl Qle_0_1) - (1 / 2) ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    exact file_geo_weight_zero_at_zero_p argv envp fs0 pth s c
  · intro hle
    have h : (1 : Rat) - (1 / 2) ≤ 0 := hle
    exact absurd h (by decide +kernel)

/-- At `p = 1` the weight does NOT vanish, and that degeneracy is the interesting
one: every core whose input file is NON-EMPTY weighs zero while the empty-file
core keeps its weight.  The family goes blind to the file contents without going
quiet. -/
theorem file_geo_weight_collapses_at_one_p (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) :
    fs_file pth c.core_fs ≠ [] → file_geo_weight 1 argv envp fs0 pth s c = 0 := by
  intro Hne
  unfold file_geo_weight
  split
  · have hpos : 0 < (fs_file pth c.core_fs).length := by
      cases h : fs_file pth c.core_fs with
      | nil => exact absurd h Hne
      | cons b d => simp
    obtain ⟨m, hm⟩ : ∃ m, (fs_file pth c.core_fs).length = m + 1 :=
      ⟨(fs_file pth c.core_fs).length - 1, by omega⟩
    rw [hm]
    unfold geo_point geo_mass
    simp only [Qpow_succ, Rat.sub_self, Rat.zero_mul, Rat.mul_zero]
  · rfl

/-- ... and the blindness as a statement about the distribution.  Both are
exported: a reader asking "what goes wrong at this parameter" wants the
blindness, and a reader asking "what does the weight become" wants the identity
above. -/
theorem file_geometric_needs_p_below_one (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List byte) (c : FinCore) :
    fs_file pth c.core_fs ≠ [] →
    cd_weight (file_geometric 1 argv envp fs0 pth s Qle_0_1 Rat.le_refl) c = 0 := by
  intro Hne
  exact file_geo_weight_collapses_at_one_p argv envp fs0 pth s c Hne

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
