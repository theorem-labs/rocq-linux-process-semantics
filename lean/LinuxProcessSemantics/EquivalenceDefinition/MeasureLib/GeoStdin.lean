-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058

# MeasureLib.GeoStdin — geometric standard input over a fixed environment

This file holds `theories/EquivalenceDefinition/MeasureLib.v` lines 3006-3658:
the combinator that weighs a core by the length of its standard input when the
core's argv, envp and file system are the fixed ones, and zero otherwise; the
prefix cylinder and the enumeration that bounds it; the three exports (cylinder
mass, cylinder bound, whole-space upper certificate); the length-slice bound
with its attainment and sharpness; the two non-vacuity blocks (Rocq 3503-3545
and 3546-3614); and the four `core_sum` identities the composition combinators
need (Rocq 3615-3657).

Rocq `Q` is `Rat`, and Rocq's `Qeq` is Lean `=`, as `Measure.lean`'s header
explains. Rocq `1 # 256` is written `1 / 256`. Names are the Rocq names.

Imported from `Prelude.lean`: `Qpow`, `Qpow_0`, `Qpow_succ`, `Qpow_Qeq`,
`Qpow_nonneg`, `Qpow_mult`, `Qpow_1`, `Qnat`, `Qnat_le`, `Qnat_256`,
`Qnat_pow_256`, `Qle_0_1`, `Qle_0_inv_256`, `Qle_of_Qeq`, `CoreDistribution`,
`cd_weight`, `cd_mass`, `FinCore_eq_dec`, `qsum`, `qsum_nil`, `qsum_cons`,
`qsum_ext`, `qsum_zero`, `core_sum`, `core_sum_nil`, `core_sum_cons`,
`core_sum_map_fin_core`.
Imported from `FiniteSupport.lean`: `all_bytes`, `all_bytes_length`,
`all_bytes_complete`, `qsum_core_incl_le`, `qsum_flat_map_const_le`,
`qsum_const`, `qsum_filter`, `list_max`, `list_max_ge`, `core_input`,
`fin_core_core_input`, `injective_core_list_in_cylinder_length_bound`,
`injective_core_list_in_cylinder_length_bound_attained`.

Every declaration of the Rocq span is ported. Nothing is left unported. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## Combinator: geometric standard input over a fixed environment -/

/-- The mass of the cylinder over a prefix of length `n`: the `n`-th power of
the one ratio `(1 - p) * (1/256)`. Continuing costs `1 - p` and choosing the
next byte costs `1/256`. The plan's three-factor form is a lemma below, not a
rival definition. -/
def geo_mass (p : Rat) (n : Nat) : Rat := Qpow ((1 - p) * (1 / 256)) n

/-- The weight of a single core whose standard input has length `n`: stopping
costs the factor `p` on top of the cylinder mass. -/
def geo_point (p : Rat) (n : Nat) : Rat := p * geo_mass p n

/-- The cylinder mass, as the product of the two powers the plan quotes. -/
theorem geo_mass_closed_form (p : Rat) (n : Nat) :
    geo_mass p n = Qpow (1 - p) n * Qpow (1 / 256) n :=
  Qpow_mult _ _ n

/-- The point weight, as `p` times the same two powers. -/
theorem geo_point_closed_form (p : Rat) (n : Nat) :
    geo_point p n = p * Qpow (1 - p) n * Qpow (1 / 256) n := by
  unfold geo_point
  rw [geo_mass_closed_form, Rat.mul_assoc]

/-- The ratio is nonnegative exactly when `p ≤ 1`. That is where the second
side condition of the constructor comes from, and the only thing it is for. -/
theorem geo_ratio_nonneg (p : Rat) : p ≤ 1 → 0 ≤ (1 - p) * (1 / 256) := by
  intro Hp1
  refine Rat.mul_nonneg ?_ Qle_0_inv_256
  exact (Rat.le_iff_sub_nonneg p 1).mp Hp1

/-- A nonnegative ratio has nonnegative powers, so every cylinder mass is
nonnegative. -/
theorem geo_mass_nonneg (p : Rat) (n : Nat) : p ≤ 1 → 0 ≤ geo_mass p n := by
  intro Hp1
  exact Qpow_nonneg _ n (geo_ratio_nonneg p Hp1)

/-- Every point weight is nonnegative, given `0 ≤ p` and `p ≤ 1`. -/
theorem geo_point_nonneg (p : Rat) (n : Nat) : 0 ≤ p → p ≤ 1 → 0 ≤ geo_point p n := by
  intro Hp0 Hp1
  exact Rat.mul_nonneg Hp0 (geo_mass_nonneg p n Hp1)

/-- A single core weighs at most the mass of the cylinder it sits at the tip
of, because `p ≤ 1`. This is the base case of the cylinder induction: a
cylinder with no room to continue holds only its own stopping core. -/
theorem geo_point_le_mass (p : Rat) (n : Nat) : p ≤ 1 → geo_point p n ≤ geo_mass p n := by
  intro Hp1
  have h := Rat.mul_le_mul_of_nonneg_right Hp1 (geo_mass_nonneg p n Hp1)
  rwa [Rat.one_mul] at h

/-- THE WEIGHT. Zero unless the core's argv, envp and file system are the fixed
ones; otherwise the geometric weight of its standard-input length. The
environment test is the single decidable equation "the core is the template
with its own standard input plugged in", which is the form the counting lemma
already carries. -/
def geo_weight (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs) (c : FinCore) : Rat :=
  if c = FinCore.mkFinCore argv envp fs c.core_stdin then geo_point p c.core_stdin.length else 0

/-- The weight at a matching core, as a rewrite rule, so that no proof below
names the decision procedure. -/
theorem geo_weight_match (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs) (s : List byte) :
    geo_weight p argv envp fs (FinCore.mkFinCore argv envp fs s) = geo_point p s.length := by
  unfold geo_weight
  exact ite_eq_left rfl

/-- The weight at a core that misses the fixed environment is zero. -/
theorem geo_weight_mismatch (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs) (c : FinCore) :
    c ≠ FinCore.mkFinCore argv envp fs c.core_stdin → geo_weight p argv envp fs c = 0 := by
  intro Hne
  unfold geo_weight
  exact ite_eq_right Hne

/-- The weight is nonnegative everywhere, which is the field the distribution
constructor needs. -/
theorem geo_weight_nonneg (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs) :
    0 ≤ p → p ≤ 1 → ∀ c, 0 ≤ geo_weight p argv envp fs c := by
  intro Hp0 Hp1 c
  unfold geo_weight
  split
  · exact geo_point_nonneg p _ Hp0 Hp1
  · exact Rat.le_refl

/-- The distribution. Mass `1` is declared, exactly as `Measure`'s header says
every `M` is; `stdin_geometric_mass_upper` below is the proof that owes
something to it. The two side conditions are arguments because `cd_nonneg` is a
field. `0 < p` is not among them. -/
def stdin_geometric (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution where
  cd_weight := geo_weight p argv envp fs
  cd_mass := 1
  cd_nonneg := geo_weight_nonneg p argv envp fs Hp0 Hp1

/-- `Measure.Distribution`'s `M_nonneg` for this family: `0 ≤ 1` on the numeral
the constructor writes. It is stated here so that a distribution assembled from
combinators can discharge the obligation with no arithmetic at the site. -/
theorem stdin_geometric_mass_nonneg (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : 0 ≤ cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) :=
  Qle_0_1

/-! ## The prefix cylinder, and the enumeration that bounds it -/

/-- The cores the cylinder bound is about: the fixed environment, and standard
input extending `bs`. One existential, which is the form both the construction
and the enumeration want. -/
def in_stdin_cylinder (argv envp : List (List byte)) (fs : Fs.Fs)
    (bs : List byte) (c : FinCore) : Prop :=
  ∃ ext, c = FinCore.mkFinCore argv envp fs (bs ++ ext)

/-- Every core in the cylinder over `bs` whose standard input exceeds `bs` by
at most `N` bytes, as a list: the stopping core, then for each byte the
enumeration of the cylinder one byte deeper. The recursion is on `N`, which is
what makes it a recursive definition at all, since `bs` grows.

Duplicate-freedom of this list is never proved and never needed:
`qsum_core_incl_le` asks nothing of the list it bounds against. -/
def cyl_enum (argv envp : List (List byte)) (fs : Fs.Fs) : List byte → Nat → List FinCore
  | bs, 0 => [FinCore.mkFinCore argv envp fs bs]
  | bs, N + 1 =>
      FinCore.mkFinCore argv envp fs bs
        :: all_bytes.flatMap (fun b => cyl_enum argv envp fs (bs ++ [b]) N)

/-- The enumeration misses nothing within its depth. -/
theorem cyl_enum_complete (argv envp : List (List byte)) (fs : Fs.Fs) (N : Nat) :
    ∀ (bs ext : List byte), ext.length ≤ N →
      FinCore.mkFinCore argv envp fs (bs ++ ext) ∈ cyl_enum argv envp fs bs N := by
  induction N with
  | zero =>
    intro bs ext Hlen
    cases ext with
    | nil => rw [List.append_nil]; exact List.Mem.head _
    | cons b ext => simp only [List.length_cons] at Hlen; omega
  | succ N ih =>
    intro bs ext Hlen
    cases ext with
    | nil => rw [List.append_nil]; exact List.Mem.head _
    | cons b ext =>
      refine List.Mem.tail _ ?_
      refine List.mem_flatMap.mpr ⟨b, all_bytes_complete b, ?_⟩
      have happ : bs ++ b :: ext = (bs ++ [b]) ++ ext := by
        rw [List.append_assoc]; rfl
      rw [happ]
      refine ih (bs ++ [b]) ext ?_
      simp only [List.length_cons] at Hlen
      omega

/-- THE CANCELLATION, by induction on the depth: the whole enumeration weighs
no more than the cylinder mass, at every depth and every prefix.

The step is exact rather than lossy, which is why the constant is the right
one. The stopping core contributes `p * m`, where `m` is the cylinder's mass;
each of the 256 continuations contributes at most the mass of a cylinder one
byte deeper, which is `(1 - p) * (1/256) * m`; and `p + 256 * (1 - p) * (1/256)`
is `1` exactly. The closed comparison `256 * (1/256) = 1` is decided by the
kernel on literals this file wrote, the way `Measure.lean` does it.

The base case is the one place `p ≤ 1` is spent for anything other than
nonnegativity: a depth-zero cylinder holds only its stopping core. -/
theorem cyl_enum_sum_le (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs) :
    0 ≤ p → p ≤ 1 →
    ∀ (N : Nat) (bs : List byte),
      qsum (geo_weight p argv envp fs) (cyl_enum argv envp fs bs N)
        ≤ geo_mass p bs.length := by
  intro Hp0 Hp1 N
  have h256 : (256 : Rat) * (1 / 256) = 1 := by decide +kernel
  have hmove : ∀ a X : Rat, 256 * (a * (1 / 256) * X) = a * X := by
    intro a X
    rw [Rat.mul_assoc a (1 / 256) X, ← Rat.mul_assoc 256 a ((1 / 256) * X),
      Rat.mul_comm 256 a, Rat.mul_assoc a 256 ((1 / 256) * X),
      ← Rat.mul_assoc 256 (1 / 256) X, h256, Rat.one_mul]
  have hstep : ∀ n : Nat, geo_point p n + 256 * geo_mass p (n + 1) = geo_mass p n := by
    intro n
    show p * Qpow ((1 - p) * (1 / 256)) n + 256 * Qpow ((1 - p) * (1 / 256)) (n + 1)
        = Qpow ((1 - p) * (1 / 256)) n
    rw [Qpow_succ, hmove (1 - p) (Qpow ((1 - p) * (1 / 256)) n),
      Rat.add_comm, ← Rat.add_mul, Rat.sub_add_cancel, Rat.one_mul]
  induction N with
  | zero =>
    intro bs
    show qsum (geo_weight p argv envp fs) [FinCore.mkFinCore argv envp fs bs]
        ≤ geo_mass p bs.length
    rw [qsum_cons, qsum_nil, geo_weight_match, Rat.add_zero]
    exact geo_point_le_mass p bs.length Hp1
  | succ N ih =>
    intro bs
    show qsum (geo_weight p argv envp fs)
          (FinCore.mkFinCore argv envp fs bs
            :: all_bytes.flatMap (fun b => cyl_enum argv envp fs (bs ++ [b]) N))
        ≤ geo_mass p bs.length
    rw [qsum_cons, geo_weight_match]
    have hblocks : ∀ b ∈ all_bytes,
        qsum (geo_weight p argv envp fs) (cyl_enum argv envp fs (bs ++ [b]) N)
          ≤ geo_mass p (bs.length + 1) := by
      intro b _
      have h := ih (bs ++ [b])
      rwa [List.length_append, List.length_singleton] at h
    have hflat := qsum_flat_map_const_le (geo_weight p argv envp fs)
      (fun b => cyl_enum argv envp fs (bs ++ [b]) N) all_bytes
      (geo_mass p (bs.length + 1)) hblocks
    rw [all_bytes_length, Qnat_256] at hflat
    refine Rat.le_trans (Rat.add_le_add_left.mpr hflat) ?_
    exact Qle_of_Qeq _ _ (hstep bs.length)

/-- The bound over cores: any duplicate-free list of cores lying in the
cylinder weighs at most the cylinder's mass. The depth to enumerate to is read
off the list, as the largest standard-input length occurring in it; that is
where the finiteness of `Measure.weight_bound_T`'s lists is spent, and the only
place it is needed. -/
theorem geo_weight_cylinder_bound (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs) :
    0 ≤ p → p ≤ 1 →
    ∀ (bs : List byte) (cs : List FinCore),
      cs.Nodup →
      (∀ c ∈ cs, in_stdin_cylinder argv envp fs bs c) →
      qsum (geo_weight p argv envp fs) cs ≤ geo_mass p bs.length := by
  intro Hp0 Hp1 bs cs Hnd Hcyl
  refine Rat.le_trans
    (qsum_core_incl_le (geo_weight p argv envp fs) cs
      (cyl_enum argv envp fs bs (list_max (cs.map (fun c => c.core_stdin.length))))
      (geo_weight_nonneg p argv envp fs Hp0 Hp1) Hnd ?_)
    (cyl_enum_sum_le p argv envp fs Hp0 Hp1 _ bs)
  intro c Hc
  have Hin : c.core_stdin.length ∈ cs.map (fun c => c.core_stdin.length) :=
    List.mem_map.mpr ⟨c, Hc, rfl⟩
  obtain ⟨ext, Hext⟩ := Hcyl c Hc
  have Hmax := list_max_ge _ _ Hin
  subst Hext
  simp only [List.length_append] at Hmax
  exact cyl_enum_complete argv envp fs _ bs ext (by omega)

/-! ## The three exports -/

/-- The cylinder's mass: a power of the ratio. -/
def stdin_geometric_cylinder_mass (p : Rat) (bs : List byte) : Rat := geo_mass p bs.length

/-- The cylinder mass in closed form, as the product of the two powers the plan
quotes. -/
theorem stdin_geometric_cylinder_mass_closed_form (p : Rat) (bs : List byte) :
    stdin_geometric_cylinder_mass p bs = Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length :=
  geo_mass_closed_form p bs.length

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in the
cylinder over `bs`, weighs at most that cylinder's mass. The hypothesis is the
one `Measure.weight_bound_T` carries, and `core_sum_map_fin_core` is the only
step between them. -/
theorem stdin_geometric_bound (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_stdin_cylinder argv envp fs bs (fin_core f)) →
    core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
      ≤ stdin_geometric_cylinder_mass p bs := by
  intro Hnd Hcyl
  show core_sum (geo_weight p argv envp fs) l ≤ stdin_geometric_cylinder_mass p bs
  rw [core_sum_map_fin_core]
  unfold stdin_geometric_cylinder_mass
  refine geo_weight_cylinder_bound p argv envp fs Hp0 Hp1 bs _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hin, rfl⟩ := List.mem_map.mp Hc
  exact Hcyl f Hin

/-- The environment test as a boolean, so that `List.filter` can use it. No
rational is involved: this decides an equality of cores. -/
def matches_env (argv envp : List (List byte)) (fs : Fs.Fs) (c : FinCore) : Bool :=
  if c = FinCore.mkFinCore argv envp fs c.core_stdin then true else false

/-- A core the test rejects is not the template with its own standard input
plugged in. -/
theorem matches_env_false (argv envp : List (List byte)) (fs : Fs.Fs) (c : FinCore) :
    matches_env argv envp fs c = false → c ≠ FinCore.mkFinCore argv envp fs c.core_stdin := by
  intro H
  unfold matches_env at H
  split at H
  · exact Bool.noConfusion H
  · assumption

/-- A core the test accepts is that template. -/
theorem matches_env_true (argv envp : List (List byte)) (fs : Fs.Fs) (c : FinCore) :
    matches_env argv envp fs c = true → c = FinCore.mkFinCore argv envp fs c.core_stdin := by
  intro H
  unfold matches_env at H
  split at H
  · assumption
  · exact Bool.noConfusion H

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE: each record is in the
cylinder, or its core misses the fixed environment entirely.

`stdin_geometric_bound` cannot drop the membership requirement: a core that
matches the environment but whose standard input leaves the cylinder has
positive weight and refutes it. What can be added is the one class of cores
that weighs nothing, and this is that statement. It is a strict generalization
of `stdin_geometric_bound` (take the left disjunct everywhere), and both are
exported: the membership form is what a task proves when its whole fire set is
inside one cylinder, the disjunctive form is what it proves when the fire set
was described some other way and happens to miss the environment elsewhere.

Without this export every consumer repeats the same repair: filter on
`matches_env`, discharge the dropped terms through `geo_weight_mismatch`, carry
duplicate-freedom across the filter, and observe that a surviving core took the
left disjunct. -/
theorem stdin_geometric_bound_or_off_environment
    (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List byte) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, in_stdin_cylinder argv envp fs bs (fin_core f)
       ∨ matches_env argv envp fs (fin_core f) = false) →
    core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
      ≤ stdin_geometric_cylinder_mass p bs := by
  intro Hnd Hor
  show core_sum (geo_weight p argv envp fs) l ≤ stdin_geometric_cylinder_mass p bs
  rw [core_sum_map_fin_core]
  have Hz : ∀ c, matches_env argv envp fs c = false → geo_weight p argv envp fs c = 0 :=
    fun c hc => geo_weight_mismatch p argv envp fs c (matches_env_false argv envp fs c hc)
  rw [qsum_filter (geo_weight p argv envp fs) (matches_env argv envp fs) _ Hz]
  unfold stdin_geometric_cylinder_mass
  refine geo_weight_cylinder_bound p argv envp fs Hp0 Hp1 bs _
    (List.Pairwise.filter _ Hnd) ?_
  intro c Hc
  rw [List.mem_filter] at Hc
  obtain ⟨Hin, Hm⟩ := Hc
  obtain ⟨f, Hinl, rfl⟩ := List.mem_map.mp Hin
  rcases Hor f Hinl with Hcyl | Hoff
  · exact Hcyl
  · rw [Hoff] at Hm
    exact Bool.noConfusion Hm

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared mass
`1`. This is the whole-space form, and it is not deferred.

With the disjunctive bound in hand it is that bound at the empty prefix, and
the whole content is that the disjunction is exhaustive there: a core either
matches the fixed launch-time environment, in which case its standard input is
`[] ++ itself` and it is in the cylinder over `[]`, or it does not, which is the
right disjunct. Nothing is assumed about the list beyond
`Measure.weight_bound_T`'s own duplicate-freedom. The cylinder mass over the
empty prefix is `1` because `Qpow` at exponent zero is. -/
theorem stdin_geometric_mass_upper (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
      ≤ cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) := by
  intro Hnd
  have hmass : cd_mass (stdin_geometric p argv envp fs Hp0 Hp1)
      = stdin_geometric_cylinder_mass p [] := by
    unfold stdin_geometric_cylinder_mass geo_mass
    rw [List.length_nil, Qpow_0]
    rfl
  rw [hmass]
  refine stdin_geometric_bound_or_off_environment p argv envp fs Hp0 Hp1 [] l Hnd ?_
  intro f _
  cases hm : matches_env argv envp fs (fin_core f) with
  | true => exact Or.inl ⟨(fin_core f).core_stdin, matches_env_true argv envp fs _ hm⟩
  | false => exact Or.inr rfl

/-- The cancellation the slice bound turns on, on its own: a full slice, all
`256 ^ n` of it, weighs exactly `p * (1 - p) ^ n`. The `256 ^ n` and the
`(1/256) ^ n` inside each weight recombine into `1 ^ n` through `Qpow_mult` and
`Qpow_1`, with no side condition. It is stated separately because both
directions need it: the bound needs it to know the constant is right, and
`stdin_geometric_slice_bound_attained` needs it to know the constant is
reached. -/
theorem geo_slice_total (p : Rat) (n : Nat) :
    Qnat (256 ^ n) * geo_point p n = p * Qpow (1 - p) n := by
  have h1 : Qpow 256 n * Qpow (1 / 256) n = 1 := by
    rw [← Qpow_mult, Qpow_Qeq ((256 : Rat) * (1 / 256)) 1 n (by decide +kernel)]
    exact Qpow_1 n
  rw [Qnat_pow_256]
  show Qpow 256 n * (p * Qpow ((1 - p) * (1 / 256)) n) = p * Qpow (1 - p) n
  rw [Qpow_mult,
    Rat.mul_comm (Qpow 256 n) (p * (Qpow (1 - p) n * Qpow (1 / 256) n)),
    Rat.mul_assoc p (Qpow (1 - p) n * Qpow (1 / 256) n) (Qpow 256 n),
    Rat.mul_assoc (Qpow (1 - p) n) (Qpow (1 / 256) n) (Qpow 256 n),
    Rat.mul_comm (Qpow (1 / 256) n) (Qpow 256 n), h1, Rat.mul_one]

/-- THE LENGTH SLICE: a list drawn from one length slice weighs at most
`p * (1 - p) ^ n`, the geometric distribution over lengths with no `1/256` left
in it. Every core in such a list weighs the same, so the sum is the length of
the list times that weight; the length is at most `256 ^ n`; and `256 ^ n`
against the `(1/256) ^ n` inside the weight cancels exactly. It is a stepping
stone to nothing below, and is exported because a task author summing over
inputs of a fixed size wants this number, not a cylinder's. -/
theorem stdin_geometric_slice_bound (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f ∈ l, fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin
       ∧ f.fin_stdin.length = n) →
    core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
      ≤ p * Qpow (1 - p) n := by
  intro Hnd Hall
  show core_sum (geo_weight p argv envp fs) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  have hconst : ∀ c ∈ l.map fin_core, geo_weight p argv envp fs c = geo_point p n := by
    intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlen⟩ := Hall f Hf
    rw [Henv, geo_weight_match, Hlen]
  rw [qsum_const _ _ (geo_point p n) hconst, ← geo_slice_total p n]
  refine Rat.mul_le_mul_of_nonneg_right ?_ (geo_point_nonneg p n Hp0 Hp1)
  rw [List.length_map]
  exact Qnat_le _ _ (injective_core_list_in_cylinder_length_bound argv envp fs n l Hnd Hall)

/-- THE SLICE BOUND'S CONSTANT IS REACHED, at every `n` and over any launch-time
environment: the full slice is admissible, and it weighs `p * (1 - p) ^ n`
exactly. Pinning that a duplicate-free slice has at most `256 ^ n` elements says
the counting is right; pinning that the bound those elements imply is reached
says the export is right. The witness is the counting lemma's own. -/
theorem stdin_geometric_slice_bound_attained
    (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ (∀ f ∈ l, fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin
            ∧ f.fin_stdin.length = n)
      ∧ core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
            = p * Qpow (1 - p) n := by
  obtain ⟨l, Hnd, Hall, Hlen⟩ :=
    injective_core_list_in_cylinder_length_bound_attained argv envp fs n
  refine ⟨l, Hnd, Hall, ?_⟩
  show core_sum (geo_weight p argv envp fs) l = p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  have hconst : ∀ c ∈ l.map fin_core, geo_weight p argv envp fs c = geo_point p n := by
    intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlength⟩ := Hall f Hf
    rw [Henv, geo_weight_match, Hlength]
  rw [qsum_const _ _ (geo_point p n) hconst, List.length_map, Hlen]
  exact geo_slice_total p n

/-- ... and so no smaller constant is a slice bound. Attainment says the number
is reached; this says it cannot be lowered. It is quantified over every
candidate `K` a future version of this file might try to prove instead, so it
stays true as a regression test rather than as a fact about today's proof. -/
theorem stdin_geometric_slice_bound_sharp
    (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (K : Rat) :
    (∀ l : List FinProcInput, (l.map fin_core).Nodup →
       (∀ f ∈ l, fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin
          ∧ f.fin_stdin.length = n) →
       core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l ≤ K) →
    p * Qpow (1 - p) n ≤ K := by
  intro Hbound
  obtain ⟨l, Hnd, Hall, Hsum⟩ :=
    stdin_geometric_slice_bound_attained p argv envp fs Hp0 Hp1 n
  rw [← Hsum]
  exact Hbound l Hnd Hall

/-! ## Non-vacuity: the weight really vanishes off the fixed environment -/

/-- Differing in argv alone is enough to zero the weight. It is stated on argv
because that is the field the example varies; envp and the file system go the
same way, through the same `geo_weight_mismatch`. -/
theorem geo_weight_off_environment_zero (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (c : FinCore) : c.core_argv ≠ argv → geo_weight p argv envp fs c = 0 := by
  intro Hne
  refine geo_weight_mismatch p argv envp fs c ?_
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- A core over the empty launch-time environment with the empty standard
input. Neither this nor the next one is claimed valid; they are two points of
`FinInput.FinCore`. -/
def geo_example_core : FinCore := FinCore.mkFinCore [] [] [] []

/-- The same, with an argv that is not empty. -/
def geo_example_other : FinCore := FinCore.mkFinCore [[Z_to_bv 8 65]] [] [] []

/-- THE BITE, both ways: the distribution is not the zero distribution, since
it puts `p` on the empty input, and it is not a constant either, since a core
with the wrong argv weighs exactly zero. Without the second half, "weight zero
off the fixed environment" would be a claim only the definition makes; without
the first, every bound above would hold of a distribution that weighs
nothing. -/
theorem stdin_geometric_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p →
    0 < cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) geo_example_core
    ∧ cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) geo_example_other = 0 := by
  intro Hlt
  constructor
  · show 0 < geo_weight p [] [] [] geo_example_core
    unfold geo_example_core
    rw [geo_weight_match]
    show 0 < p * Qpow ((1 - p) * (1 / 256)) ([] : List byte).length
    rw [List.length_nil, Qpow_0, Rat.mul_one]
    exact Hlt
  · show geo_weight p [] [] [] geo_example_other = 0
    refine geo_weight_off_environment_zero p [] [] [] geo_example_other ?_
    show [[Z_to_bv 8 65]] ≠ ([] : List (List byte))
    exact List.cons_ne_nil _ _

/-! ## Non-vacuity: the mass is reached, and duplicate-freedom is load-bearing -/

/-- The member of the family at `p = 1`: stop immediately, always. It is the
point mass on the empty standard input, the constructor admits it with
`Qle_0_1` and `Rat.le_refl`, and it is the instance that makes the two bites
below concrete arithmetic. It is also why `Qpow` exists: its ratio is zero. -/
def geo_point_cd : CoreDistribution := stdin_geometric 1 [] [] [] Qle_0_1 Rat.le_refl

/-- The record over the empty core, as a one-element admissible list needs. -/
def geo_empty_input : FinProcInput := core_input geo_example_core

/-- The declared mass `1` is not padding at this instance: a one-element
admissible list reaches it outright. That is special to `p = 1`, where the tail
past the empty input is empty; the general lower certificate can only approach
the mass. It is also this file's witness that `stdin_geometric_mass_not_attained`
cannot drop its `p < 1`. -/
theorem geo_point_cd_mass_attained :
    ([geo_empty_input].map fin_core).Nodup
    ∧ core_sum (cd_weight geo_point_cd) [geo_empty_input] = cd_mass geo_point_cd := by
  constructor
  · simp
  · show core_sum (geo_weight 1 [] [] []) [geo_empty_input] = 1
    rw [core_sum_cons, core_sum_nil]
    show geo_weight 1 [] [] [] (fin_core (core_input geo_example_core)) + 0 = 1
    rw [fin_core_core_input]
    show geo_weight 1 [] [] [] (FinCore.mkFinCore [] [] [] []) + 0 = 1
    rw [geo_weight_match]
    show (1 : Rat) * Qpow ((1 - 1) * (1 / 256)) ([] : List byte).length + 0 = 1
    rw [List.length_nil, Qpow_0]
    decide +kernel

/-- DUPLICATE-FREEDOM IS LOAD-BEARING for the cylinder bound too: offer the same
core twice, as two records, so the list is duplicate-free as a list of records
and both records lie in the cylinder over the empty prefix, and the sum is `2`
against a cylinder mass of `1`.

All three conjuncts are needed. The second says the list really does satisfy
the cylinder hypothesis, so it is not excluded by that; the third says the
bound genuinely fails on it; the first names what does exclude it. -/
theorem stdin_geometric_bound_needs_nodup :
    ¬ ([geo_empty_input, geo_empty_input].map fin_core).Nodup
    ∧ (∀ f ∈ [geo_empty_input, geo_empty_input],
          in_stdin_cylinder [] [] [] [] (fin_core f))
    ∧ ¬ (core_sum (cd_weight geo_point_cd) [geo_empty_input, geo_empty_input]
            ≤ stdin_geometric_cylinder_mass 1 []) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro f Hf
    have hf : f = geo_empty_input := by
      rcases List.mem_cons.mp Hf with h | h
      · exact h
      · exact List.mem_singleton.mp h
    subst hf
    refine ⟨[], ?_⟩
    show fin_core (core_input geo_example_core) = FinCore.mkFinCore [] [] [] ([] ++ [])
    rw [fin_core_core_input]
    rfl
  · intro Hle
    have Hle' : (1 : Rat) * Qpow ((1 - 1) * (1 / 256)) ([] : List byte).length
        + ((1 : Rat) * Qpow ((1 - 1) * (1 / 256)) ([] : List byte).length + 0)
          ≤ Qpow ((1 - (1 : Rat)) * (1 / 256)) ([] : List byte).length := by
      have h : core_sum (cd_weight geo_point_cd) [geo_empty_input, geo_empty_input]
          = (1 : Rat) * Qpow ((1 - 1) * (1 / 256)) ([] : List byte).length
            + ((1 : Rat) * Qpow ((1 - 1) * (1 / 256)) ([] : List byte).length + 0) := by
        rw [core_sum_cons, core_sum_cons, core_sum_nil]
        show geo_weight 1 [] [] [] (fin_core (core_input geo_example_core))
            + (geo_weight 1 [] [] [] (fin_core (core_input geo_example_core)) + 0) = _
        rw [fin_core_core_input]
        show geo_weight 1 [] [] [] (FinCore.mkFinCore [] [] [] [])
            + (geo_weight 1 [] [] [] (FinCore.mkFinCore [] [] [] []) + 0) = _
        rw [geo_weight_match]
        rfl
      rw [h] at Hle
      exact Hle
    rw [List.length_nil, Qpow_0] at Hle'
    exact absurd Hle' (by decide +kernel)

/-! ## Sums, scaled and added -/

/-- Scaling a weight scales its sum. Stated on `core_sum` because that is the
side a consumer's bound is on, and placed here because the composition
combinators below are its only callers. -/
theorem core_sum_scale (q : Rat) (w : FinCore → Rat) (l : List FinProcInput) :
    core_sum (fun c => q * w c) l = q * core_sum w l := by
  induction l with
  | nil => rw [core_sum_nil, core_sum_nil, Rat.mul_zero]
  | cons f l ih => rw [core_sum_cons, core_sum_cons, ih, Rat.mul_add]

/-- Adding two weights adds their sums. -/
theorem core_sum_plus (w1 w2 : FinCore → Rat) (l : List FinProcInput) :
    core_sum (fun c => w1 c + w2 c) l = core_sum w1 l + core_sum w2 l := by
  induction l with
  | nil => rw [core_sum_nil, core_sum_nil, core_sum_nil, Rat.add_zero]
  | cons f l ih =>
    rw [core_sum_cons, core_sum_cons, core_sum_cons, ih,
      Rat.add_assoc (w1 (fin_core f)) (w2 (fin_core f)),
      Rat.add_assoc (w1 (fin_core f)) (core_sum w1 l),
      Rat.add_left_comm (w2 (fin_core f)) (core_sum w1 l) (core_sum w2 l)]

/-- The zero weight sums to zero. -/
theorem core_sum_zero (l : List FinProcInput) :
    core_sum (fun _ => (0 : Rat)) l = 0 := by
  induction l with
  | nil => exact core_sum_nil _
  | cons f l ih => rw [core_sum_cons, ih, Rat.add_zero]

/-- A weight that vanishes everywhere sums to zero, whatever the list. It is
what makes the degeneracy at `p = 0` a statement about every admissible list
rather than about one witness family. -/
theorem core_sum_zero_weight (w : FinCore → Rat) (l : List FinProcInput) :
    (∀ c, w c = 0) → core_sum w l = 0 := by
  intro Hz
  rw [core_sum_map_fin_core, qsum_ext w (fun _ => 0) _ (fun c _ => Hz c)]
  exact qsum_zero _

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
