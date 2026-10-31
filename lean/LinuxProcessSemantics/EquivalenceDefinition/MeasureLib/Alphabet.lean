-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-!

# MeasureLib.Alphabet — byte lists over a fixed alphabet

This file holds Rocq `MeasureLib.v:10042-10455`: byte lists over a fixed
alphabet, and the geometric arithmetic over it.

The 256-byte families spread a payload's bytes over every byte. A program
that reads text wants printable input, and under the 256-byte law almost
every payload holds a control byte. So the shape those families count and
sum is written once here over an alphabet `alpha`, with hypotheses where
the 256-byte enumeration had facts: the alphabet repeats nothing, and it
is not empty. An alphabet is not asked to hold every byte, so completeness
becomes a test on payloads, `alpha_only`. The 256-byte objects are the
case `alpha = all_bytes`, and that is proved: `alpha_lists_all_bytes`,
`alpha_short_inputs_all_bytes`, `alpha_cyl_all_bytes`,
`alpha_geo_mass_all_bytes`.

Rocq's `Q` is Lean's `Rat`, whose values are reduced, so each Rocq `Qeq`
statement is an `=` statement here.

Every one of the span's 45 Rocq declarations is here. No `unported:` line. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## Membership in the alphabet -/

/-- Membership in the alphabet, as a boolean. -/
def alpha_memb (alpha : List byte) (b : byte) : Bool :=
  alpha.any (fun a => decide (a = b))

/-- The boolean test agrees with membership in the list. -/
theorem alpha_memb_In (alpha : List byte) (b : byte) :
    alpha_memb alpha b = true ↔ b ∈ alpha := by
  constructor
  · intro h
    obtain ⟨a, ha, hab⟩ := List.any_eq_true.mp h
    have hab' : a = b := of_decide_eq_true hab
    subst hab'
    exact ha
  · intro h
    exact List.any_eq_true.mpr ⟨b, h, decide_eq_true rfl⟩

/-- Every byte of `t` is in the alphabet, as a boolean. -/
def alpha_only (alpha t : List byte) : Bool :=
  t.all (alpha_memb alpha)

/-- The payload test agrees with "every byte of `t` is in `alpha`". -/
theorem alpha_only_In (alpha t : List byte) :
    alpha_only alpha t = true ↔ ∀ b, b ∈ t → b ∈ alpha := by
  unfold alpha_only
  rw [List.all_eq_true]
  exact ⟨fun h b hb => (alpha_memb_In alpha b).mp (h b hb),
         fun h b hb => (alpha_memb_In alpha b).mpr (h b hb)⟩

/-- The test splits over an append. -/
theorem alpha_only_app (alpha t1 t2 : List byte) :
    alpha_only alpha (t1 ++ t2) = (alpha_only alpha t1 && alpha_only alpha t2) := by
  unfold alpha_only
  exact List.all_append

/-- Every payload is over the full alphabet: the test is
`all_bytes_complete` read as a boolean. -/
theorem alpha_only_all_bytes (t : List byte) : alpha_only all_bytes t = true :=
  (alpha_only_In all_bytes t).mpr (fun b _ => all_bytes_complete b)

/-- The full alphabet is not empty, because it has 256 members. -/
theorem all_bytes_ne : all_bytes ≠ [] := by
  intro h
  have hl : all_bytes.length = ([] : List byte).length := congrArg List.length h
  rw [all_bytes_length] at hl
  simp at hl

/-! ## The per-byte ratio -/

/-- One over the alphabet's size. This is the inverse of a `Qnat`, not a
fraction with a fixed denominator, so that the size is the list's own
length and the cancellation below is a multiplication by an inverse under
"not empty". -/
def alpha_ratio (alpha : List byte) : Rat := (Qnat alpha.length)⁻¹

/-- The ratio is never negative. -/
theorem alpha_ratio_nonneg (alpha : List byte) : 0 ≤ alpha_ratio alpha := by
  unfold alpha_ratio
  rcases Rat.le_iff_lt_or_eq.mp (Qnat_nonneg alpha.length) with h | h
  · exact Rat.le_of_lt (Rat.inv_pos.mpr h)
  · rw [← h, Rat.inv_zero]
    exact Rat.le_refl

/-- A non-empty list has a strictly positive count. -/
theorem Qnat_length_pos (alpha : List byte) :
    alpha ≠ [] → 0 < Qnat alpha.length := by
  intro hne
  cases alpha with
  | nil => exact absurd rfl hne
  | cons a alpha =>
    have h1 : (1 : Rat) + 0 ≤ 1 + Qnat alpha.length :=
      Rat.add_le_add_left.mpr (Qnat_nonneg alpha.length)
    rw [Rat.add_zero] at h1
    show 0 < Qnat (a :: alpha).length
    rw [List.length_cons, Qnat_succ]
    exact Std.lt_of_lt_of_le (by decide) h1

/-- A non-empty alphabet has a strictly positive ratio. -/
theorem alpha_ratio_pos (alpha : List byte) : alpha ≠ [] → 0 < alpha_ratio alpha :=
  fun hne => Rat.inv_pos.mpr (Qnat_length_pos alpha hne)

/-- The size and the ratio cancel. This is where "not empty" is spent. -/
theorem alpha_ratio_cancel (alpha : List byte) :
    alpha ≠ [] → Qnat alpha.length * alpha_ratio alpha = 1 := by
  intro hne
  unfold alpha_ratio
  refine Rat.mul_inv_cancel _ ?_
  intro h0
  have hpos := Qnat_length_pos alpha hne
  rw [h0] at hpos
  exact absurd hpos (by decide)

/-- At the full alphabet the ratio is one over 256. -/
theorem alpha_ratio_all_bytes : alpha_ratio all_bytes = 1 / 256 := by
  unfold alpha_ratio
  rw [all_bytes_length]
  decide +kernel

/-! ## The geometric arithmetic over an alphabet -/

/-- The mass of a payload cylinder over the alphabet: powers of the one
ratio `(1 - p) * alpha_ratio alpha`, as `geo_mass` is powers of
`(1 - p) * (1 / 256)`. -/
def alpha_geo_mass (alpha : List byte) (p : Rat) (n : Nat) : Rat :=
  Qpow ((1 - p) * alpha_ratio alpha) n

/-- The weight of one payload of length `n` over the alphabet. -/
def alpha_geo_point (alpha : List byte) (p : Rat) (n : Nat) : Rat :=
  p * alpha_geo_mass alpha p n

/-- The mass splits into the continuation power and the ratio power. -/
theorem alpha_geo_mass_closed_form (alpha : List byte) (p : Rat) (n : Nat) :
    alpha_geo_mass alpha p n = Qpow (1 - p) n * Qpow (alpha_ratio alpha) n :=
  Qpow_mult (1 - p) (alpha_ratio alpha) n

/-- The point weight in the three-factor form. -/
theorem alpha_geo_point_closed_form (alpha : List byte) (p : Rat) (n : Nat) :
    alpha_geo_point alpha p n = p * Qpow (1 - p) n * Qpow (alpha_ratio alpha) n := by
  unfold alpha_geo_point
  rw [alpha_geo_mass_closed_form, ← Rat.mul_assoc]

/-- The ratio the powers run on is never negative when `p` is at most 1. -/
theorem alpha_geo_ratio_nonneg (alpha : List byte) (p : Rat) :
    p ≤ 1 → 0 ≤ (1 - p) * alpha_ratio alpha :=
  fun hp1 => Rat.mul_nonneg ((Rat.le_iff_sub_nonneg p 1).mp hp1) (alpha_ratio_nonneg alpha)

/-- The mass is never negative when `p` is at most 1. -/
theorem alpha_geo_mass_nonneg (alpha : List byte) (p : Rat) (n : Nat) :
    p ≤ 1 → 0 ≤ alpha_geo_mass alpha p n :=
  fun hp1 => Qpow_nonneg _ n (alpha_geo_ratio_nonneg alpha p hp1)

/-- The point weight is never negative when `p` is in `[0, 1]`. -/
theorem alpha_geo_point_nonneg (alpha : List byte) (p : Rat) (n : Nat) :
    0 ≤ p → p ≤ 1 → 0 ≤ alpha_geo_point alpha p n :=
  fun hp0 hp1 => Rat.mul_nonneg hp0 (alpha_geo_mass_nonneg alpha p n hp1)

/-- One payload never weighs more than the cylinder it sits in. -/
theorem alpha_geo_point_le_mass (alpha : List byte) (p : Rat) (n : Nat) :
    p ≤ 1 → alpha_geo_point alpha p n ≤ alpha_geo_mass alpha p n := by
  intro hp1
  have h := Rat.mul_le_mul_of_nonneg_right hp1 (alpha_geo_mass_nonneg alpha p n hp1)
  rw [Rat.one_mul] at h
  exact h

/-- Every payload of a non-empty alphabet weighs something, when `p` is
strictly between 0 and 1. -/
theorem alpha_geo_point_pos (alpha : List byte) (p : Rat) (n : Nat) :
    0 < p → p < 1 → alpha ≠ [] → 0 < alpha_geo_point alpha p n := by
  intro hp0 hp1 hne
  show 0 < p * alpha_geo_mass alpha p n
  refine Rat.mul_pos hp0 ?_
  show 0 < Qpow ((1 - p) * alpha_ratio alpha) n
  exact Qpow_pos _ n
    (Rat.mul_pos ((Rat.lt_iff_sub_pos p 1).mp hp1) (alpha_ratio_pos alpha hne))

/-- At the full alphabet the mass is the 256-byte mass. -/
theorem alpha_geo_mass_all_bytes (p : Rat) (n : Nat) :
    alpha_geo_mass all_bytes p n = geo_mass p n := by
  show Qpow ((1 - p) * alpha_ratio all_bytes) n = geo_mass p n
  rw [alpha_ratio_all_bytes]
  rfl

/-- At the full alphabet the point weight is the 256-byte point weight. -/
theorem alpha_geo_point_all_bytes (p : Rat) (n : Nat) :
    alpha_geo_point all_bytes p n = geo_point p n := by
  show p * alpha_geo_mass all_bytes p n = geo_point p n
  rw [alpha_geo_mass_all_bytes]
  rfl

/-! ## The length-`n` lists over the alphabet -/

/-- Every list of length `n` over the alphabet: `byte_lists` with `alpha`
in place of `all_bytes`. -/
def alpha_lists (alpha : List byte) : Nat → List (List byte)
  | 0 => [[]]
  | n + 1 => alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l))

/-- At the full alphabet this is `byte_lists`. -/
theorem alpha_lists_all_bytes (n : Nat) : alpha_lists all_bytes n = byte_lists n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show all_bytes.flatMap (fun b => (alpha_lists all_bytes n).map (fun l => b :: l))
        = byte_lists (n + 1)
    rw [ih]
    rfl

/-- There are `alpha.length ^ n` of them. -/
theorem alpha_lists_length (alpha : List byte) (n : Nat) :
    (alpha_lists alpha n).length = alpha.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l))).length
        = alpha.length ^ (n + 1)
    have hfm : (alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l))).length
        = alpha.length * alpha.length ^ n := by
      apply length_flat_map_const
      intro b _
      rw [List.length_map, ih]
    rw [hfm, Nat.pow_succ]
    exact Nat.mul_comm _ _

/-- None is missing: a payload over the alphabet is in the slice of its
own length. -/
theorem alpha_lists_complete (alpha : List byte) (l : List byte) :
    alpha_only alpha l = true → l ∈ alpha_lists alpha l.length := by
  induction l with
  | nil => intro _; simp [alpha_lists]
  | cons b l ih =>
    intro hl
    unfold alpha_only at hl
    rw [List.all_cons, Bool.and_eq_true] at hl
    obtain ⟨hb, hl2⟩ := hl
    show (b :: l) ∈ alpha.flatMap (fun c => (alpha_lists alpha l.length).map (fun s => c :: s))
    refine List.mem_flatMap.mpr ⟨b, (alpha_memb_In alpha b).mp hb, ?_⟩
    exact List.mem_map.mpr ⟨l, ih hl2, rfl⟩

/-- Everything in the slice has length `n`. -/
theorem alpha_lists_In_length (alpha : List byte) (n : Nat) (s : List byte) :
    s ∈ alpha_lists alpha n → s.length = n := by
  induction n generalizing s with
  | zero =>
    intro hs
    simp only [alpha_lists, List.mem_singleton] at hs
    subst hs
    rfl
  | succ n ih =>
    intro hs
    simp only [alpha_lists, List.mem_flatMap, List.mem_map] at hs
    obtain ⟨_, _, s', hs', rfl⟩ := hs
    rw [List.length_cons, ih s' hs']

/-- Everything in the slice is over the alphabet. -/
theorem alpha_lists_In_alpha (alpha : List byte) (n : Nat) (s : List byte) :
    s ∈ alpha_lists alpha n → alpha_only alpha s = true := by
  induction n generalizing s with
  | zero =>
    intro hs
    simp only [alpha_lists, List.mem_singleton] at hs
    subst hs
    rfl
  | succ n ih =>
    intro hs
    simp only [alpha_lists, List.mem_flatMap, List.mem_map] at hs
    obtain ⟨b, hb, s', hs', rfl⟩ := hs
    unfold alpha_only
    rw [List.all_cons, Bool.and_eq_true]
    exact ⟨(alpha_memb_In alpha b).mpr hb, ih s' hs'⟩

/-- The slice repeats nothing when the alphabet repeats nothing. Distinct
first bytes give disjoint blocks, and inside a block `cons` is injective. -/
theorem alpha_lists_nodup (alpha : List byte) :
    alpha.Nodup → ∀ n, (alpha_lists alpha n).Nodup := by
  intro hnd n
  induction n with
  | zero => simp [alpha_lists]
  | succ n ih =>
    show (alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l))).Nodup
    apply NoDup_flat_map
    · exact hnd
    · intro b _
      apply NoDup_map_inj
      · intro x y _ _ heq
        injection heq with _ hxy
      · exact ih
    · intro x y bs _ _ hx hy
      obtain ⟨lx, _, hlx⟩ := List.mem_map.mp hx
      obtain ⟨ly, _, hly⟩ := List.mem_map.mp hy
      have hcons : x :: lx = y :: ly := by rw [hlx, hly]
      injection hcons with hxy _

/-! ## A full slice weighs `p (1 - p) ^ n` -/

/-- A power of a count is the count's power. -/
theorem Qnat_pow (m n : Nat) : Qnat (m ^ n) = Qpow (Qnat m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Qnat_mult, ih, Qpow_succ]
    exact Rat.mul_comm _ _

/-- The count of a full slice times the weight of one of its payloads is
`p (1 - p) ^ n`: the size and the ratio's `n`th power cancel. -/
theorem alpha_slice_total (alpha : List byte) (p : Rat) (n : Nat) :
    alpha ≠ [] →
    Qnat (alpha.length ^ n) * alpha_geo_point alpha p n = p * Qpow (1 - p) n := by
  intro hne
  have h1 : Qpow (Qnat alpha.length) n * Qpow (alpha_ratio alpha) n = 1 := by
    rw [← Qpow_mult, Qpow_Qeq _ 1 n (alpha_ratio_cancel alpha hne), Qpow_1]
  have mlc : ∀ a b c : Rat, a * (b * c) = b * (a * c) := by
    intro a b c
    rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc]
  rw [Qnat_pow]
  show Qpow (Qnat alpha.length) n * (p * Qpow ((1 - p) * alpha_ratio alpha) n)
      = p * Qpow (1 - p) n
  rw [Qpow_mult]
  calc Qpow (Qnat alpha.length) n * (p * (Qpow (1 - p) n * Qpow (alpha_ratio alpha) n))
      = Qpow (Qnat alpha.length) n * Qpow (alpha_ratio alpha) n * (p * Qpow (1 - p) n) := by
        simp only [Rat.mul_comm, mlc]
    _ = 1 * (p * Qpow (1 - p) n) := by rw [h1]
    _ = p * Qpow (1 - p) n := Rat.one_mul _

/-- The whole slice sums to `p (1 - p) ^ n`. -/
theorem alpha_lists_sum (alpha : List byte) (p : Rat) (n : Nat) :
    alpha ≠ [] →
    qsum (fun s => alpha_geo_point alpha p s.length) (alpha_lists alpha n)
      = p * Qpow (1 - p) n := by
  intro hne
  have hc : qsum (fun s => alpha_geo_point alpha p s.length) (alpha_lists alpha n)
      = Qnat (alpha_lists alpha n).length * alpha_geo_point alpha p n := by
    apply qsum_const
    intro s hs
    rw [alpha_lists_In_length alpha n s hs]
  rw [hc, alpha_lists_length]
  exact alpha_slice_total alpha p n hne

/-! ## The length-bounded prefix family over the alphabet -/

/-- Every payload over the alphabet shorter than `k`: `short_inputs` with
`alpha_lists` in place of `byte_lists`. -/
def alpha_short_inputs (alpha : List byte) : Nat → List (List byte)
  | 0 => []
  | k + 1 => alpha_lists alpha k ++ alpha_short_inputs alpha k

/-- At the full alphabet this is `short_inputs`. -/
theorem alpha_short_inputs_all_bytes (k : Nat) :
    alpha_short_inputs all_bytes k = short_inputs k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show alpha_lists all_bytes k ++ alpha_short_inputs all_bytes k = short_inputs (k + 1)
    rw [ih, alpha_lists_all_bytes]
    rfl

/-- Everything in it is shorter than `k`. -/
theorem alpha_short_inputs_In_length (alpha : List byte) (k : Nat) (s : List byte) :
    s ∈ alpha_short_inputs alpha k → s.length < k := by
  induction k generalizing s with
  | zero =>
    intro hs
    simp [alpha_short_inputs] at hs
  | succ k ih =>
    intro hs
    rw [show alpha_short_inputs alpha (k + 1)
          = alpha_lists alpha k ++ alpha_short_inputs alpha k from rfl,
        List.mem_append] at hs
    rcases hs with hs | hs
    · rw [alpha_lists_In_length alpha k s hs]
      omega
    · have := ih s hs
      omega

/-- Everything in it is over the alphabet. -/
theorem alpha_short_inputs_In_alpha (alpha : List byte) (k : Nat) (s : List byte) :
    s ∈ alpha_short_inputs alpha k → alpha_only alpha s = true := by
  induction k generalizing s with
  | zero =>
    intro hs
    simp [alpha_short_inputs] at hs
  | succ k ih =>
    intro hs
    rw [show alpha_short_inputs alpha (k + 1)
          = alpha_lists alpha k ++ alpha_short_inputs alpha k from rfl,
        List.mem_append] at hs
    rcases hs with hs | hs
    · exact alpha_lists_In_alpha alpha k s hs
    · exact ih s hs

/-- Nothing short and over the alphabet is missing. -/
theorem alpha_short_inputs_complete (alpha : List byte) (k : Nat) (s : List byte) :
    alpha_only alpha s = true → s.length < k → s ∈ alpha_short_inputs alpha k := by
  induction k generalizing s with
  | zero =>
    intro _ hlen
    omega
  | succ k ih =>
    intro ha hlen
    show s ∈ alpha_lists alpha k ++ alpha_short_inputs alpha k
    rw [List.mem_append]
    by_cases heq : s.length = k
    · left
      rw [← heq]
      exact alpha_lists_complete alpha s ha
    · right
      exact ih s ha (by omega)

/-- It repeats nothing when the alphabet repeats nothing: the two parts
hold payloads of different lengths. -/
theorem alpha_short_inputs_nodup (alpha : List byte) :
    alpha.Nodup → ∀ k, (alpha_short_inputs alpha k).Nodup := by
  intro hnd k
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
    show (alpha_lists alpha k ++ alpha_short_inputs alpha k).Nodup
    refine List.nodup_append.mpr ⟨alpha_lists_nodup alpha hnd k, ih, ?_⟩
    intro a ha b hb hab
    subst hab
    have h1 := alpha_lists_In_length alpha k a ha
    have h2 := alpha_short_inputs_In_length alpha k a hb
    omega

/-- The whole bounded family sums to the geometric partial sum. -/
theorem alpha_short_inputs_sum (alpha : List byte) (p : Rat) (k : Nat) :
    alpha ≠ [] →
    qsum (fun s => alpha_geo_point alpha p s.length) (alpha_short_inputs alpha k)
      = geo_prefix_sum p k := by
  intro hne
  induction k with
  | zero => rfl
  | succ k ih =>
    show qsum (fun s => alpha_geo_point alpha p s.length)
        (alpha_lists alpha k ++ alpha_short_inputs alpha k) = geo_prefix_sum p (k + 1)
    rw [qsum_app, ih, alpha_lists_sum alpha p k hne]
    rfl

/-! ## The cylinder enumeration over the alphabet -/

/-- Every payload that extends `bs` by at most `N` bytes of the alphabet:
`bytes_cyl` with `alpha` in place of `all_bytes`. -/
def alpha_cyl (alpha : List byte) : List byte → Nat → List (List byte)
  | bs, 0 => [bs]
  | bs, N + 1 => bs :: alpha.flatMap (fun b => alpha_cyl alpha (bs ++ [b]) N)

/-- At the full alphabet this is `bytes_cyl`. -/
theorem alpha_cyl_all_bytes (N : Nat) (bs : List byte) :
    alpha_cyl all_bytes bs N = bytes_cyl bs N := by
  induction N generalizing bs with
  | zero => rfl
  | succ N ih =>
    show bs :: all_bytes.flatMap (fun b => alpha_cyl all_bytes (bs ++ [b]) N)
        = bytes_cyl bs (N + 1)
    have hf : (fun b => alpha_cyl all_bytes (bs ++ [b]) N)
        = (fun b => bytes_cyl (bs ++ [b]) N) := by
      funext b
      exact ih (bs ++ [b])
    rw [hf]
    rfl

/-- Every short extension of `bs` over the alphabet is in the cylinder. -/
theorem alpha_cyl_In (alpha : List byte) (N : Nat) (bs ext : List byte) :
    alpha_only alpha ext = true → ext.length ≤ N → (bs ++ ext) ∈ alpha_cyl alpha bs N := by
  induction N generalizing bs ext with
  | zero =>
    intro _ hlen
    cases ext with
    | nil =>
      rw [List.append_nil]
      simp [alpha_cyl]
    | cons b ext => simp at hlen
  | succ N ih =>
    intro hext hlen
    cases ext with
    | nil =>
      rw [List.append_nil]
      show bs ∈ bs :: alpha.flatMap (fun b => alpha_cyl alpha (bs ++ [b]) N)
      exact List.mem_cons_self
    | cons b ext =>
      unfold alpha_only at hext
      rw [List.all_cons, Bool.and_eq_true] at hext
      obtain ⟨hb, hext'⟩ := hext
      show (bs ++ b :: ext) ∈ bs :: alpha.flatMap (fun c => alpha_cyl alpha (bs ++ [c]) N)
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b, (alpha_memb_In alpha b).mp hb, ?_⟩)
      have happ : bs ++ b :: ext = (bs ++ [b]) ++ ext := by
        rw [List.append_assoc]
        rfl
      rw [happ]
      refine ih (bs ++ [b]) ext hext' ?_
      simp at hlen
      omega

/-- A cylinder never weighs more than its own prefix's mass. A cylinder of
depth `N + 1` is its own stopping payload plus `alpha.length` cylinders one
byte deeper, and `p + alpha.length * (1 - p) * alpha_ratio alpha` is
exactly 1 by `alpha_ratio_cancel`. -/
theorem alpha_cyl_sum_le (alpha : List byte) (p : Rat) :
    alpha ≠ [] → 0 ≤ p → p ≤ 1 →
    ∀ (N : Nat) (bs : List byte),
      qsum (fun s => alpha_geo_point alpha p s.length) (alpha_cyl alpha bs N)
        ≤ alpha_geo_mass alpha p bs.length := by
  intro hne _ hp1 N
  induction N with
  | zero =>
    intro bs
    show qsum (fun s => alpha_geo_point alpha p s.length) [bs]
        ≤ alpha_geo_mass alpha p bs.length
    rw [qsum_cons, qsum_nil, Rat.add_zero]
    exact alpha_geo_point_le_mass alpha p bs.length hp1
  | succ N ih =>
    intro bs
    show qsum (fun s => alpha_geo_point alpha p s.length)
        (bs :: alpha.flatMap (fun b => alpha_cyl alpha (bs ++ [b]) N))
        ≤ alpha_geo_mass alpha p bs.length
    rw [qsum_cons]
    have hblk : qsum (fun s => alpha_geo_point alpha p s.length)
        (alpha.flatMap (fun b => alpha_cyl alpha (bs ++ [b]) N))
        ≤ Qnat alpha.length * alpha_geo_mass alpha p (bs.length + 1) := by
      apply qsum_flat_map_const_le
      intro b _
      have h := ih (bs ++ [b])
      have hlen : (bs ++ [b]).length = bs.length + 1 := by simp
      rw [hlen] at h
      exact h
    have mlc : ∀ a b c : Rat, a * (b * c) = b * (a * c) := by
      intro a b c
      rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc]
    have key : alpha_geo_point alpha p bs.length
        + Qnat alpha.length * alpha_geo_mass alpha p (bs.length + 1)
        = alpha_geo_mass alpha p bs.length := by
      show p * Qpow ((1 - p) * alpha_ratio alpha) bs.length
          + Qnat alpha.length * Qpow ((1 - p) * alpha_ratio alpha) (bs.length + 1)
          = Qpow ((1 - p) * alpha_ratio alpha) bs.length
      rw [Qpow_succ]
      calc p * Qpow ((1 - p) * alpha_ratio alpha) bs.length
            + Qnat alpha.length
              * ((1 - p) * alpha_ratio alpha * Qpow ((1 - p) * alpha_ratio alpha) bs.length)
          = p * Qpow ((1 - p) * alpha_ratio alpha) bs.length
            + Qnat alpha.length * alpha_ratio alpha
              * ((1 - p) * Qpow ((1 - p) * alpha_ratio alpha) bs.length) := by
            simp only [Rat.mul_assoc, mlc]
        _ = p * Qpow ((1 - p) * alpha_ratio alpha) bs.length
            + 1 * ((1 - p) * Qpow ((1 - p) * alpha_ratio alpha) bs.length) := by
            rw [alpha_ratio_cancel alpha hne]
        _ = p * Qpow ((1 - p) * alpha_ratio alpha) bs.length
            + (1 - p) * Qpow ((1 - p) * alpha_ratio alpha) bs.length := by
            rw [Rat.one_mul]
        _ = (p + (1 - p)) * Qpow ((1 - p) * alpha_ratio alpha) bs.length :=
            (Rat.add_mul p (1 - p) _).symm
        _ = 1 * Qpow ((1 - p) * alpha_ratio alpha) bs.length := by
            rw [Rat.add_comm p (1 - p), Rat.sub_add_cancel]
        _ = Qpow ((1 - p) * alpha_ratio alpha) bs.length := Rat.one_mul _
    exact Rat.le_trans (Rat.add_le_add_left.mpr hblk) (Qle_of_Qeq _ _ key)

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
