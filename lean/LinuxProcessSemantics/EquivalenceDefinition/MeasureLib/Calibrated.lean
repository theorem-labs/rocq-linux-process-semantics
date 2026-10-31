-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdinVarying

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058

# EquivalenceDefinition.MeasureLib.Calibrated — the calibrated mixture

This file holds `theories/EquivalenceDefinition/MeasureLib.v` lines 7101-8095:
the calibrated mixture of the two base families, the two constants of the
environment coordinate with the pins that say how free they are, and the
`fs_file` / `file_core` pair that addresses one file inside a core's file
system.

No new combinator appears here.  The mixture is `cd_scale` twice and
`cd_mix2` once, at the shares `15 / 16` on the component that fixes an
environment and `1 / 16` on the component that varies it.  The stop weight
`p_stop` stays a parameter, because a task configuration picks it per
binary.

Rocq `Qeq` is `=` on `Rat`, as `Measure.lean`'s header says.  Closed
rational comparisons are closed with `decide +kernel`, the way
`Measure.lean` closes them; open rational rearrangements are closed with
`grind`, which has `Rat` as an ordered field.
-/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## The calibrated mixture: most of the mass on standard input alone, a
sixteenth on the environment -/

/-- The share the environment-varying component carries. -/
def calibrated_lambda : Rat := 1 / 16

/-- The share the standard-input-only component carries.  It is written as
its own numeral rather than as `1 - calibrated_lambda`, so that the two
shares summing to `1` is a claim and `calibrated_mixture_mass_is_one` is
where it is checked. -/
def calibrated_co_lambda : Rat := 15 / 16

/-- The entry-count parameter of the environment coordinate: a mean of four
environment entries. -/
def calibrated_r : Rat := 1 / 5

/-- The entry-length parameter of the environment coordinate: a mean entry
length of thirty-two, the shape of a `NAME=value` string. -/
def calibrated_q : Rat := 1 / 33

/-- The environment-varying share is nonnegative. -/
theorem calibrated_lambda_nonneg : 0 ≤ calibrated_lambda := by decide +kernel

/-- The standard-input-only share is nonnegative. -/
theorem calibrated_co_lambda_nonneg : 0 ≤ calibrated_co_lambda := by decide +kernel

/-- The entry-count parameter is nonnegative. -/
theorem calibrated_r_nonneg : 0 ≤ calibrated_r := by decide +kernel

/-- The entry-count parameter is at most one. -/
theorem calibrated_r_le_1 : calibrated_r ≤ 1 := by decide +kernel

/-- The entry-length parameter is nonnegative. -/
theorem calibrated_q_nonneg : 0 ≤ calibrated_q := by decide +kernel

/-- The entry-length parameter is at most one. -/
theorem calibrated_q_le_1 : calibrated_q ≤ 1 := by decide +kernel

/-- The composition a task configuration ships: `15 / 16` of the family
that fixes the environment `envp` and varies standard input, plus `1 / 16`
of the family that varies the launch-time environment as well.  Both
components take the same argv and file system; the second takes no envp at
all, which is the whole difference between them. -/
def calibrated_mixture (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  cd_mix2
    (cd_scale calibrated_co_lambda calibrated_co_lambda_nonneg
      (stdin_geometric p argv envp fs Hp0 Hp1))
    (cd_scale calibrated_lambda calibrated_lambda_nonneg
      (stdin_envp_geometric p calibrated_r calibrated_q argv fs
        Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
        calibrated_q_nonneg calibrated_q_le_1))

/-- Both components declare `1`, so the mixture declares `15 / 16` of one
plus `1 / 16` of the other, and that is `1`.  The declared masses are
written by the two constructors, so nothing here is decided by weighing
cores. -/
theorem calibrated_mixture_mass_is_one (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    cd_mass (calibrated_mixture p argv envp fs Hp0 Hp1) = 1 := by
  show calibrated_co_lambda * 1 + calibrated_lambda * 1 = 1
  decide +kernel

/-- The upper half of the certificate pair, for the mixture itself and not
only for its components.  It composes: each component has its own
whole-space upper certificate, `cd_scale_bound_mass` carries one through a
scaling and `cd_mix2_bound_mass` adds two on the same list, and
`calibrated_mixture_mass_is_one` reads the composed mass as `1`. -/
theorem calibrated_mixture_mass_upper (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l ≤ 1 := by
  intro Hnd
  have hA := cd_scale_bound_mass calibrated_co_lambda calibrated_co_lambda_nonneg
    (stdin_geometric p argv envp fs Hp0 Hp1) l
    (stdin_geometric_mass_upper p argv envp fs Hp0 Hp1 l Hnd)
  have hB := cd_scale_bound_mass calibrated_lambda calibrated_lambda_nonneg
    (stdin_envp_geometric p calibrated_r calibrated_q argv fs Hp0 Hp1
      calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1) l
    (stdin_envp_geometric_mass_upper p calibrated_r calibrated_q argv fs Hp0 Hp1
      calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1 l Hnd)
  exact Rat.le_trans (cd_mix2_bound_mass _ _ l hA hB)
    (Qle_of_Qeq _ _ (calibrated_mixture_mass_is_one p argv envp fs Hp0 Hp1))

/-! ## The lower half: one list both components can be certified on -/

/-- The shared witness, read from the environment-varying component's side.
`envp_geo_lower_witness` enumerates (environment, standard input) pairs, and
the standard-input-only component weighs a core of that list only where the
core's environment is the one it fixes.  So the list contains that
component's own witness family as a sublist, provided the fixed environment
is reached by the two depths: fewer entries than `M`, every entry shorter
than `L`.  `envps_upto_complete` is what puts it there, and
`qsum_core_incl_le` is the step from the sublist's exact sum to the whole
list's. -/
theorem stdin_geometric_on_envp_geo_lower_witness (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (M L k : Nat) :
    envp.length < M → (∀ e, e ∈ envp → e.length < L) →
    1 - Qpow (1 - p) k
      ≤ core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
          (envp_geo_lower_witness argv fs M L k) := by
  intro HM HL
  rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness]
  have hnonneg : ∀ c, 0 ≤ geo_weight p argv envp fs c :=
    geo_weight_nonneg p argv envp fs Hp0 Hp1
  have hnodup : ((short_inputs k).map (FinCore.mkFinCore argv envp fs)).Nodup := by
    rw [← map_fin_core_geo_lower_witness argv envp fs k]
    exact geo_lower_witness_nodup argv envp fs k
  have hincl : (short_inputs k).map (FinCore.mkFinCore argv envp fs) ⊆
      envp_stdin_product argv fs (envps_upto L M) (short_inputs k) := by
    intro c hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    exact In_envp_stdin_product argv fs (envps_upto L M) (short_inputs k) envp s
      (envps_upto_complete L M envp HM HL) hs
  have hstep := qsum_core_incl_le (geo_weight p argv envp fs)
    ((short_inputs k).map (FinCore.mkFinCore argv envp fs))
    (envp_stdin_product argv fs (envps_upto L M) (short_inputs k))
    hnonneg hnodup hincl
  have hsmall : qsum (geo_weight p argv envp fs)
      ((short_inputs k).map (FinCore.mkFinCore argv envp fs)) = 1 - Qpow (1 - p) k := by
    rw [qsum_short_inputs, geo_prefix_sum_closed]
  rw [hsmall] at hstep
  exact hstep

/-- The mixture's lower certificate, at any two nonnegative shares.  It is
stated of `cd_mix2` of two `cd_scale`s and not of `calibrated_mixture`,
because nothing in the argument turns on the calibration constants: the
shares `a` and `b` are arbitrary and are not required to sum to `1`.

The margin is split by the shares: each component is certified to
`eps / (a + b + 1)`, and `a + b` of that is at most `eps` whatever the
shares are.  The `+ 1` makes the division unconditional and costs nothing.

The depths are chosen once, by `envp_stdin_depths_above`, with floors the
fixed environment asks for: one past its entry count, one past its longest
entry.  After that choice the environment-varying component is evaluated on
the list exactly and the standard-input-only component is certified on the
same list from its standard-input tail alone. -/
theorem stdin_envp_mix2_mass_lower_certificate (p r q a b : Rat)
    (Ha : 0 ≤ a) (Hb : 0 ≤ b) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (eps : Rat) :
    0 < p → 0 < r → 0 < q → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ cd_mass (cd_mix2
            (cd_scale a Ha (stdin_geometric p argv envp fs Hp0 Hp1))
            (cd_scale b Hb (stdin_envp_geometric p r q argv fs
              Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))) - eps
          ≤ core_sum
              (cd_weight (cd_mix2
                (cd_scale a Ha (stdin_geometric p argv envp fs Hp0 Hp1))
                (cd_scale b Hb (stdin_envp_geometric p r q argv fs
                  Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)))) l := by
  intro Hppos Hrpos Hqpos Heps
  have HS : (0 : Rat) < a + b + 1 := by grind
  have HSne : a + b + 1 ≠ 0 := by grind
  have Heps' : 0 < eps * (a + b + 1)⁻¹ := Rat.mul_pos Heps (Rat.inv_pos.mpr HS)
  obtain ⟨M, L, k, HM0, HL0, Hsum, Hk⟩ :=
    envp_stdin_depths_above p r q (eps * (a + b + 1)⁻¹) (envp.length + 1)
      (list_max (envp.map (fun e => e.length)) + 1) Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps'
  have HLe : ∀ e, e ∈ envp → e.length < L := by
    intro e He
    have Hmax : e.length ≤ list_max (envp.map (fun e' => e'.length)) :=
      list_max_ge (envp.map (fun e' => e'.length)) e.length (List.mem_map.mpr ⟨e, He, rfl⟩)
    omega
  have Hmono : ∀ x y : Rat, x ≤ y → 1 - y ≤ 1 - x := by
    intro x y h; grind
  have H1 : 1 - eps * (a + b + 1)⁻¹
      ≤ core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
          (envp_geo_lower_witness argv fs M L k) :=
    Rat.le_trans (Hmono _ _ Hk)
      (stdin_geometric_on_envp_geo_lower_witness p argv envp fs Hp0 Hp1 M L k
        (by omega) HLe)
  have H2 : 1 - eps * (a + b + 1)⁻¹
      ≤ core_sum (cd_weight (stdin_envp_geometric p r q argv fs
            Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) (envp_geo_lower_witness argv fs M L k) := by
    rw [(stdin_envp_geometric_mass_lower_witness p r q argv fs
      Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k).2]
    exact envp_stdin_margin_at_depths p r q (eps * (a + b + 1)⁻¹) M L k
      Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum
  have HAB : (a + b) * (a + b + 1)⁻¹ ≤ 1 := by
    have h1 : (a + b) * (a + b + 1)⁻¹ ≤ (a + b + 1) * (a + b + 1)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr HS))
    have h2 : (a + b + 1) * (a + b + 1)⁻¹ = 1 := Rat.mul_inv_cancel (a + b + 1) HSne
    grind
  have Hmar : (a + b) * (eps * (a + b + 1)⁻¹) ≤ eps := by
    have h3 : (a + b) * (a + b + 1)⁻¹ * eps ≤ 1 * eps :=
      Rat.mul_le_mul_of_nonneg_right HAB (Rat.le_of_lt Heps)
    grind
  have Hstep : ∀ e : Rat, (a + b) * e ≤ eps →
      a * 1 + b * 1 - eps ≤ a * (1 - e) + b * (1 - e) := by
    intro e he; grind
  refine ⟨envp_geo_lower_witness argv fs M L k,
    envp_geo_lower_witness_nodup argv fs M L k, ?_⟩
  have Hlow := cd_mix2_bound_lower
    (cd_scale a Ha (stdin_geometric p argv envp fs Hp0 Hp1))
    (cd_scale b Hb (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))
    (envp_geo_lower_witness argv fs M L k)
    (a * (1 - eps * (a + b + 1)⁻¹)) (b * (1 - eps * (a + b + 1)⁻¹))
    (cd_scale_bound_lower a Ha (stdin_geometric p argv envp fs Hp0 Hp1)
      (envp_geo_lower_witness argv fs M L k) (1 - eps * (a + b + 1)⁻¹) H1)
    (cd_scale_bound_lower b Hb
      (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
      (envp_geo_lower_witness argv fs M L k) (1 - eps * (a + b + 1)⁻¹) H2)
  exact Rat.le_trans (Hstep (eps * (a + b + 1)⁻¹) Hmar) Hlow

/-- The same certificate at the calibrated constants, which is the object a
task ships.  `calibrated_mixture` is the `cd_mix2` of two `cd_scale`s the
lemma above quantifies over, so the only work is exhibiting `0 < r` and
`0 < q` at the two numerals.  It is stated against `1` so that it pairs with
`calibrated_mixture_mass_upper` term for term. -/
theorem calibrated_mixture_mass_lower_certificate (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (eps : Rat) :
    0 < p → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ 1 - eps ≤ core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l := by
  intro Hppos Heps
  have Hrpos : 0 < calibrated_r := by decide +kernel
  have Hqpos : 0 < calibrated_q := by decide +kernel
  obtain ⟨l, Hnd, Hle⟩ := stdin_envp_mix2_mass_lower_certificate p calibrated_r
    calibrated_q calibrated_co_lambda calibrated_lambda
    calibrated_co_lambda_nonneg calibrated_lambda_nonneg argv envp fs Hp0 Hp1
    calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1
    eps Hppos Hrpos Hqpos Heps
  refine ⟨l, Hnd, ?_⟩
  have Hmass : cd_mass (calibrated_mixture p argv envp fs Hp0 Hp1) - eps = 1 - eps := by
    rw [calibrated_mixture_mass_is_one p argv envp fs Hp0 Hp1]
  rw [← Hmass]
  exact Hle

/-! ## Where the mixture's own hypotheses are spent -/

/-- Both depth constraints are load-bearing, and the failure is total.  At
depths that do not reach the fixed environment the shared list carries none
of the standard-input-only component's weight: every core of the product
draws its environment from `envps_upto L M`, and the component weighs every
environment but its own zero.  Either depth alone loses it, which is why the
hypothesis is a disjunction.  The second conjunct is the gap of one half the
file's other degeneracy pins use: the declared mass is still `1`, so a list
weighing zero is within no margin under one. -/
theorem stdin_geometric_on_envp_geo_lower_witness_needs_the_depths (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (M L k : Nat) :
    (M ≤ envp.length ∨ ∃ e, e ∈ envp ∧ L ≤ e.length) →
    core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
        (envp_geo_lower_witness argv fs M L k) = 0
    ∧ ¬ (cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) - 1 / 2 ≤ 0) := by
  intro Hdeep
  have Hout : envp ∉ envps_upto L M := by
    intro Hin
    rcases Hdeep with Hlen | ⟨e, He, Hle⟩
    · have h := envps_upto_In_length L M envp Hin
      omega
    · have h := envps_upto_In_entry L M envp e Hin He
      omega
  refine ⟨?_, ?_⟩
  · rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness]
    have hz : ∀ c ∈ envp_stdin_product argv fs (envps_upto L M) (short_inputs k),
        cd_weight (stdin_geometric p argv envp fs Hp0 Hp1) c = 0 := by
      intro c hc
      simp only [envp_stdin_product, List.mem_flatMap, List.mem_map] at hc
      obtain ⟨es, hes, s, _, rfl⟩ := hc
      refine geo_weight_off_envp_zero p argv envp fs
        (FinCore.mkFinCore argv es fs s) ?_
      intro Heq
      have hes' : es = envp := Heq
      exact Hout (hes' ▸ hes)
    rw [qsum_ext (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
      (fun _ => (0 : Rat)) _ hz, qsum_zero]
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    decide +kernel

/-- The two shares force the standard-input-only component to carry weight.
The environment-varying component carries a share of `1 / 16` and no
admissible list collects more than its declared `1`, so it contributes at
most `1 / 16` however the list is chosen.  At any margin under `15 / 16` the
rest has to come from the other component.  The statement is about the two
shares alone and about neither family. -/
theorem calibrated_shares_force_stdin (S1 S2 eps : Rat) :
    S2 ≤ 1 → eps < 15 / 16 → 1 - eps ≤ (15 / 16) * S1 + (1 / 16) * S2 → 0 < S1 := by
  intro HS21 Heps Hle
  grind

/-- The threshold has no slack: at `eps` exactly `15 / 16` the lemma above
is false.  At `S1 = 0` and `S2 = 1` the hypothesis holds with equality,
`1 - 15 / 16` and `1 / 16` of `1` being the same number, while the
conclusion asks for `0 < 0`. -/
theorem calibrated_shares_force_stdin_needs_the_threshold :
    ∃ S1 S2 eps : Rat,
      S2 ≤ 1
      ∧ ¬ (eps < 15 / 16)
      ∧ 1 - eps ≤ (15 / 16) * S1 + (1 / 16) * S2
      ∧ ¬ (0 < S1) :=
  ⟨0, 1, 15 / 16, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- The mixture's sum read as the two shares of its components' sums:
`core_sum_plus` and `core_sum_scale` applied where `cd_mix2` and `cd_scale`
left them.  The pin below is the only place in the file that needs the
mixture taken apart again. -/
theorem calibrated_mixture_sum_split (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput) :
    core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l
      = calibrated_co_lambda
          * core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
        + calibrated_lambda
          * core_sum (cd_weight (stdin_envp_geometric p calibrated_r calibrated_q
              argv fs Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
              calibrated_q_nonneg calibrated_q_le_1)) l :=
  calc core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l
      = core_sum (fun c =>
          calibrated_co_lambda * cd_weight (stdin_geometric p argv envp fs Hp0 Hp1) c
          + calibrated_lambda * cd_weight (stdin_envp_geometric p calibrated_r
              calibrated_q argv fs Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
              calibrated_q_nonneg calibrated_q_le_1) c) l := rfl
    _ = core_sum (fun c =>
            calibrated_co_lambda * cd_weight (stdin_geometric p argv envp fs Hp0 Hp1) c) l
        + core_sum (fun c =>
            calibrated_lambda * cd_weight (stdin_envp_geometric p calibrated_r
              calibrated_q argv fs Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
              calibrated_q_nonneg calibrated_q_le_1) c) l := core_sum_plus _ _ l
    _ = calibrated_co_lambda
          * core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
        + calibrated_lambda
          * core_sum (cd_weight (stdin_envp_geometric p calibrated_r calibrated_q
              argv fs Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
              calibrated_q_nonneg calibrated_q_le_1)) l := by
            rw [core_sum_scale, core_sum_scale]

/-- A list that meets the mixture's lower certificate at a margin under
`15 / 16` carries weight of the standard-input-only component, and names a
core that component weighs positively.  The environment-varying component
cannot supply `1 - eps` by itself: it carries `1 / 16` and collects at most
its declared `1`. -/
theorem calibrated_mixture_mass_lower_certificate_needs_the_stdin_component
    (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p)
    (Hp1 : p ≤ 1) (eps : Rat) (l : List FinProcInput) :
    (l.map fin_core).Nodup → eps < 15 / 16 →
    1 - eps ≤ core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l →
    0 < core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
    ∧ ∃ c, c ∈ l.map fin_core
        ∧ 0 < cd_weight (stdin_geometric p argv envp fs Hp0 Hp1) c := by
  intro Hnd Heps Hle
  rw [calibrated_mixture_sum_split p argv envp fs Hp0 Hp1 l] at Hle
  have Hup := stdin_envp_geometric_mass_upper p calibrated_r calibrated_q argv fs
    Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg
    calibrated_q_le_1 l Hnd
  have Hpos : 0 < core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l :=
    calibrated_shares_force_stdin _ _ eps Hup Heps Hle
  refine ⟨Hpos, ?_⟩
  rw [core_sum_map_fin_core] at Hpos
  exact qsum_positive_member (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
    (l.map fin_core) (cd_nonneg (stdin_geometric p argv envp fs Hp0 Hp1)) Hpos

/-- The hypothesis of that pin is met, so the two compose into an
unconditional existence claim: at every `p_stop > 0` and every margin in
`(0, 15 / 16)` there is an admissible list within the margin that names a
core the standard-input-only component weighs positively.  The empty list
does not satisfy it, and neither does any list of cores the mixture weighs
zero. -/
theorem calibrated_mixture_mass_lower_certificate_names_a_stdin_core (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (eps : Rat) :
    0 < p → 0 < eps → eps < 15 / 16 →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ 1 - eps ≤ core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l
      ∧ ∃ c, c ∈ l.map fin_core
          ∧ 0 < cd_weight (stdin_geometric p argv envp fs Hp0 Hp1) c := by
  intro Hppos Heps Hsmall
  obtain ⟨l, Hnd, Hle⟩ :=
    calibrated_mixture_mass_lower_certificate p argv envp fs Hp0 Hp1 eps Hppos Heps
  exact ⟨l, Hnd, Hle,
    (calibrated_mixture_mass_lower_certificate_needs_the_stdin_component p argv envp
      fs Hp0 Hp1 eps l Hnd Hsmall Hle).2⟩

/-- The shallowest environment witness names exactly one core.
`envps_upto 1 1` is the single environment `[]` and `short_inputs 1` the
single standard input `[]`, so their product is a one-element list. -/
theorem envp_stdin_product_at_depth_one :
    envp_stdin_product [] [] (envps_upto 1 1) (short_inputs 1)
      = [FinCore.mkFinCore [] [] [] []] := by
  rfl

/-- The threshold is load-bearing at the distribution too, and it needs a
strictly larger margin than the arithmetic does.  This mixture fixes the
one-entry environment `[Z_to_bv 8 65]` for its standard-input-only
component, and the list is the shallowest environment witness, whose single
core has the environment `[]`.  So that component weighs the list zero.  The
mixture collects `1 / 16` of `1 / 5` of `1 / 2`, namely `1 / 160`, and
`1 - 159 / 160` is `1 / 160` as well: the certificate's conclusion is met
with equality by a list carrying none of the standard-input-only
component's weight. -/
theorem calibrated_mixture_mass_lower_certificate_needs_the_threshold
    (Hp0 : (0 : Rat) ≤ 1 / 2) (Hp1 : (1 : Rat) / 2 ≤ 1) :
    ((15 : Rat) / 16 < 159 / 160) ∧ ((159 : Rat) / 160 < 1)
    ∧ ((envp_geo_lower_witness [] [] 1 1 1).map fin_core).Nodup
    ∧ 1 - (159 : Rat) / 160
        ≤ core_sum
            (cd_weight (calibrated_mixture (1 / 2) [] [[Z_to_bv 8 65]] [] Hp0 Hp1))
            (envp_geo_lower_witness [] [] 1 1 1)
    ∧ core_sum
        (cd_weight (stdin_geometric (1 / 2) [] [[Z_to_bv 8 65]] [] Hp0 Hp1))
        (envp_geo_lower_witness [] [] 1 1 1) = 0 := by
  refine ⟨by decide +kernel, by decide +kernel,
    envp_geo_lower_witness_nodup [] [] 1 1 1, ?_, ?_⟩
  · rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness,
      envp_stdin_product_at_depth_one, qsum_cons, qsum_nil]
    show 1 - (159 : Rat) / 160
      ≤ calibrated_co_lambda
          * geo_weight (1 / 2) [] [[Z_to_bv 8 65]] [] (FinCore.mkFinCore [] [] [] [])
        + calibrated_lambda
          * envp_geo_weight (1 / 2) calibrated_r calibrated_q [] []
              (FinCore.mkFinCore [] [] [] []) + 0
    rw [geo_weight_off_envp_zero (1 / 2) [] [[Z_to_bv 8 65]] []
        (FinCore.mkFinCore [] [] [] []) (by decide),
      envp_geo_weight_match (1 / 2) calibrated_r calibrated_q [] [] [] []]
    decide +kernel
  · rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness,
      envp_stdin_product_at_depth_one, qsum_cons, qsum_nil]
    show geo_weight (1 / 2) [] [[Z_to_bv 8 65]] [] (FinCore.mkFinCore [] [] [] [])
      + 0 = 0
    rw [geo_weight_off_envp_zero (1 / 2) [] [[Z_to_bv 8 65]] []
      (FinCore.mkFinCore [] [] [] []) (by decide)]
    decide +kernel

/-- A positive stop weight is as load-bearing for the mixture as for either
component.  At `p_stop = 0` both components weigh every core zero, so
fifteen sixteenths of one plus a sixteenth of the other is zero on every
admissible list, while the declared mass is still `1`.
`calibrated_mixture_mass_upper` remains true here: an upper bound survives
the degeneracy, a lower one does not. -/
theorem calibrated_mixture_mass_lower_needs_positive (argv envp : List (List byte))
    (fs : Fs.Fs) :
    (∀ l : List FinProcInput,
        core_sum (cd_weight (calibrated_mixture 0 argv envp fs Rat.le_refl Qle_0_1)) l
          = 0)
    ∧ ¬ (cd_mass (calibrated_mixture 0 argv envp fs Rat.le_refl Qle_0_1) - 1 / 2
          ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    refine core_sum_zero_weight
      (cd_weight (calibrated_mixture 0 argv envp fs Rat.le_refl Qle_0_1)) l ?_
    intro c
    show calibrated_co_lambda * geo_weight 0 argv envp fs c
      + calibrated_lambda * envp_geo_weight 0 calibrated_r calibrated_q argv fs c = 0
    rw [geo_weight_zero_at_zero_p argv envp fs c,
      envp_geo_weight_zero_at_zero_p calibrated_r calibrated_q argv fs c]
    decide +kernel
  · show ¬ (calibrated_co_lambda * 1 + calibrated_lambda * 1 - 1 / 2 ≤ 0)
    decide +kernel

/-- The mixture inherits the bite, which is the reason for mixing rather
than replacing.  The standard-input-only component still weighs a
non-canonical environment zero; the mixture does not, because a sixteenth of
a positive number is positive. -/
theorem calibrated_mixture_envp_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 < p → p < 1 →
    cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) envp_example_named = 0
    ∧ 0 < cd_weight (calibrated_mixture p [] [] [] Hp0 Hp1) envp_example_named := by
  intro Hppos Hplt
  have Hne : envp_example_named.core_envp ≠ [] := by decide
  refine ⟨geo_weight_off_envp_zero p [] [] [] envp_example_named Hne, ?_⟩
  have Hgeo : geo_weight p [] [] [] (FinCore.mkFinCore [] [[Z_to_bv 8 65]] [] []) = 0 :=
    geo_weight_off_envp_zero p [] [] [] (FinCore.mkFinCore [] [[Z_to_bv 8 65]] [] [])
      (by decide)
  have Hep : 0 < envp_point calibrated_r calibrated_q [[Z_to_bv 8 65]] :=
    envp_point_pos calibrated_r calibrated_q [[Z_to_bv 8 65]]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have Hgp : 0 < geo_point p ([] : List byte).length := geo_point_pos p _ Hppos Hplt
  have Hprod : 0 < calibrated_lambda
      * (envp_point calibrated_r calibrated_q [[Z_to_bv 8 65]]
          * geo_point p ([] : List byte).length) :=
    Rat.mul_pos (by decide +kernel) (Rat.mul_pos Hep Hgp)
  show 0 < calibrated_co_lambda
      * geo_weight p [] [] [] (FinCore.mkFinCore [] [[Z_to_bv 8 65]] [] [])
    + calibrated_lambda
      * envp_geo_weight p calibrated_r calibrated_q [] []
          (FinCore.mkFinCore [] [[Z_to_bv 8 65]] [] [])
  rw [Hgeo, envp_geo_weight_match p calibrated_r calibrated_q [] []
    [[Z_to_bv 8 65]] []]
  grind

/-! ## The environment coordinate's two constants, pinned from both sides -/

/-- The same composition with the environment coordinate's pair left open.
`calibrated_lambda` is load-bearing, and
`calibrated_shares_force_stdin_needs_the_threshold` pins it; `calibrated_r`
and `calibrated_q` are a calibration, and every guarantee the mixture offers
holds at any pair in the open interval `(0, 1)`. -/
def calibrated_mixture_at (r q : Rat)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (p : Rat) (argv envp : List (List byte)) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  cd_mix2
    (cd_scale calibrated_co_lambda calibrated_co_lambda_nonneg
      (stdin_geometric p argv envp fs Hp0 Hp1))
    (cd_scale calibrated_lambda calibrated_lambda_nonneg
      (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))

/-- The calibrated mixture is that composition at the calibrated pair, by
conversion, so nothing below is a second object that could drift from the
one a task ships. -/
theorem calibrated_mixture_at_calibrated_r_q (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    calibrated_mixture p argv envp fs Hp0 Hp1
      = calibrated_mixture_at calibrated_r calibrated_q calibrated_r_nonneg
          calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1 p argv envp fs
          Hp0 Hp1 := by
  rfl

/-- The two constants lie in the open interval the lemmas below ask for. -/
theorem calibrated_r_q_in_the_open_interval :
    0 < calibrated_r ∧ calibrated_r < 1 ∧ 0 < calibrated_q ∧ calibrated_q < 1 := by
  decide +kernel

/-- The mass, at any admissible pair: the shares are what make it `1`, and
the environment coordinate's parameters do not enter. -/
theorem calibrated_mixture_at_mass_is_one (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    cd_mass (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1) = 1 := by
  show calibrated_co_lambda * 1 + calibrated_lambda * 1 = 1
  decide +kernel

/-- The upper certificate, at any admissible pair. -/
theorem calibrated_mixture_at_mass_upper (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (p : Rat) (argv envp : List (List byte))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs
      Hp0 Hp1)) l ≤ 1 := by
  intro Hnd
  have hA := cd_scale_bound_mass calibrated_co_lambda calibrated_co_lambda_nonneg
    (stdin_geometric p argv envp fs Hp0 Hp1) l
    (stdin_geometric_mass_upper p argv envp fs Hp0 Hp1 l Hnd)
  have hB := cd_scale_bound_mass calibrated_lambda calibrated_lambda_nonneg
    (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) l
    (stdin_envp_geometric_mass_upper p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 l Hnd)
  exact Rat.le_trans (cd_mix2_bound_mass _ _ l hA hB)
    (Qle_of_Qeq _ _ (calibrated_mixture_at_mass_is_one r q Hr0 Hr1 Hq0 Hq1 p argv
      envp fs Hp0 Hp1))

/-- The lower certificate, at any admissible pair.  It is the only guarantee
whose hypotheses mention `r` and `q` at all, and what it asks of them is
exactly positivity. -/
theorem calibrated_mixture_at_mass_lower_certificate (r q : Rat) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (p : Rat)
    (argv envp : List (List byte)) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (eps : Rat) :
    0 < p → 0 < r → 0 < q → 0 < eps →
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup
      ∧ 1 - eps ≤ core_sum (cd_weight (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p
          argv envp fs Hp0 Hp1)) l := by
  intro Hppos Hrpos Hqpos Heps
  obtain ⟨l, Hnd, Hle⟩ := stdin_envp_mix2_mass_lower_certificate p r q
    calibrated_co_lambda calibrated_lambda calibrated_co_lambda_nonneg
    calibrated_lambda_nonneg argv envp fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps
    Hppos Hrpos Hqpos Heps
  refine ⟨l, Hnd, ?_⟩
  have Hmass : cd_mass (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs
      Hp0 Hp1) - eps = 1 - eps := by
    rw [calibrated_mixture_at_mass_is_one r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1]
  rw [← Hmass]
  exact Hle

/-- The other direction: four endpoints, four collapses, all on the
standard-input-only component's own fixed environment `[]`, so that
component contributes nothing either and the number a reader sees is the
mixture's.  `r = 0` gives every environment weight zero; `r = 1` puts the
whole environment coordinate on the empty environment; `q = 0` charges any
entry an infinite price; and `q = 1` charges any non-empty entry one, which
is why the fourth conjunct asks for a non-empty entry and not a non-empty
environment. -/
theorem calibrated_mixture_at_endpoints_bite (p q r : Rat)
    (argv : List (List byte)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hq0 : 0 ≤ q)
    (Hq1 : q ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore) :
    c.core_envp ≠ [] →
    cd_weight (calibrated_mixture_at 0 q Rat.le_refl Qle_0_1 Hq0 Hq1 p argv [] []
        Hp0 Hp1) c = 0
    ∧ cd_weight (calibrated_mixture_at 1 q Qle_0_1 Rat.le_refl Hq0 Hq1 p argv [] []
        Hp0 Hp1) c = 0
    ∧ cd_weight (calibrated_mixture_at r 0 Hr0 Hr1 Rat.le_refl Qle_0_1 p argv [] []
        Hp0 Hp1) c = 0
    ∧ (∀ e, e ∈ c.core_envp → e ≠ [] →
        cd_weight (calibrated_mixture_at r 1 Hr0 Hr1 Qle_0_1 Rat.le_refl p argv []
          [] Hp0 Hp1) c = 0) := by
  intro Hne
  have Hgeo : geo_weight p argv [] [] c = 0 :=
    geo_weight_off_envp_zero p argv [] [] c Hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · show calibrated_co_lambda * geo_weight p argv [] [] c
      + calibrated_lambda * envp_geo_weight p 0 q argv [] c = 0
    rw [Hgeo, envp_geo_weight_zero_at_zero_r p q argv [] c]
    decide +kernel
  · show calibrated_co_lambda * geo_weight p argv [] [] c
      + calibrated_lambda * envp_geo_weight p 1 q argv [] c = 0
    rw [Hgeo, envp_geo_weight_collapses_at_one_r p q argv [] c, Hgeo]
    decide +kernel
  · show calibrated_co_lambda * geo_weight p argv [] [] c
      + calibrated_lambda * envp_geo_weight p r 0 argv [] c = 0
    rw [Hgeo, envp_geo_weight_zero_at_zero_q p r argv [] c Hne]
    decide +kernel
  · intro e Hin Hene
    show calibrated_co_lambda * geo_weight p argv [] [] c
      + calibrated_lambda * envp_geo_weight p r 1 argv [] c = 0
    rw [Hgeo, envp_geo_weight_zero_at_one_q p r argv [] c e Hin Hene]
    decide +kernel

/-! ## Addressing one file's contents inside a core's file system -/

/-- The contents of the file at `pth`, read out of a file system, with the
absent file reading as the empty one.  This is the coordinate the two file
families below vary, and collapsing "absent" onto "empty" is what makes it
total.  It costs nothing those families use: their cores all have the file
present, because `file_core` sets it. -/
def fs_file (pth : Fs.path) (fs : Fs.Fs) : List byte :=
  match Fs.fs_lookup fs pth with
  | some d => d
  | none => []

/-- Setting a path and reading it back gives what was set, at every file
system and with no sortedness hypothesis.  `Fs.fs_set` either inserts before
the first larger key, replaces an equal one, or recurses past a smaller one,
and in all three cases the entry it lands on is the one `Fs.fs_lookup` finds
first. -/
theorem fs_lookup_set (fs : Fs.Fs) (pth : Fs.path) (d : List byte) :
    Fs.fs_lookup (Fs.fs_set fs pth d) pth = some d := by
  induction fs with
  | nil => simp [Fs.fs_set, Fs.fs_lookup, Fs.path_eqb_refl]
  | cons hd r IH =>
    obtain ⟨q, e⟩ := hd
    simp only [Fs.fs_set]
    split
    · simp [Fs.fs_lookup, Fs.path_eqb_refl]
    · split
      · simp [Fs.fs_lookup, Fs.path_eqb_refl]
      · rename_i hne
        simp only [Fs.fs_lookup, hne, Bool.false_eq_true, ite_false]
        exact IH

/-- The coordinate read back off a file system the contents were set in. -/
theorem fs_file_set (fs0 : Fs.Fs) (pth : Fs.path) (d : List byte) :
    fs_file pth (Fs.fs_set fs0 pth d) = d := by
  unfold fs_file
  rw [fs_lookup_set fs0 pth d]

/-- The template: the core over fixed argv, envp, standard input and a fixed
base file system, carrying `d` as the contents of the file at `pth`.  It is
`FinCore.mkFinCore` with one field built rather than passed, and `d` is its
last argument on purpose: partially applied, it is the embedding
`List byte → FinCore` that every enumeration below maps over.  `fs0` need
not already contain `pth` and need not be sorted. -/
def file_core (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List byte) (d : List byte) : FinCore :=
  FinCore.mkFinCore argv envp (Fs.fs_set fs0 pth d) s

/-- The coordinate is readable off the template, which is what makes the
weight of the families below well defined. -/
theorem fs_file_file_core (argv envp : List (List byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s d : List byte) :
    fs_file pth (file_core argv envp fs0 pth s d).core_fs = d := by
  show fs_file pth (Fs.fs_set fs0 pth d) = d
  exact fs_file_set fs0 pth d

/-- So the template is injective in the contents.  An embedding that lost
information would make every length slice smaller than `256 ^ n` and every
witness family shorter than it claims. -/
theorem file_core_inj (argv envp : List (List byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s d1 d2 : List byte) :
    file_core argv envp fs0 pth s d1 = file_core argv envp fs0 pth s d2 → d1 = d2 := by
  intro Heq
  have h1 := fs_file_file_core argv envp fs0 pth s d1
  have h2 := fs_file_file_core argv envp fs0 pth s d2
  rw [Heq, h2] at h1
  exact h1.symm

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
