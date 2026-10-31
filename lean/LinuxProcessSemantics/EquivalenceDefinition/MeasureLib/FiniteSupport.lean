-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-!

# EquivalenceDefinition.MeasureLib.FiniteSupport — the finite-support combinator

Holds `theories/EquivalenceDefinition/MeasureLib.v` lines 1834-3005: the
distribution supported on a finite list of (core, weight) entries, the bound
it gives, the same bound refined to a subset of the cores, the embedding of a
core back into a record, the honesty certificates, the three non-vacuity
blocks (a worked example, duplicate cores summed, a negative entry refused),
the enumeration of the bytes and of the byte lists of a given length, the
sums over inclusions and filters, and the counting lemma.

Rocq `Qeq` is Lean `=`, as `Measure.lean`'s header sets out, so every Rocq
`==` statement below is an `=` statement.

`list_max` is new here and has no Rocq declaration of its own: Rocq's
`list_max_ge` reads the standard library's `List.list_max`, and Lean core
ships no twin of it, so the twin of that lemma needs the function written
down. `GeoStdin.lean`, `GeoStdinVarying.lean`, `Calibrated.lean` and
`FullSupport.lean` read it from here.

Every declaration of the span is ported. Nothing is `unported`. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MeasureLib

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Measure

/-- Two nonnegative rationals added on both sides of a `≤`. Lean core ships
`Rat.add_le_add_left` and `Rat.add_le_add_right` as one-sided `iff`s and not
the two-sided step Rocq calls `Qplus_le_compat`, so it is assembled once. -/
private theorem add_le_add_rat {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_left.mpr h2) (Rat.add_le_add_right.mpr h1)

/-! ## Combinator: finite support -/

/-- The weight an entry list gives a core: the total of the entries naming
it, SUMMED and not "the first one wins". A duplicate core is an author
writing the same core twice, and adding the two is the reading that keeps
`entries_mass` — a flat sum over the entries — equal to the total weight;
`dup_entries_weight_summed` and `dup_witness_attains_mass` below pin both
halves of that. -/
def entries_weight (entries : List (FinCore × Rat)) (c : FinCore) : Rat :=
  entries.foldr (fun e acc => core_indicator e.1 e.2 c + acc) 0

/-- The declared mass of an entry list: the sum of the entries' weights, with
no reference to which cores they name. -/
def entries_mass (entries : List (FinCore × Rat)) : Rat :=
  entries.foldr (fun e acc => e.2 + acc) 0

/-- The empty entry list declares no mass. -/
theorem entries_mass_nil : entries_mass [] = 0 := rfl

/-- The declared mass splits off its head entry. -/
theorem entries_mass_cons (e : FinCore × Rat) (entries : List (FinCore × Rat)) :
    entries_mass (e :: entries) = e.2 + entries_mass entries := rfl

/-- The declared mass of a nonnegative entry list is nonnegative. This is the
first half of `Measure.Distribution`'s `M_nonneg` for everything this library
builds out of `finite_support`: the mass is a fold of addition over the entry
weights, so the hypothesis the constructor already demands is the hypothesis
this needs, entry by entry. Nothing here ties the mass to the weight
function. -/
theorem entries_mass_nonneg (entries : List (FinCore × Rat)) :
    (∀ e, e ∈ entries → 0 ≤ e.2) → 0 ≤ entries_mass entries := by
  induction entries with
  | nil => intro _; exact Rat.le_refl
  | cons e entries ih =>
    intro hnn
    rw [entries_mass_cons]
    exact Qplus_nonneg _ _ (hnn e List.mem_cons_self)
      (ih (fun e' he' => hnn e' (List.mem_cons_of_mem _ he')))

/-- Splitting the head entry off a sum: the entry list's weight summed over
`cs` is the head's indicator summed over `cs` plus the tail's weight summed
over `cs`. `qsum_plus` does the work; the extensionality step is there only
because the fold's unfolding is a pointwise equation. -/
theorem qsum_entries_cons (e : FinCore × Rat) (entries : List (FinCore × Rat))
    (cs : List FinCore) :
    qsum (entries_weight (e :: entries)) cs
      = qsum (core_indicator e.1 e.2) cs + qsum (entries_weight entries) cs := by
  rw [← qsum_plus]
  exact qsum_ext _ _ _ (fun _ _ => rfl)

/-- Nonnegative entries give a nonnegative weight — the field `finite_support`
has to fill in. Induction on the entries, with the head's indicator
nonnegative by case analysis. -/
theorem entries_weight_nonneg (entries : List (FinCore × Rat)) :
    (∀ e, e ∈ entries → 0 ≤ e.2) → ∀ c, 0 ≤ entries_weight entries c := by
  induction entries with
  | nil => intro _ _; exact Rat.le_refl
  | cons e entries ih =>
    intro hnn c
    show 0 ≤ core_indicator e.1 e.2 c + entries_weight entries c
    refine Qplus_nonneg _ _ ?_
      (ih (fun e' he' => hnn e' (List.mem_cons_of_mem _ he')) c)
    unfold core_indicator
    by_cases h : e.1 = c
    · rw [ite_eq_left h]
      exact hnn e List.mem_cons_self
    · rw [ite_eq_right h]
      exact Rat.le_refl

/-- THE BOUND, over cores: any duplicate-free list of cores sums to at most
the entry list's declared mass. The induction is on the ENTRIES, not on the
list — the list is fixed and its duplicate-freedom is used once per entry, by
`qsum_indicator_le`. Nonnegativity is needed for entries the list does not
mention: they add nothing to the sum but their weight to the mass. -/
theorem entries_weight_qsum_le (entries : List (FinCore × Rat)) (cs : List FinCore) :
    (∀ e, e ∈ entries → 0 ≤ e.2) → cs.Nodup →
    qsum (entries_weight entries) cs ≤ entries_mass entries := by
  induction entries with
  | nil =>
    intro _ _
    rw [qsum_ext (entries_weight []) (fun _ => (0 : Rat)) cs (fun _ _ => rfl),
      qsum_zero, entries_mass_nil]
    exact Rat.le_refl
  | cons e entries ih =>
    intro hnn hnd
    rw [qsum_entries_cons, entries_mass_cons]
    exact add_le_add_rat
      (qsum_indicator_le e.1 e.2 cs (hnn e List.mem_cons_self) hnd)
      (ih (fun e' he' => hnn e' (List.mem_cons_of_mem _ he')) hnd)

/-- The distribution supported on a finite list of (core, weight) entries.
The nonnegativity proof is an argument, not a side condition discovered
later; `negative_entries_no_core_distribution` says what happens when the
entries cannot supply it. -/
def finite_support (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) : CoreDistribution :=
  { cd_weight := entries_weight entries
    cd_mass := entries_mass entries
    cd_nonneg := entries_weight_nonneg entries Hnn }

/-- `Measure.Distribution`'s `M_nonneg`, for a finite support: the proof
argument the constructor already took is exactly what the declared mass
needs, so an author who built the distribution owes nothing further. -/
theorem finite_support_mass_nonneg (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    0 ≤ cd_mass (finite_support entries Hnn) := by
  show 0 ≤ entries_mass entries
  exact entries_mass_nonneg entries Hnn

/-- Discharging `finite_support`'s proof argument BY COMPUTATION, which is
what a task author will want to do. An entry list written out as a literal
makes "every entry is nonnegative" a decidable fact about closed rationals,
and this bridge turns it into one boolean scan; see `example_entries_nonneg`
and `dup_cd` for the two styles. Without it every author writes the case
chain over the entry list by hand, and it grows with the list. -/
theorem entries_nonneg_of_forallb (entries : List (FinCore × Rat)) :
    entries.all (fun e => decide (0 ≤ e.2)) = true → ∀ e, e ∈ entries → 0 ≤ e.2 := by
  intro hall e he
  exact of_decide_eq_true (List.all_eq_true.mp hall e he)

/-- THE EXPORT: any list of records with pairwise distinct cores — the exact
hypothesis `Measure.weight_bound_T` carries — weighs at most the declared
mass. `core_sum_map_fin_core` turns the records into their cores and the
hypothesis into an ordinary `List.Nodup`; the rest is
`entries_weight_qsum_le`. A task's `Measure.weight_bound_T` proof compares
against `b * M`, so at `b = 1` it is this bound, and
`Measure.weight_bound_mono` carries it to every larger `b`. The
duplicate-freedom hypothesis is doing work:
`finite_support_bound_needs_nodup` exhibits a list the bound fails on. -/
theorem finite_support_bound (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (finite_support entries Hnn)) l
      ≤ cd_mass (finite_support entries Hnn) := by
  intro hnd
  have hw : cd_weight (finite_support entries Hnn) = entries_weight entries := rfl
  have hm : cd_mass (finite_support entries Hnn) = entries_mass entries := rfl
  rw [hw, hm, core_sum_map_fin_core]
  exact entries_weight_qsum_le entries (l.map fin_core) Hnn hnd

/-! ## The same bound, refined to a subset of the cores -/

/-- The entries naming a core the predicate accepts. A `Bool`-valued
predicate rather than a `Prop`-valued one, because the restriction has to be
COMPUTED: `entries_mass` of the restriction is the number the refined bound
compares against, and an author writing that number down wants it to
reduce. -/
def entries_restrict (P : FinCore → Bool) (entries : List (FinCore × Rat)) :
    List (FinCore × Rat) :=
  entries.filter (fun e => P e.1)

/-- Restricting keeps every entry's weight nonnegative, since it only removes
entries. -/
theorem entries_restrict_nonneg (P : FinCore → Bool) (entries : List (FinCore × Rat)) :
    (∀ e, e ∈ entries → 0 ≤ e.2) →
    ∀ e, e ∈ entries_restrict P entries → 0 ≤ e.2 := by
  intro hnn e he
  unfold entries_restrict at he
  exact hnn e (List.mem_filter.mp he).1

/-- AT AN ACCEPTED CORE, the discarded entries were contributing nothing: an
entry the predicate rejects names a core the predicate rejects, which is not
the core being weighed, so its indicator misses. Note where this does NOT
hold — at a core the predicate rejects the two weights differ, which is why
the bound below quantifies over lists of accepted cores. -/
theorem entries_weight_restrict (P : FinCore → Bool) (entries : List (FinCore × Rat))
    (c : FinCore) :
    P c = true → entries_weight entries c = entries_weight (entries_restrict P entries) c := by
  intro hp
  unfold entries_restrict
  induction entries with
  | nil => rfl
  | cons e entries ih =>
    by_cases hf : P e.1 = true
    · rw [List.filter_cons_of_pos (p := fun e : FinCore × Rat => P e.1) (a := e)
        (l := entries) hf]
      show core_indicator e.1 e.2 c + entries_weight entries c
        = core_indicator e.1 e.2 c
          + entries_weight (entries.filter (fun e => P e.1)) c
      rw [ih]
    · rw [List.filter_cons_of_neg (p := fun e : FinCore × Rat => P e.1) (a := e)
        (l := entries) hf]
      have hne : e.1 ≠ c := by
        intro heq
        rw [heq] at hf
        exact hf hp
      show core_indicator e.1 e.2 c + entries_weight entries c
        = entries_weight (entries.filter (fun e => P e.1)) c
      rw [core_indicator_miss e.1 e.2 c hne, Rat.zero_add, ih]

/-- THE PER-SUBSET REFINEMENT: a list whose cores all satisfy `P` weighs at
most the mass of the `P`-entries alone, not the mass of all of them.
`finite_support_bound` is the case where `P` accepts everything
(`entries_restrict_all`), but the refinement is what a task needs when its
fire set is a known part of the support and the rest of the declared mass
sits on cores the classifier accepts. The proof is one rewrite and then the
unrefined bound. -/
theorem finite_support_bound_subset (P : FinCore → Bool) (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → P (fin_core f) = true) →
    core_sum (cd_weight (finite_support entries Hnn)) l
      ≤ entries_mass (entries_restrict P entries) := by
  intro hnd hP
  have hw : cd_weight (finite_support entries Hnn) = entries_weight entries := rfl
  have hext : qsum (entries_weight entries) (l.map fin_core)
      = qsum (entries_weight (entries_restrict P entries)) (l.map fin_core) := by
    refine qsum_ext _ _ _ ?_
    intro c hc
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
    exact entries_weight_restrict P entries (fin_core f) (hP f hf)
  rw [hw, core_sum_map_fin_core, hext]
  exact entries_weight_qsum_le (entries_restrict P entries) (l.map fin_core)
    (entries_restrict_nonneg P entries Hnn) hnd

/-- The refinement subsumes the total-mass bound rather than sitting beside
it: at the predicate that accepts everything the restriction is the entry
list itself. -/
theorem entries_restrict_all (entries : List (FinCore × Rat)) :
    entries_restrict (fun _ => true) entries = entries := by
  show entries.filter (fun _ : FinCore × Rat => (true : Bool)) = entries
  induction entries with
  | nil => rfl
  | cons e entries ih =>
    rw [List.filter_cons_of_pos (p := fun _ : FinCore × Rat => (true : Bool)) (a := e)
      (l := entries) rfl, ih]

/-! ## Wrapping a core back up as a record -/

/-- A canonical `FinInput.FinProcInput` over a given core. The four core
fields are copied; the launch-environment fields are invented. The ids, the
descriptor limit and the blocked mask are all the zero word, which is what
`Run.valid_input` admits for each of them; `fin_groups` is empty and
`fin_net` is `State.net_silent`, neither of which `Run.valid_input`
constrains; `fin_hwcap` is `StackLayout.hwcap_rv64gc`, because
`Run.valid_hwcap` admits exactly two words and zero is neither; and
`fin_abort_terminal` is `false`, the one value `Run.valid_input` fixes.

The choice is allowed to be arbitrary because `FinInput.fin_core` forgets all
of it. What the embedding is FOR is `fin_core_core_input`: it is a section of
`FinInput.fin_core`, so a statement about a list of cores can be re-stated as
a statement about a list of records without changing any sum. It is NOT
claimed that `core_input c` is valid, nor that anything rejects it. -/
def core_input (c : FinCore) : FinProcInput :=
  FinProcInput.mkFinProcInput c.core_argv c.core_envp c.core_fs c.core_stdin
    (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent (Z_to_bv 64 0) (Z_to_bv 64 0)
    StackLayout.hwcap_rv64gc false .Sv48 [] []

/-- The embedding is a section of `FinInput.fin_core`: wrapping a core up and
reading it back gives the core. A core is its own four fields. -/
theorem fin_core_core_input (c : FinCore) : fin_core (core_input c) = c := by
  cases c
  rfl

/-- ... and so a list of cores, wrapped, has exactly those cores. -/
theorem map_fin_core_core_input (cs : List FinCore) :
    (cs.map core_input).map fin_core = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, List.map_cons, fin_core_core_input, ih]

/-- THE RESTRICTION TO CORES COSTS NOTHING, mechanized. Any weight satisfying
`Measure.Distribution`'s two weight obligations agrees, pointwise, with the
lift of the `CoreDistribution` that weighs a core by that weight at the
core's canonical record; the declared mass is free of the weight, since no
obligation ties `M` to it. So "this library builds all the distributions
there are" is a theorem, and an author who cannot see how to phrase a weight
as a `CoreDistribution` has a presentation problem, not a limit. -/
theorem cd_lift_complete (w : FinProcInput → Rat) (M : Rat) :
    (∀ f, 0 ≤ w f) →
    (∀ f g, fin_core f = fin_core g → w f = w g) →
    ∃ D : CoreDistribution, cd_mass D = M ∧ ∀ f, w f = cd_lift D f := by
  intro hnn hblind
  refine ⟨{ cd_weight := fun c => w (core_input c)
            cd_mass := M
            cd_nonneg := fun c => hnn (core_input c) }, rfl, ?_⟩
  intro f
  show w f = w (core_input (fin_core f))
  exact hblind f (core_input (fin_core f)) (fin_core_core_input (fin_core f)).symm

/-! ## Honesty certificates for `finite_support` -/

/-- UPPER: every admissible partial sum is at most the declared mass. This is
`finite_support_bound` under the name the certificate vocabulary uses, stated
separately so that the pair (upper, lower) reads as a pair. -/
theorem finite_support_mass_upper (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    core_sum (cd_weight (finite_support entries Hnn)) l
      ≤ cd_mass (finite_support entries Hnn) :=
  finite_support_bound entries Hnn l

/-- The counting fact behind the lower witness: over a duplicate-free list of
cores that COVERS every entry, the sum reaches the mass. Induction on the
entries again, with `qsum_indicator_present` at the head, which is where the
coverage hypothesis is spent. This direction needs no nonnegativity, because
nothing is being dropped. -/
theorem entries_mass_le_qsum (entries : List (FinCore × Rat)) (cs : List FinCore) :
    cs.Nodup → (∀ e, e ∈ entries → e.1 ∈ cs) →
    entries_mass entries ≤ qsum (entries_weight entries) cs := by
  induction entries with
  | nil =>
    intro _ _
    rw [entries_mass_nil,
      qsum_ext (entries_weight []) (fun _ => (0 : Rat)) cs (fun _ _ => rfl), qsum_zero]
    exact Rat.le_refl
  | cons e entries ih =>
    intro hnd hcov
    rw [qsum_entries_cons, entries_mass_cons,
      qsum_indicator_present e.1 e.2 cs hnd (hcov e List.mem_cons_self)]
    exact add_le_add_rat Rat.le_refl
      (ih hnd (fun e' he' => hcov e' (List.mem_cons_of_mem _ he')))

/-- LOWER, with the CHOICE of list left to the caller: any duplicate-free
list of cores that covers the entries attains the declared mass, once wrapped
by `core_input`. The content and the choice are separated because a mixture
needs them separated: a two-component mixture has to attain both components
on ONE list, and neither component's canonical witness need cover the
other's cores. `finite_support_mass_lower_witness` is this lemma at the
canonical choice. -/
theorem finite_support_mass_lower_on (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) (cs : List FinCore) :
    cs.Nodup → (∀ e, e ∈ entries → e.1 ∈ cs) →
    cd_mass (finite_support entries Hnn)
      ≤ core_sum (cd_weight (finite_support entries Hnn)) (cs.map core_input) := by
  intro hnd hcov
  have hw : cd_weight (finite_support entries Hnn) = entries_weight entries := rfl
  have hm : cd_mass (finite_support entries Hnn) = entries_mass entries := rfl
  rw [hw, hm, core_sum_map_fin_core, map_fin_core_core_input]
  exact entries_mass_le_qsum entries cs hnd hcov

/-- Dropping repeats from a list of cores. Rocq reads `List.nodup` of the
standard library here; Lean core ships `List.eraseDups` without the two facts
this needs, so the function is written down. -/
private def core_dedup : List FinCore → List FinCore
  | [] => []
  | c :: cs => if c ∈ cs then core_dedup cs else c :: core_dedup cs

/-- The step equation of `core_dedup`. -/
private theorem core_dedup_cons (c : FinCore) (cs : List FinCore) :
    core_dedup (c :: cs) = if c ∈ cs then core_dedup cs else c :: core_dedup cs := rfl

/-- `core_dedup` keeps exactly the members it was given. -/
private theorem mem_core_dedup (x : FinCore) (l : List FinCore) :
    x ∈ core_dedup l ↔ x ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons c cs ih =>
    rw [core_dedup_cons]
    by_cases hc : c ∈ cs
    · rw [ite_eq_left hc, ih, List.mem_cons]
      constructor
      · intro h
        exact Or.inr h
      · intro h
        rcases h with rfl | h
        · exact hc
        · exact h
    · rw [ite_eq_right hc, List.mem_cons, List.mem_cons, ih]

/-- `core_dedup` leaves no repeats. -/
private theorem nodup_core_dedup (l : List FinCore) : (core_dedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons c cs ih =>
    rw [core_dedup_cons]
    by_cases hc : c ∈ cs
    · rw [ite_eq_left hc]
      exact ih
    · rw [ite_eq_right hc]
      exact List.nodup_cons.mpr ⟨fun h => hc ((mem_core_dedup c cs).mp h), ih⟩

/-- LOWER, at the canonical list: the entries' cores with repeats removed,
each wrapped by `core_input`. So the declared mass is not padding: some list
the obligation quantifies over does weigh that much. The witness list is not
claimed valid or rejected; a task that wants its mass attained BY THE FIRE
SET has to exhibit rejected inputs itself. -/
theorem finite_support_mass_lower_witness (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup ∧
      cd_mass (finite_support entries Hnn)
        ≤ core_sum (cd_weight (finite_support entries Hnn)) l := by
  refine ⟨(core_dedup (entries.map Prod.fst)).map core_input, ?_, ?_⟩
  · rw [map_fin_core_core_input]
    exact nodup_core_dedup _
  · refine finite_support_mass_lower_on entries Hnn _ (nodup_core_dedup _) ?_
    intro e he
    exact (mem_core_dedup e.1 _).mpr (List.mem_map_of_mem he)

/-- The two certificates together: the declared mass is exactly what some
admissible list weighs. The equality is DERIVED from the two inequalities by
antisymmetry, never decided by computing on either side. -/
theorem finite_support_mass_exact (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup ∧
      core_sum (cd_weight (finite_support entries Hnn)) l
        = cd_mass (finite_support entries Hnn) := by
  obtain ⟨l, hnd, hlow⟩ := finite_support_mass_lower_witness entries Hnn
  exact ⟨l, hnd, Rat.le_antisymm (finite_support_bound entries Hnn l hnd) hlow⟩

/-! ## Non-vacuity: the obligations really discharge -/

/-- The empty core: empty argv, empty envp, empty file system, empty standard
input. Not claimed valid; a point of `FinInput.FinCore` to hang a weight
on. -/
def example_core_empty : FinCore := FinCore.mkFinCore [] [] [] []

/-- The same core with the one-byte standard input "A". -/
def example_core_a : FinCore := FinCore.mkFinCore [] [] [] [Z_to_bv 8 65]

/-- A two-entry support: half the mass on the empty input, a quarter on "A",
for a declared total of three quarters. -/
def example_entries : List (FinCore × Rat) :=
  [(example_core_empty, (1 / 2 : Rat)), (example_core_a, (1 / 4 : Rat))]

/-- The nonnegativity obligation, discharged by the boolean scan of
`entries_nonneg_of_forallb` rather than by a case chain. The kernel runs the
scan, because the rational comparisons normalize through `Nat.gcd`, which the
elaborator does not unfold — the same reason `Measure.lean` gives at
`weight_bound_refutable`. -/
theorem example_entries_nonneg : ∀ e, e ∈ example_entries → 0 ≤ e.2 :=
  entries_nonneg_of_forallb example_entries (by decide +kernel)

/-- The example distribution: the two-entry finite support. -/
def example_cd : CoreDistribution :=
  finite_support example_entries example_entries_nonneg

/-- THE POINT OF THE FILE, compiled: a `Measure.Distribution` whose five
components are all taken from the library, with no proof written here. `w` is
the lift, `M` is the declared mass, the two weight obligations are
`cd_lift_nonneg` and `cd_lift_core_blind` at the distribution, and `M_nonneg`
is `finite_support_mass_nonneg` at the entry list's own nonnegativity proof.
Were any obligation not discharged by the library's lemma, this definition
would not typecheck. -/
def Example_D : Distribution :=
  { w := cd_lift example_cd
    M := cd_mass example_cd
    w_nonneg := cd_lift_nonneg example_cd
    M_nonneg := finite_support_mass_nonneg example_entries example_entries_nonneg
    w_core_blind := cd_lift_core_blind example_cd }

/-- The example is not the zero distribution, which every obligation in sight
would satisfy and which would make the definition above evidence of nothing:
it puts a half on the record over the empty core. The comparison is on closed
rational literals and is run by the kernel. -/
theorem example_D_w_positive : 0 < Example_D.w (core_input example_core_empty) := by
  have h : Example_D.w (core_input example_core_empty)
      = entries_weight example_entries example_core_empty :=
    congrArg (entries_weight example_entries) (fin_core_core_input example_core_empty)
  rw [h]
  decide +kernel

/-- ... and its mass certificates are inhabited at that instance: the mass
its two entries declare is attained by an admissible list. This is
`finite_support_mass_exact` at the example, quoted so that the generic
certificate is seen to apply to something. -/
theorem example_D_mass_attained :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup ∧
      core_sum (cd_weight example_cd) l = cd_mass example_cd :=
  finite_support_mass_exact example_entries example_entries_nonneg

/-- The predicate that accepts the empty core and nothing else. -/
def example_is_empty_core (c : FinCore) : Bool :=
  if c = example_core_empty then true else false

/-- THE PER-SUBSET REFINEMENT BITES, which is the only way to see that it is
a refinement and not a restatement. Restricting `example_entries` to the
empty core alone leaves a mass of a half, and the declared total is three
quarters, a number the refined bound does not permit. Without the second part
the first would be consistent with the refinement being vacuous; together
they say that a task whose fire set lies inside the empty core is held to
half the mass. -/
theorem finite_support_bound_subset_bites :
    entries_mass (entries_restrict example_is_empty_core example_entries) = 1 / 2
    ∧ ¬ (entries_mass example_entries ≤ 1 / 2) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## Non-vacuity: duplicate cores are SUMMED, and `List.Nodup` is
load-bearing -/

/-- An entry list that names one core TWICE — half and an eighth on the empty
core, a quarter on "A" — so that the reading argued for at `entries_weight`
is exercised by something instead of only asserted. `example_entries` has two
distinct cores and therefore tests nothing about repeats. -/
def dup_entries : List (FinCore × Rat) :=
  [(example_core_empty, (1 / 2 : Rat)),
   (example_core_a, (1 / 4 : Rat)),
   (example_core_empty, (1 / 8 : Rat))]

/-- The distribution on the repeating entry list. The nonnegativity
obligation is discharged at the definition site, the other of the two styles
`entries_nonneg_of_forallb` supports. -/
def dup_cd : CoreDistribution :=
  finite_support dup_entries (entries_nonneg_of_forallb dup_entries (by decide +kernel))

/-- The bite: the repeated core weighs five eighths, the SUM of its two
entries, and not the half a "first entry wins" reading would give it. An
equation between closed literals, run by the kernel. -/
theorem dup_entries_weight_summed :
    entries_weight dup_entries example_core_empty = 5 / 8 := by
  decide +kernel

/-- ... and the declared mass is still the flat total of the entries, seven
eighths, which is the half of the story that makes the summing reading the
only coherent one: a first-wins weight would total three quarters against a
declared seven eighths, and no list could reach the declared mass. -/
theorem dup_entries_mass : entries_mass dup_entries = 7 / 8 := by
  decide +kernel

/-- The witness `finite_support_mass_lower_witness` builds for this entry
list, written out. Dropping the repeat leaves two elements for three
entries. -/
def dup_witness : List FinProcInput :=
  (core_dedup (dup_entries.map Prod.fst)).map core_input

/-- The witness has two elements, not three. -/
theorem dup_witness_collapses_the_repeat : dup_witness.length = 2 := by
  decide +kernel

/-- ... and it still attains the declared seven eighths, which is exactly the
claim `finite_support_mass_lower_witness` would fail on under a first-wins
reading. -/
theorem dup_witness_attains_mass :
    core_sum (cd_weight dup_cd) dup_witness = cd_mass dup_cd := by
  decide +kernel

/-- THE `List.Nodup` HYPOTHESIS IS LOAD-BEARING, the combinator-level
counterpart of `Measure.weight_bound_refutable`: without duplicate-freedom of
the CORES, `finite_support_bound` is false. Offer the same core twice — two
records, so the list is duplicate-free as a list of RECORDS — and the sum is
five quarters against a declared mass of seven eighths. The second part says
the bound really would fail on this list; the first says the list is excluded
and names what excludes it. -/
theorem finite_support_bound_needs_nodup :
    ¬ (([core_input example_core_empty, core_input example_core_empty].map fin_core).Nodup)
    ∧ ¬ (core_sum (cd_weight dup_cd)
          [core_input example_core_empty, core_input example_core_empty]
          ≤ cd_mass dup_cd) := by
  constructor
  · intro hnd
    simp only [List.map_cons, List.map_nil, fin_core_core_input] at hnd
    exact (List.nodup_cons.mp hnd).1 List.mem_cons_self
  · decide +kernel

/-! ## Non-vacuity, the other way: a negative entry admits no distribution -/

/-- A rigged entry list: one core, weight minus one. Nothing stops an author
WRITING this list, and the two lemmas below are what stops it becoming a
`CoreDistribution`. -/
def negative_entries : List (FinCore × Rat) :=
  [(example_core_empty, (-1 : Rat))]

/-- The constructor's obligation is unsatisfiable for it: the weight it gives
the rigged core is minus one, and no proof of nonnegativity exists. -/
theorem negative_entries_no_nonneg_weight :
    ¬ (∀ c, 0 ≤ entries_weight negative_entries c) := by
  intro hnn
  exact absurd (hnn example_core_empty) (by decide +kernel)

/-- So no `CoreDistribution` whatever weighs cores that way — not just none
built by `finite_support`, and not just none whose weight is that exact
function: none whose weight so much as agrees with it pointwise. The
`cd_nonneg` FIELD is what refutes it, and that is the argument for making
nonnegativity a field: the impossibility becomes a property of the record
rather than of one combinator's typing. -/
theorem negative_entries_no_core_distribution (D : CoreDistribution) :
    ¬ (∀ c, cd_weight D c = entries_weight negative_entries c) := by
  intro hagree
  refine negative_entries_no_nonneg_weight ?_
  intro c
  rw [← hagree c]
  exact cd_nonneg D c

/-! ## Enumerating the bytes, and the byte lists of a given length -/

/-- The round trip through `BvBase`'s `Z_to_bv` at a natural number. -/
private theorem z_to_bv_natCast (w n : Nat) : Z_to_bv w (n : Int) = BitVec.ofNat w n :=
  BitVec.ofInt_natCast w n

/-- All 256 bytes, as a list. Nothing here is about measures: if `BvBase`
grows an enumeration of `BvBase.byte`, delete this one and use it. It is a
map over a range rather than a spelled-out literal because the three facts
wanted of it — its length, that it misses nothing, that it repeats nothing —
are then three short arguments about the range. -/
def all_bytes : List byte :=
  (List.range 256).map (fun n : Nat => Z_to_bv 8 (n : Int))

/-- There are 256 of them. -/
theorem all_bytes_length : all_bytes.length = 256 := by
  unfold all_bytes
  rw [List.length_map, List.length_range]

/-- It misses nothing. A `BvBase.byte` is a `BitVec 8`, whose value is below
256, so the byte is `Z_to_bv 8` of a number the range enumerates. -/
theorem all_bytes_complete (b : byte) : b ∈ all_bytes := by
  have hb : b.toNat < 256 := by simpa using b.isLt
  unfold all_bytes
  refine List.mem_map.mpr ⟨b.toNat, List.mem_range.mpr hb, ?_⟩
  show Z_to_bv 8 ((b.toNat : Int)) = b
  rw [z_to_bv_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Mapping an injective function over a duplicate-free list leaves it
duplicate-free. Lean core ships the other direction; this one is what a list
built by `List.map` needs. Injectivity is asked for only ON THE LIST, which
is what makes it usable for a byte constructor injective on `[0, 256)` and on
nothing wider. -/
theorem NoDup_map_inj {A B : Type} (f : A → B) (l : List A) :
    (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) → l.Nodup → (l.map f).Nodup := by
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons x l ih =>
    intro hinj hnd
    obtain ⟨hnin, hnd⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, ih (fun y z hy hz =>
      hinj y z (List.mem_cons_of_mem _ hy) (List.mem_cons_of_mem _ hz)) hnd⟩
    intro hin
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hin
    have hxy : x = y :=
      hinj x y List.mem_cons_self (List.mem_cons_of_mem _ hy) hfy.symm
    rw [hxy] at hnin
    exact hnin hy

/-- ... and the byte enumeration repeats nothing: below 256 the round trip
through the numeric value is the identity, so the map is injective on the
range, which is itself duplicate-free. -/
theorem all_bytes_nodup : all_bytes.Nodup := by
  unfold all_bytes
  refine NoDup_map_inj _ _ ?_ List.nodup_range
  intro x y hx hy heq
  replace heq : Z_to_bv 8 (x : Int) = Z_to_bv 8 (y : Int) := heq
  rw [List.mem_range] at hx hy
  rw [z_to_bv_natCast, z_to_bv_natCast] at heq
  have h := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
  have h256 : (2 : Nat) ^ 8 = 256 := by decide
  rw [h256, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact h

/-- Every byte list of length `n`, as a list of 256 ^ n of them. This is the
object the counting lemma counts against: an explicit finite enumeration, so
that "there are at most 256 ^ n of these" is an inclusion into a list whose
length is known, rather than a cardinality argument about a type. -/
def byte_lists : Nat → List (List byte)
  | 0 => [[]]
  | n + 1 => all_bytes.flatMap (fun b => (byte_lists n).map (fun s => b :: s))

/-- The base equation of `byte_lists`. -/
private theorem byte_lists_zero : byte_lists 0 = [[]] := rfl

/-- The step equation of `byte_lists`. -/
private theorem byte_lists_succ (n : Nat) :
    byte_lists (n + 1)
      = all_bytes.flatMap (fun b => (byte_lists n).map (fun s => b :: s)) := rfl

/-- The length of a `List.flatMap` whose blocks all have the same size. Lean
core adds up the block lengths; when every block is the same size the sum is
a product, and that is the shape `byte_lists` produces. -/
theorem length_flat_map_const (A B : Type) (f : A → List B) (l : List A) (c : Nat) :
    (∀ x, x ∈ l → (f x).length = c) → (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hc
    rw [List.flatMap_cons, List.length_append, hc x List.mem_cons_self,
      ih (fun y hy => hc y (List.mem_cons_of_mem _ hy)), List.length_cons,
      Nat.add_mul, Nat.one_mul]
    exact Nat.add_comm c (l.length * c)

/-- There are 256 ^ n byte lists of length n. -/
theorem byte_lists_length (n : Nat) : (byte_lists n).length = 256 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hblk : ∀ b : byte,
        b ∈ all_bytes → ((byte_lists n).map (fun s => b :: s)).length = 256 ^ n := by
      intro b _
      rw [List.length_map, ih]
    rw [byte_lists_succ,
      length_flat_map_const byte (List byte)
        (fun b => (byte_lists n).map (fun s => b :: s)) all_bytes (256 ^ n) hblk,
      all_bytes_length]
    exact (Nat.mul_comm 256 (256 ^ n)).trans (Nat.pow_succ 256 n).symm

/-- ... and none is missing. Stated at the list's own length rather than at
an arbitrary number equal to it, so that the induction needs no
generalization. -/
theorem byte_lists_complete (l : List byte) : l ∈ byte_lists l.length := by
  induction l with
  | nil =>
    show ([] : List byte) ∈ [([] : List byte)]
    exact List.mem_cons_self
  | cons b l ih =>
    rw [List.length_cons, byte_lists_succ]
    exact List.mem_flatMap.mpr ⟨b, all_bytes_complete b, List.mem_map.mpr ⟨l, ih, rfl⟩⟩

/-- ... and nothing longer or shorter has crept in: the enumeration at `n`
holds only length-`n` lists. Needed because a witness list built from it has
to satisfy the counting lemma's own length hypothesis. -/
theorem byte_lists_In_length (n : Nat) (s : List byte) :
    s ∈ byte_lists n → s.length = n := by
  induction n generalizing s with
  | zero =>
    intro hs
    replace hs : s ∈ [([] : List byte)] := hs
    have h := List.mem_singleton.mp hs
    subst h
    rfl
  | succ n ih =>
    intro hs
    rw [byte_lists_succ] at hs
    obtain ⟨_, _, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    rw [List.length_cons, ih s' hs']

/-- `List.Nodup` through a `List.flatMap`. Lean core ships nothing for this,
so the three conditions are spelled out: the index list is duplicate-free,
each block is, and no element lands in two blocks. The third is the one a
caller has to think about. Stated generically rather than inlined into
`byte_lists_nodup` because the shape recurs. -/
theorem NoDup_flat_map {A B : Type} (f : A → List B) (l : List A) :
    l.Nodup →
    (∀ x, x ∈ l → (f x).Nodup) →
    (∀ x y b, x ∈ l → y ∈ l → b ∈ f x → b ∈ f y → x = y) →
    (l.flatMap f).Nodup := by
  induction l with
  | nil => intro _ _ _; exact List.nodup_nil
  | cons x l ih =>
    intro hnd hblk hdisj
    obtain ⟨hnin, hnd⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr ⟨hblk x List.mem_cons_self, ?_, ?_⟩
    · exact ih hnd (fun y hy => hblk y (List.mem_cons_of_mem _ hy))
        (fun y z b hy hz hby hbz => hdisj y z b (List.mem_cons_of_mem _ hy)
          (List.mem_cons_of_mem _ hz) hby hbz)
    · intro a ha b hb hab
      subst hab
      obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp hb
      have hxy : x = y :=
        hdisj x y a List.mem_cons_self (List.mem_cons_of_mem _ hy) ha hay
      subst hxy
      exact hnin hy

/-- ... and the enumeration repeats nothing. Distinct first bytes give
disjoint blocks, and within a block the induction hypothesis carries over
through `cons`, which is injective. This is what a witness list of the full
size 256 ^ n needs. -/
theorem byte_lists_nodup (n : Nat) : (byte_lists n).Nodup := by
  induction n with
  | zero =>
    show ([([] : List byte)]).Nodup
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | succ n ih =>
    rw [byte_lists_succ]
    refine NoDup_flat_map _ _ all_bytes_nodup ?_ ?_
    · intro b _
      refine NoDup_map_inj _ _ ?_ ih
      intro x y _ _ heq
      replace heq : b :: x = b :: y := heq
      injection heq with _ h
    · intro x y bs _ _ hx hy
      obtain ⟨lx, _, hlx⟩ := List.mem_map.mp hx
      obtain ⟨ly, _, hly⟩ := List.mem_map.mp hy
      replace hlx : x :: lx = bs := hlx
      replace hly : y :: ly = bs := hly
      have h := hlx.trans hly.symm
      injection h with h1 _

/-! ## Sums over inclusions, concatenations and filters -/

/-- A POSITIVE sum has a positive member, the companion of `qsum_nonneg` and
the direction a non-vacuity argument needs. A claim "some admissible list
weighs at least this much" is worth exactly as much as the reasons a list
could have for satisfying it, so the certificates are followed by pins that
read a positive WEIGHT back out of a positive SUM. The case split at one core
at a time: either the head weighs something, or it weighs zero — its weight
is nonnegative and not positive — and the tail carries the whole sum. -/
theorem qsum_positive_member {A : Type} (w : A → Rat) (cs : List A) :
    (∀ c, 0 ≤ w c) → 0 < qsum w cs → ∃ c, c ∈ cs ∧ 0 < w c := by
  intro hw
  induction cs with
  | nil =>
    intro hpos
    rw [qsum_nil] at hpos
    exact absurd hpos Rat.lt_irrefl
  | cons c cs ih =>
    intro hpos
    rw [qsum_cons] at hpos
    rcases Classical.em (0 < w c) with hc | hc
    · exact ⟨c, List.mem_cons_self, hc⟩
    · have hz : w c = 0 := Rat.le_antisymm (Rat.not_lt.mp hc) (hw c)
      rw [hz, Rat.zero_add] at hpos
      obtain ⟨c', hin, hc'⟩ := ih hpos
      exact ⟨c', List.mem_cons_of_mem _ hin, hc'⟩

/-- Removing ONE occurrence of a core from a list. `List.erase` would remove
every occurrence, and the difference is the whole point: the sum lemma below
is then an exact equation with NO duplicate-freedom hypothesis on the list,
which is what lets `qsum_core_incl_le` bound a sum by a sum over a list
nobody has proved duplicate-free. -/
def core_remove_one (c : FinCore) : List FinCore → List FinCore
  | [] => []
  | x :: rest => if c = x then rest else x :: core_remove_one c rest

/-- The step equation of `core_remove_one`. -/
private theorem core_remove_one_cons (c x : FinCore) (rest : List FinCore) :
    core_remove_one c (x :: rest)
      = if c = x then rest else x :: core_remove_one c rest := rfl

/-- A member's weight splits off the sum exactly, leaving the sum over the
list with one occurrence of it removed. -/
theorem qsum_core_remove_one (w : FinCore → Rat) (c : FinCore) (cs : List FinCore) :
    c ∈ cs → qsum w cs = w c + qsum w (core_remove_one c cs) := by
  induction cs with
  | nil => intro h; simp at h
  | cons x cs ih =>
    intro hin
    rw [core_remove_one_cons]
    by_cases hcx : c = x
    · rw [ite_eq_left hcx, qsum_cons, hcx]
    · have hin' : c ∈ cs := by
        rcases List.mem_cons.mp hin with heq | h
        · exact absurd heq hcx
        · exact h
      rw [ite_eq_right hcx, qsum_cons, qsum_cons, ih hin']
      exact Rat.add_left_comm (w x) (w c) (qsum w (core_remove_one c cs))

/-- Everything else survives the removal. -/
theorem In_core_remove_one (c x : FinCore) (cs : List FinCore) :
    x ∈ cs → x ≠ c → x ∈ core_remove_one c cs := by
  induction cs with
  | nil => intro h _; simp at h
  | cons y cs ih =>
    intro hin hne
    rw [core_remove_one_cons]
    by_cases hcy : c = y
    · rw [ite_eq_left hcy]
      rcases List.mem_cons.mp hin with heq | h
      · exact absurd (heq.trans hcy.symm) hne
      · exact h
    · rw [ite_eq_right hcy]
      rcases List.mem_cons.mp hin with heq | h
      · rw [heq]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h hne)

/-- THE MONOTONICITY THE CYLINDER BOUND RUNS ON: a duplicate-free list of
cores sums to at most what any list containing it sums to. The induction
peels the head, removes one occurrence of it from the containing list, and
recurses; duplicate-freedom of the SMALL list is what makes the tail still
included in the remainder, and it is the only place that hypothesis is used.
Nothing is asked of the containing list — it may repeat, and each repeat only
makes its sum larger. Nonnegativity of the weight is genuinely needed: the
empty list already refutes the statement without it. -/
theorem qsum_core_incl_le (w : FinCore → Rat) (cs ys : List FinCore) :
    (∀ c, 0 ≤ w c) → cs.Nodup → cs ⊆ ys → qsum w cs ≤ qsum w ys := by
  intro hw
  induction cs generalizing ys with
  | nil =>
    intro _ _
    rw [qsum_nil]
    exact qsum_nonneg w ys (fun c _ => hw c)
  | cons c cs ih =>
    intro hnd hincl
    obtain ⟨hnin, hnd⟩ := List.nodup_cons.mp hnd
    have hc : c ∈ ys := hincl List.mem_cons_self
    rw [qsum_core_remove_one w c ys hc, qsum_cons]
    refine add_le_add_rat Rat.le_refl (ih (core_remove_one c ys) hnd ?_)
    intro x hx
    refine In_core_remove_one c x ys (hincl (List.mem_cons_of_mem _ hx)) ?_
    intro hxc
    rw [hxc] at hx
    exact hnin hx

/-- A `List.flatMap` of uniformly bounded blocks is bounded by the count of
blocks times the bound. This turns "each of the 256 continuations carries at
most m" into "the 256 of them carry at most 256 * m". -/
theorem qsum_flat_map_const_le {A B : Type} (w : B → Rat) (f : A → List B)
    (l : List A) (C : Rat) :
    (∀ x, x ∈ l → qsum w (f x) ≤ C) → qsum w (l.flatMap f) ≤ Qnat l.length * C := by
  induction l with
  | nil =>
    intro _
    rw [List.flatMap_nil, qsum_nil]
    show (0 : Rat) ≤ Qnat 0 * C
    rw [Qnat_0, Rat.zero_mul]
    exact Rat.le_refl
  | cons x l ih =>
    intro hb
    rw [List.flatMap_cons, qsum_app]
    refine Rat.le_trans (add_le_add_rat (hb x List.mem_cons_self)
      (ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)))) ?_
    rw [List.length_cons, Qnat_succ, Rat.add_mul, Rat.one_mul]
    exact Rat.le_refl

/-- A list on which the weight is constant sums to the count times the
constant — the other half of the length-slice bound, where the counting lemma
supplies the count. -/
theorem qsum_const {A : Type} (w : A → Rat) (cs : List A) (C : Rat) :
    (∀ c, c ∈ cs → w c = C) → qsum w cs = Qnat cs.length * C := by
  induction cs with
  | nil =>
    intro _
    rw [qsum_nil]
    show (0 : Rat) = Qnat 0 * C
    rw [Qnat_0, Rat.zero_mul]
  | cons c cs ih =>
    intro hc
    rw [qsum_cons, hc c List.mem_cons_self,
      ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)), List.length_cons,
      Qnat_succ, Rat.add_mul, Rat.one_mul]

/-- Elements the weight ignores can be dropped. Together with
`List.Nodup.filter` this lets a bound proved for lists INSIDE a region be
applied to a list that merely happens to weigh zero outside it. -/
theorem qsum_filter {A : Type} (w : A → Rat) (P : A → Bool) (cs : List A) :
    (∀ c, P c = false → w c = 0) → qsum w cs = qsum w (cs.filter P) := by
  intro hz
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hp : P c = true
    · rw [List.filter_cons_of_pos hp, qsum_cons, qsum_cons, ih]
    · have hpf : P c = false := by
        cases hpc : P c
        · rfl
        · exact absurd hpc hp
      rw [List.filter_cons_of_neg hp, qsum_cons, hz c hpf, Rat.zero_add, ih]

/-- The largest member of a list of naturals, zero on the empty list. Rocq
reads the standard library's `List.list_max` here and Lean core has no twin
of it, so it is written down; `list_max_ge` is the Rocq declaration this
serves. -/
def list_max (l : List Nat) : Nat := l.foldr Nat.max 0

/-- `list_max` bounds every member. Lean core states the equivalence for
`List.max?` and not this consequence of it. -/
theorem list_max_ge (l : List Nat) (n : Nat) : n ∈ l → n ≤ list_max l := by
  induction l with
  | nil => intro h; simp at h
  | cons x l ih =>
    intro hin
    rcases List.mem_cons.mp hin with heq | h
    · rw [heq]
      exact Nat.le_max_left x (list_max l)
    · exact Nat.le_trans (ih h) (Nat.le_max_right x (list_max l))

/-! ## THE COUNTING LEMMA -/

/-- A list of records with duplicate-free CORES, every core matching fixed
argv, envp and file system and carrying standard input of length exactly `n`,
has at most 256 ^ n elements.

This is the fact the geometric distribution's bounds are built out of, and
the reason it can be stated at all is the quotient:
`Measure.weight_bound_T` reads duplicate-freedom on `FinInput.fin_core`, so
the list's records inject into their cores, and a core matching the fixed
environment is determined by its standard input alone. Length-`n` byte lists
are enumerated by `byte_lists n`, there are 256 ^ n of them, and the
inclusion of a duplicate-free list converts into the bound.

The environment hypothesis is a single equation rather than three field
equations, because that is the form the injection consumes directly. Read it
as: the list is a duplicate-free sample from ONE length slice of ONE
launch-time environment. Nothing is claimed about lists that mix slices. -/
theorem injective_core_list_in_cylinder_length_bound (argv envp : List (List byte))
    (fs : Fs.Fs) (n : Nat) (l : List FinProcInput) :
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l →
      fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin ∧ f.fin_stdin.length = n) →
    l.length ≤ 256 ^ n := by
  intro hnd hall
  have hsub : (l.map fin_core) ⊆ (byte_lists n).map (FinCore.mkFinCore argv envp fs) := by
    intro c hc
    obtain ⟨f, hin, rfl⟩ := List.mem_map.mp hc
    obtain ⟨henv, hlen⟩ := hall f hin
    refine List.mem_map.mpr ⟨f.fin_stdin, ?_, henv.symm⟩
    rw [← hlen]
    exact byte_lists_complete f.fin_stdin
  have hle := List.Nodup.length_le_of_subset hnd hsub
  rwa [List.length_map, List.length_map, byte_lists_length] at hle

/-- THE BOUND IS ATTAINED AT EVERY `n`, so 256 ^ n is the right constant and
not merely a true one: over any launch-time environment at all there is an
admissible list of exactly 256 ^ n records, one per length-`n` standard
input. It is `byte_lists n` wrapped by `core_input`, and the proof is
symbolic throughout: nothing is ever computed, so the witness at two bytes
costs what the witness at one byte costs, which is nothing. -/
theorem injective_core_list_in_cylinder_length_bound_attained
    (argv envp : List (List byte)) (fs : Fs.Fs) (n : Nat) :
    ∃ l : List FinProcInput,
      (l.map fin_core).Nodup ∧
      (∀ f, f ∈ l →
        fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin ∧ f.fin_stdin.length = n) ∧
      l.length = 256 ^ n := by
  refine ⟨(byte_lists n).map (fun s => core_input (FinCore.mkFinCore argv envp fs s)),
    ?_, ?_, ?_⟩
  · have hmap :
        ((byte_lists n).map (fun s => core_input (FinCore.mkFinCore argv envp fs s))).map
            fin_core
          = (byte_lists n).map (fun s => FinCore.mkFinCore argv envp fs s) := by
      rw [List.map_map]
      rfl
    rw [hmap]
    refine NoDup_map_inj _ _ ?_ (byte_lists_nodup n)
    intro x y _ _ heq
    exact congrArg FinCore.core_stdin heq
  · intro f hf
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
    refine ⟨?_, ?_⟩
    · exact fin_core_core_input (FinCore.mkFinCore argv envp fs s)
    · exact byte_lists_In_length n s hs
  · rw [List.length_map, byte_lists_length]

end LinuxProcessSemantics.EquivalenceDefinition.MeasureLib
