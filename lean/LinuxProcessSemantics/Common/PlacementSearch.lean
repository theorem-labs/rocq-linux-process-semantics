import LinuxProcessSemantics.LinuxProcessSem.State
import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! rocq-baseline: 7ba58b45f168d97ca1a555a98fa3b36f29eb5b81 -/

/-! # Common.PlacementSearch — deciding "is there a free gap here?"

Ported whole from `theories/Common/PlacementSearch.v` (ticket
E-proof-library-2a).  The statements are Rocq's in Lean spellings, the
less obvious of which are listed below, except that `existsb_find`'s
element type differs from Rocq's in both directions, as the paragraph
before that list says.  The file was read at the commit named above
(`nightly/09-28-2026`).

Proof-library machinery, not specification.  It decides whether a
page-aligned free gap of `nZ` bytes lies in an interval of the ledger
(`higher_fit_b`, which `no_higher_fit_iff` shows decides `no_higher_fit`
under that lemma's premises), and builds an executable placement on the
same candidate list (`place`, with `place_sound`, `place_complete` and
their `place_in_model` forms).
The arguments — why the candidate list suffices, why the floor hypothesis
of `higher_fit_b_complete` is `0 ≤ aZ + nZ`, why `place_complete` is
conditional, why `place_in_model_admissible` concludes at
`bv_unsigned (Z_to_bv 64 a)` — are on the Rocq lemmas, and the docstrings
here point there rather than restate them.

Rocq's `Example`s are theorems here, closed by `decide` where Rocq runs
`vm_compute`.  Rocq closes `place_complete_premises_are_satisfiable` by
rewriting with `State.v`'s `alloc_top_mkVmMaps`; here `decide` evaluates
`demo_top`, and the proof names no such lemma.

`existsb_find`'s element type differs from Rocq's in both directions.
Rocq binds it as `A : Type@{existsb_find.u0}`, a global universe: a use
at a type `A : Type@{v}` adds the constraint `v <= existsb_find.u0`, so
`A` may be `nat` or `Type` but not `Type@{existsb_find.u0}`, and a
universe-polymorphic use at `Type@{u}` carries `u < existsb_find.u0`.
Here `A : Type _` makes `A`'s universe a parameter of the theorem
(`existsb_find.{u_1}`), with no upper bound, so `A` may be a type in any
universe `Type u`.  Rocq's `A` may also be a proposition such as `True`,
by cumulativity; Lean's `List` takes no proposition as its element type,
so those instances have no counterpart over `List` in Lean.

Representation spellings:
- Rocq `Z` is `Int`.  At the positive `page_size`, Rocq's `mod` and `/`
  (`Z.modulo`, `Z.div`) are Lean's `%` and `/` on `Int`.
- `Z.eqb`/`Z.leb` are `decide` of `=`/`≤`; `existsb f l` is `l.any f`,
  `find f l` is `l.find? f`, `fold_left Z.max l s` is `l.foldl max s`,
  `In x l` is `x ∈ l`, and `fst`/`snd` are `.1`/`.2`.
- `region_free_In` and `region_free_intro` are `State.v` lemmas in Rocq;
  here they come from `Checks/VmMapsDisjoint.lean`, whose header says why
  it holds them and that a `lean: base:` PR moving them into
  `State/Vm.lean` deletes its copies.  The `open` of that namespace names
  just these two, so the build fails on it at that change and the line
  goes with it; the import of `Checks.VmMapsDisjoint` goes in the same
  change. -/

namespace LinuxProcessSemantics.Common.PlacementSearch

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint (region_free_In region_free_intro)

/-- No page-aligned `g` with `aZ + nZ ≤ g` and `g + nZ ≤ baseZ` has
`region_free maps` accept the words `Z_to_bv 64 g` and `Z_to_bv 64 nZ`.
While `g` and `nZ` lie in `[0, 2^64)`, as `no_higher_fit_iff`'s premises
keep them, that says no page-aligned free region of `nZ` bytes starts at
or above `aZ + nZ` and ends at or below `baseZ`; outside that range it is
a claim about the wrapped words. -/
def no_higher_fit (maps : List (word × word)) (aZ nZ baseZ : Int) : Prop :=
  ∀ g : Int,
    g % page_size = 0 →
    aZ + nZ ≤ g →
    g + nZ ≤ baseZ →
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false

/-- The candidates `higher_fit_b` scans; why they suffice is
`higher_fit_b_complete`'s argument. -/
def fit_candidates (maps : List (word × word)) (aZ nZ : Int) : List Int :=
  (aZ + nZ) :: maps.map (fun p => page_round_up_Z (bv_unsigned p.1 + bv_unsigned p.2))

def higher_fit_b (maps : List (word × word)) (aZ nZ baseZ : Int) : Bool :=
  (fit_candidates maps aZ nZ).any (fun g =>
    decide (g % page_size = 0) && decide (aZ + nZ ≤ g) && decide (g + nZ ≤ baseZ)
    && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))

/-- Protected to distinguish `Common/AllocSim.lean`'s `page_round_up_Z_aligned`,
which states that rounding an aligned nonnegative input leaves it unchanged. -/
protected theorem page_round_up_Z_aligned : ∀ z, page_round_up_Z z % page_size = 0 := by
  intro z
  simp only [page_round_up_Z, page_size]
  omega

/-- Protected to distinguish `LinuxProcessSem/Checks/VmMapsDisjoint.lean`'s
`page_round_up_Z_ge`, which takes an extra nonnegativity premise. -/
protected theorem page_round_up_Z_ge : ∀ z, z ≤ page_round_up_Z z := by
  intro z
  simp only [page_round_up_Z, page_size]
  omega

/-- The round-up is the least page multiple at or above its argument. -/
theorem page_round_up_Z_le : ∀ z b,
    z ≤ b → b % page_size = 0 → page_round_up_Z z ≤ b := by
  intro z b hzb hb
  simp only [page_round_up_Z, page_size] at hb ⊢
  omega

theorem fold_max_ge_seed : ∀ (l : List Int) (s : Int), s ≤ l.foldl max s := by
  intro l
  induction l with
  | nil => intro s; exact Int.le_refl s
  | cons x l ih =>
    intro s
    rw [List.foldl_cons]
    have h1 := ih (max s x)
    have h2 : s ≤ max s x := Int.le_max_left s x
    omega

theorem fold_max_ge_in : ∀ (l : List Int) (s x : Int),
    x ∈ l → x ≤ l.foldl max s := by
  intro l
  induction l with
  | nil => intro s x hin; cases hin
  | cons y l ih =>
    intro s x hin
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hin with heq | hin'
    · have h1 := fold_max_ge_seed l (max s y)
      have h2 : y ≤ max s y := Int.le_max_right s y
      omega
    · exact ih (max s y) x hin'

theorem fold_max_le : ∀ (l : List Int) (s b : Int),
    s ≤ b → (∀ x, x ∈ l → x ≤ b) → l.foldl max s ≤ b := by
  intro l
  induction l with
  | nil => intro s b hs _; exact hs
  | cons y l ih =>
    intro s b hs hl
    rw [List.foldl_cons]
    apply ih
    · have hy := hl y List.mem_cons_self
      exact Int.max_le.mpr ⟨hs, hy⟩
    · intro x hx
      exact hl x (List.mem_cons_of_mem _ hx)

theorem fold_max_in_or_seed : ∀ (l : List Int) (s : Int),
    l.foldl max s = s ∨ l.foldl max s ∈ l := by
  intro l
  induction l with
  | nil => intro s; exact Or.inl rfl
  | cons y l ih =>
    intro s
    rw [List.foldl_cons]
    rcases ih (max s y) with heq | hin
    · rw [heq]
      rcases Int.le_total s y with h | h
      · right
        rw [Int.max_eq_right h]
        exact List.mem_cons_self
      · left
        exact Int.max_eq_left h
    · right
      exact List.mem_cons_of_mem _ hin

/-- Completeness of the candidate scan: under these premises, a
page-aligned fitting free gap yields a candidate that is free and
fitting.  The sliding argument, and why the floor hypothesis is
`0 ≤ aZ + nZ` rather than `0 ≤ aZ`, are on the Rocq lemma. -/
theorem higher_fit_b_complete : ∀ (maps : List (word × word)) (aZ nZ baseZ g : Int),
    0 ≤ aZ + nZ → 0 < nZ →
    aZ % page_size = 0 → nZ % page_size = 0 →
    baseZ < two_pow_64 →
    g % page_size = 0 →
    aZ + nZ ≤ g →
    g + nZ ≤ baseZ →
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true →
    higher_fit_b maps aZ nZ baseZ = true := by
  intro maps aZ nZ baseZ g HaPos HnPos HaAl HnAl Hbase HgAl Hglo Hghi Hgfree
  have Hb64 : baseZ < 2 ^ 64 := Hbase
  have HgW : bv_unsigned (Z_to_bv 64 g) = g :=
    bv_unsigned_Z_to_bv_small g (by omega) (by omega)
  have HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ :=
    bv_unsigned_Z_to_bv_small nZ (by omega) (by omega)
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = (fit_candidates maps aZ nZ).filter (fun c => decide (c ≤ g)) :=
    ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = cs.foldl max (aZ + nZ) := ⟨_, rfl⟩
  have Hcs : ∀ x, x ∈ cs ↔ x ∈ fit_candidates maps aZ nZ ∧ decide (x ≤ g) = true := by
    intro x
    rw [hcs]
    exact List.mem_filter
  have Hlo : aZ + nZ ≤ g' := by
    rw [hg']
    exact fold_max_ge_seed cs (aZ + nZ)
  have Hhi : g' ≤ g := by
    rw [hg']
    apply fold_max_le cs (aZ + nZ) g Hglo
    intro x hx
    exact of_decide_eq_true ((Hcs x).mp hx).2
  have Hcand : g' ∈ fit_candidates maps aZ nZ := by
    rcases fold_max_in_or_seed cs (aZ + nZ) with heq | hin
    · rw [hg', heq]
      exact List.mem_cons_self
    · rw [hg']
      exact ((Hcs _).mp hin).1
  have Hg'W : bv_unsigned (Z_to_bv 64 g') = g' :=
    bv_unsigned_Z_to_bv_small g' (by omega) (by omega)
  have Hg'Al : g' % page_size = 0 := by
    rcases List.mem_cons.mp Hcand with heq | hin
    · rw [heq]
      simp only [page_size] at HaAl HnAl ⊢
      omega
    · obtain ⟨p, _, hp⟩ := List.mem_map.mp hin
      rw [← hp]
      exact PlacementSearch.page_round_up_Z_aligned _
  have Hg'free : region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ) = true := by
    apply region_free_intro
    intro b s hin
    have Hno := region_free_In maps _ _ b s Hgfree hin
    simp only [iv_overlap, HgW, HnW, Hg'W, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Int.not_lt] at Hno ⊢
    by_cases Hend : bv_unsigned b + bv_unsigned s ≤ g
    · -- the entry ends at or below `g`: its rounded end is a candidate at or below `g'`
      have Hc : page_round_up_Z (bv_unsigned b + bv_unsigned s) ∈ fit_candidates maps aZ nZ :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(b, s), hin, rfl⟩)
      have Hcle : page_round_up_Z (bv_unsigned b + bv_unsigned s) ≤ g :=
        page_round_up_Z_le _ _ Hend HgAl
      have Hcg' : page_round_up_Z (bv_unsigned b + bv_unsigned s) ≤ g' := by
        rw [hg']
        exact fold_max_ge_in cs (aZ + nZ) _ ((Hcs _).mpr ⟨Hc, decide_eq_true Hcle⟩)
      have Hround := PlacementSearch.page_round_up_Z_ge (bv_unsigned b + bv_unsigned s)
      exact Or.inl (Int.le_trans Hround Hcg')
    · -- the entry ends above `g`: it starts at or above `g + nZ`
      rcases Hno with Hno | Hno
      · omega
      · exact Or.inr (by omega)
  unfold higher_fit_b
  rw [List.any_eq_true]
  refine ⟨g', Hcand, ?_⟩
  have Hg'base : g' + nZ ≤ baseZ := by omega
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨Hg'Al, Hlo⟩, Hg'base⟩, Hg'free⟩

/-- The converse: a candidate the decision procedure accepts is
page-aligned, inside the interval, and accepted by `region_free maps` at
the words `Z_to_bv 64 g` and `Z_to_bv 64 nZ`. Under `0 ≤ g`,
`0 ≤ nZ`, `nZ < 2^64` and `g + nZ ≤ 2^64`, which `no_higher_fit_iff`'s
premises ensure, `[g, g+nZ)` is disjoint from each entry's integer interval
`[start, start + size)`. Interpreting this as free bytes also requires that
no entry wraps past `2^64`: a wrapping entry's low part is not seen, as
pinned by the examples below `place_fits`. -/
theorem higher_fit_b_sound : ∀ maps aZ nZ baseZ,
    higher_fit_b maps aZ nZ baseZ = true →
    ∃ g, g % page_size = 0 ∧ aZ + nZ ≤ g
      ∧ g + nZ ≤ baseZ
      ∧ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true := by
  intro maps aZ nZ baseZ H
  unfold higher_fit_b at H
  obtain ⟨g, _, Hg⟩ := List.any_eq_true.mp H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at Hg
  obtain ⟨⟨⟨Hal, Hlo⟩, Hhi⟩, Hfree⟩ := Hg
  exact ⟨g, Hal, Hlo, Hhi, Hfree⟩

/-- Under these premises, `higher_fit_b` decides `no_higher_fit`. -/
theorem no_higher_fit_iff : ∀ maps aZ nZ baseZ,
    0 ≤ aZ → 0 < nZ →
    aZ % page_size = 0 → nZ % page_size = 0 →
    baseZ < two_pow_64 →
    (higher_fit_b maps aZ nZ baseZ = false ↔ no_higher_fit maps aZ nZ baseZ) := by
  intro maps aZ nZ baseZ HaPos HnPos HaAl HnAl Hbase
  constructor
  · intro Hf g HgAl Hglo Hghi
    cases Hfree : region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) with
    | false => rfl
    | true =>
      rw [higher_fit_b_complete maps aZ nZ baseZ g (by omega) HnPos HaAl HnAl Hbase HgAl
        Hglo Hghi Hfree] at Hf
      cases Hf
  · intro H
    cases Hf : higher_fit_b maps aZ nZ baseZ with
    | false => rfl
    | true =>
      obtain ⟨g, HgAl, Hglo, Hghi, Hfree⟩ := higher_fit_b_sound maps aZ nZ baseZ Hf
      rw [H g HgAl Hglo Hghi] at Hfree
      cases Hfree

-- The zero floor exercises the non-strict premise of `no_higher_fit_iff`.
example : higher_fit_b [] 0 4096 4096 = false ↔ no_higher_fit [] 0 4096 4096 :=
  no_higher_fit_iff [] 0 4096 4096 (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! ## The placement witness

One concrete address for a proof that wants to compute one, rather than a
reproduction of Linux's placement algorithm. In Linux v6.18.46
(`1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`), `setup_new_exec` (fs/exec.c)
calls the architecture's layout selector. The generic `arch_pick_mmap_layout`
(mm/util.c, v6.18.46) chooses via `mmap_is_legacy` (mm/util.c, v6.18.46) and,
under `PF_RANDOMIZE`, offsets the base using `arch_mmap_rnd` (mm/util.c,
v6.18.46). The searches `unmapped_area` and `unmapped_area_topdown` (mm/vma.c,
v6.18.46) walk the VMA tree, with their lower bound raised to `mmap_min_addr`,
rather than this proof's ledger candidates. The Rocq section note explains
why this deterministic witness serves proofs about the admitted placements. -/

/-- The candidate list for a search from a floor rather than from a
grant's end.  `higher_fit_b_as_place` relates it to `fit_candidates`, so
the completeness argument transfers instead of being redone. -/
def search_candidates (maps : List (word × word)) (loZ : Int) : List Int :=
  loZ :: maps.map (fun p => page_round_up_Z (bv_unsigned p.1 + bv_unsigned p.2))

/-- `g` is page-aligned and at or above `loZ`, `g + nZ` is at or below
`hiZ`, and `region_free maps` accepts the words `Z_to_bv 64 g` and
`Z_to_bv 64 nZ`: for `nZ < 2^64`, under `0 ≤ g`, `0 ≤ nZ` and
`g + nZ ≤ 2^64`, `[g, g+nZ)` is disjoint from each entry's integer interval
`[start, start + size)`. Interpreting this as free bytes also requires that
no entry wraps past `2^64`: a wrapping entry's low part is not seen.
Outside those bounds, acceptance concerns the integer interval of the
converted words. The examples below pin the missing wrapped low parts of
the candidate and a ledger entry, and the need for `nZ < 2^64` when
converting the length. -/
def place_fits (maps : List (word × word)) (loZ hiZ nZ : Int) (g : Int) : Bool :=
  decide (g % page_size = 0) && decide (loZ ≤ g) && decide (g + nZ ≤ hiZ)
  && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ)

-- These 8192 bytes wrap onto the mapped [0, 4096) at the model's address walk,
-- and `region_free` still answers true, which is why the docstring bounds g + nZ.
example : region_free [(Z_to_bv 64 0, Z_to_bv 64 4096)]
    (Z_to_bv 64 (2^64 - 4096)) (Z_to_bv 64 8192) = true := by decide

-- At g = 0, nZ = 2^64, the sum bound holds but the length converts to zero.
example : region_free [(Z_to_bv 64 0, Z_to_bv 64 4096)]
    (Z_to_bv 64 0) (Z_to_bv 64 (2^64)) = true := by decide

-- This pins that a wrapping entry's low part is not seen.
example : place_fits [(Z_to_bv 64 (2^64 - 4096), Z_to_bv 64 8192)]
    0 4096 4096 0 = true := by decide

def place (maps : List (word × word)) (loZ hiZ nZ : Int) : Option Int :=
  (search_candidates maps loZ).find? (place_fits maps loZ hiZ nZ)

/-! ### Soundness: what comes out satisfies the conditions -/

theorem place_sound : ∀ maps loZ hiZ nZ a,
    place maps loZ hiZ nZ = some a →
    a % page_size = 0 ∧ loZ ≤ a ∧ a + nZ ≤ hiZ
    ∧ region_free maps (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true := by
  intro maps loZ hiZ nZ a H
  unfold place at H
  have Hf := List.find?_some H
  unfold place_fits at Hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at Hf
  obtain ⟨⟨⟨Hal, Hlo⟩, Hhi⟩, Hfree⟩ := Hf
  exact ⟨Hal, Hlo, Hhi, Hfree⟩

/-! ### Completeness: under `place_complete`'s premises, if an address fits, `place` finds one -/

theorem existsb_find : ∀ {A : Type _} (f : A → Bool) (l : List A),
    l.any f = true → ∃ x, l.find? f = some x := by
  intro A f l
  induction l with
  | nil => intro h; cases h
  | cons y l ih =>
    intro h
    cases hy : f y with
    | true => exact ⟨y, List.find?_cons_of_pos hy⟩
    | false =>
      rw [List.any_cons, hy, Bool.false_or] at h
      obtain ⟨x, hx⟩ := ih h
      exact ⟨x, by rw [List.find?_cons_of_neg (by rw [hy]; decide)]; exact hx⟩

-- This theorem restates the lemma with `A` in a universe `w` the line declares,
-- so it builds only while `A`'s universe is a parameter of the lemma. The
-- testing/lean-mutations case `common-existsb-find-universe-zero` narrows the
-- binder to `Type` and expects the restatement to fail
-- (docs/lean-port/BRIEF.md section 3, "Universes").
universe w in
theorem existsb_find_any_universe : ∀ {A : Type w} (f : A → Bool) (l : List A),
    l.any f = true → ∃ x, l.find? f = some x :=
  existsb_find

-- Rocq's A may be a proposition such as True, by cumulativity (the header);
-- Lean's binder A : Type _ refuses one. The docstring is the whole expected
-- error, so a different failure (an unknown name, a reordered argument) fails
-- the #guard_msgs.
/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @existsb_find True -/
#guard_msgs in
set_option pp.mvars false in
example := @existsb_find True

/-- A search from `loZ` walks the candidate list `fit_candidates` builds
for a grant ending at `loZ`, and `higher_fit_b`'s fitting test agrees with
`place_fits` on it. -/
theorem higher_fit_b_as_place : ∀ maps loZ hiZ nZ,
    higher_fit_b maps (loZ - nZ) nZ hiZ
    = (search_candidates maps loZ).any (place_fits maps loZ hiZ nZ) := by
  intro maps loZ hiZ nZ
  unfold higher_fit_b fit_candidates search_candidates
  rw [Int.sub_add_cancel]
  rfl

/-- The nonemptiness obligation, conditional on a witness gap.  Why the
unconditional form is not available (a full ledger has no gap:
`place_finds_nothing_when_full`) is on the Rocq lemma. -/
theorem place_complete : ∀ maps loZ hiZ nZ g,
    0 ≤ loZ → 0 < nZ →
    loZ % page_size = 0 → nZ % page_size = 0 →
    hiZ < two_pow_64 →
    g % page_size = 0 → loZ ≤ g → g + nZ ≤ hiZ →
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true →
    ∃ a, place maps loZ hiZ nZ = some a := by
  intro maps loZ hiZ nZ g Hlo0 Hn Hloal Hnal Hhi HgAl Hglo Hghi Hfree
  apply existsb_find
  rw [← higher_fit_b_as_place]
  apply higher_fit_b_complete maps (loZ - nZ) nZ hiZ g
  · omega
  · exact Hn
  · simp only [page_size] at Hloal Hnal ⊢
    omega
  · exact Hnal
  · exact Hhi
  · exact HgAl
  · omega
  · exact Hghi
  · exact Hfree

/-! ### The two together, at the model's own interval -/

/-- The floor `page_size` is what gives `place_in_model_admissible` its
`0 < bv_unsigned (Z_to_bv 64 a)` conjunct. -/
def place_in_model (h : VmMaps) (nZ : Int) : Option Int :=
  place (h.vm_reserved ++ h.vm_maps) page_size (alloc_top h) nZ

/-- Soundness against the placement conditions, concluded at
`bv_unsigned (Z_to_bv 64 a)` with the round trip as its first conjunct;
why, and what `0 ≤ nZ` closes, is on the Rocq lemma. -/
theorem place_in_model_admissible : ∀ h nZ a,
    0 ≤ nZ →
    place_in_model h nZ = some a →
    bv_unsigned (Z_to_bv 64 a) = a
    ∧ bv_unsigned (Z_to_bv 64 a) % page_size = 0
    ∧ 0 < bv_unsigned (Z_to_bv 64 a)
    ∧ bv_unsigned (Z_to_bv 64 a) + nZ ≤ alloc_top h
    ∧ region_free (h.vm_reserved ++ h.vm_maps) (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true := by
  intro h nZ a Hn H
  unfold place_in_model at H
  obtain ⟨Hal, Hlo, Hhi, Hfree⟩ := place_sound _ _ _ _ _ H
  have Htop := alloc_top_lt h
  unfold two_pow_64 at Htop
  simp only [page_size] at Hlo
  have Hrt : bv_unsigned (Z_to_bv 64 a) = a :=
    bv_unsigned_Z_to_bv_small a (by omega) (by omega)
  rw [Hrt]
  exact ⟨rfl, Hal, by omega, Hhi, Hfree⟩

/-- At `mkVmMaps [] [] 0 0 0`, whose ledger is empty, a negative length
gets the floor back.  `place` does not check the length's sign; the
`0 ≤ nZ` premise of `place_in_model_admissible` rules the case out. -/
theorem place_accepts_a_negative_length :
    place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = some 4096 := by
  decide

theorem place_in_model_complete : ∀ h nZ g,
    0 < nZ → nZ % page_size = 0 →
    g % page_size = 0 → page_size ≤ g →
    g + nZ ≤ alloc_top h →
    region_free (h.vm_reserved ++ h.vm_maps) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true →
    ∃ a, place_in_model h nZ = some a := by
  intro h nZ g Hn Hnal HgAl Hglo Hghi Hfree
  unfold place_in_model
  exact place_complete _ _ _ _ g (by simp only [page_size]; omega) Hn (by decide) Hnal
    (alloc_top_lt h) HgAl Hglo Hghi Hfree

/-! ### That the completeness lemma is not vacuous

`place_complete_premises_are_satisfiable` states `place_complete`'s
premises at `witness_ledger`, with the address
`place_skips_the_occupied_floor` shows the search returning there as the
witness; `place_finds_nothing_when_full` exhibits a ledger where the
search returns `none`. -/

def witness_ledger : List (word × word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 8192)]

/-- The top a hand-built ledger stands under (`mkVmMaps` seeds the stack
pointer at the bottom of the SP window).
Protected to distinguish `LinuxProcessSem/Checks/Cases/Prelude.lean`'s `demo_top`,
defined there as `sp_window_lo - stack_max_size`. -/
protected def demo_top : Int := alloc_top (mkVmMaps [] [] 0 0 0)

/-- The search skips an occupied candidate: `page_size` is inside the
entry, so the answer is the entry's page-rounded end. -/
theorem place_skips_the_occupied_floor :
    place witness_ledger page_size PlacementSearch.demo_top 4096 = some 12288 := by
  decide

/-- The premises of `place_complete` hold at that instance, with the
address the search returned as the witness. -/
theorem place_complete_premises_are_satisfiable :
    0 ≤ page_size ∧ (0 : Int) < 4096
    ∧ page_size % page_size = 0 ∧ (4096 : Int) % page_size = 0
    ∧ PlacementSearch.demo_top < two_pow_64
    ∧ (12288 : Int) % page_size = 0 ∧ page_size ≤ 12288
    ∧ 12288 + 4096 ≤ PlacementSearch.demo_top
    ∧ region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true := by
  decide

/-- One entry covering `[4096, demo_top)`, the interval a search from
`page_size` to `demo_top` walks.  That the `none` below is about the
witness and not about the spec's errno arm is the Rocq note on this
definition. -/
def full_ledger : List (word × word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 (PlacementSearch.demo_top - 4096))]

theorem place_finds_nothing_when_full :
    place full_ledger page_size PlacementSearch.demo_top 4096 = none := by
  decide

end LinuxProcessSemantics.Common.PlacementSearch
