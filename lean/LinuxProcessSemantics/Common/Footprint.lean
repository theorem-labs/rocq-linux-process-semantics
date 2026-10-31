import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: 7ba58b45f168d97ca1a555a98fa3b36f29eb5b81 -/

/-! # Common.Footprint — concrete address regions and their disjointness

Ported whole from `theories/Common/Footprint.v`, with the Rocq statements
(ticket E-proof-library-2a).  The file was read at the commit named above
(`nightly/09-28-2026`).

Why the vocabulary is concrete rather than symbolic, and which proof
strategies share it, is argued in the Rocq file's header.  The Rocq
`SymExec` lemmas that discharge the executor's `SCFlat` and `SCDisjoint`
obligations through it (`sc_flat_of_region`; `sc_disjoint_of_regions`
and `sc_disjoint_same_region`) are among the names `Common/SymExec.lean`
lists as unported, until that file ports them.

Representation spellings:
- Rocq `Z` is `Int` and `Z.of_nat n` is the cast `(n : Int)`.
- The record keeps Rocq's constructor name `Rg`, exported so `Rg lo hi`
  transcribes unqualified; its fields are read with dot notation.
- Rocq `Forall P l` is `∀ r ∈ l, P r`, and `nth i l d` is `l.getD i d`
  (`layout_wf`). -/

namespace LinuxProcessSemantics.Common.Footprint

open LinuxProcessSemantics.Riscv.Prelude

/-! ## 1. Regions -/

/-- A half-open byte interval `[rg_lo, rg_hi)` of the 64-bit address
space.  Its bounds are unconstrained here; `rg_wf` carries them. -/
structure region : Type where
  Rg ::
  rg_lo : Int
  rg_hi : Int

export region (Rg)

def rg_wf (r : region) : Prop :=
  0 ≤ r.rg_lo ∧ r.rg_lo ≤ r.rg_hi ∧ r.rg_hi ≤ 2 ^ 64

/-- Stated on `bv_unsigned` so that a caller's arithmetic facts about an
address (`sp_window_lo ≤ bv_unsigned rsp`, an image's segment bounds)
apply directly. -/
def covers (r : region) (a : word) (n : Nat) : Prop :=
  r.rg_lo ≤ bv_unsigned a ∧ bv_unsigned a + (n : Int) ≤ r.rg_hi

def rg_disj (r1 r2 : region) : Prop :=
  r1.rg_hi ≤ r2.rg_lo ∨ r2.rg_hi ≤ r1.rg_lo

theorem rg_disj_sym : ∀ r1 r2, rg_disj r1 r2 → rg_disj r2 r1 := by
  intro r1 r2 h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Growing a region preserves coverage. -/
theorem covers_mono : ∀ r r' a n,
    covers r a n → r'.rg_lo ≤ r.rg_lo → r.rg_hi ≤ r'.rg_hi → covers r' a n := by
  intro r r' a n h hl hh
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

/-! ## 2. The three consequences a memory proof uses -/

/-- (a) An access inside a well-formed region does not wrap the address
space. -/
theorem covers_nowrap : ∀ r a n,
    rg_wf r → covers r a n → bv_unsigned a + (n : Int) ≤ 2 ^ 64 := by
  intro r a n hwf h
  obtain ⟨_, _, hhi⟩ := hwf
  obtain ⟨_, h2⟩ := h
  omega

/-- (b) Two accesses in disjoint regions are ordered as `Int` intervals,
one ending at or below the other's start: the ordering premise of
`rdn_wbytes_disjoint` / `rdn_wbytes_below` (`Common/CatExec.lean`).  With
(a) for both accesses, which needs `rg_wf`, that is disjointness in the
address space; this lemma does not assume `rg_wf`. Pinned by
`StoreOk.covers_disj_wbytes`, `StoreOk.covers_disj_wrapping_region`, and
`StoreOk.covers_disj_wrapping_readback`. -/
theorem covers_disj : ∀ r1 r2 a1 n1 a2 n2,
    rg_disj r1 r2 → covers r1 a1 n1 → covers r2 a2 n2 →
    bv_unsigned a1 + (n1 : Int) ≤ bv_unsigned a2
    ∨ bv_unsigned a2 + (n2 : Int) ≤ bv_unsigned a1 := by
  intro r1 r2 a1 n1 a2 n2 hd h1 h2
  obtain ⟨h1l, h1h⟩ := h1
  obtain ⟨h2l, h2h⟩ := h2
  rcases hd with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- (c) Two accesses in the same region are ordered as `Int` intervals
when their offsets say so: the lemma returns that hypothesis, and the
coverage hypotheses are not used, as in Rocq.  As in (b), that is
disjointness in the address space once (a) applies to both accesses,
which needs `rg_wf`. The result type is pinned by
`StoreOk.covers_same_disj_returns_order`. -/
theorem covers_same_disj : ∀ r a1 n1 a2 n2,
    covers r a1 n1 → covers r a2 n2 →
    bv_unsigned a1 + (n1 : Int) ≤ bv_unsigned a2
    ∨ bv_unsigned a2 + (n2 : Int) ≤ bv_unsigned a1 →
    bv_unsigned a1 + (n1 : Int) ≤ bv_unsigned a2
    ∨ bv_unsigned a2 + (n2 : Int) ≤ bv_unsigned a1 := by
  intro _ _ _ _ _ _ _ h
  exact h

/-! ## 3. The regions the examples have -/

/-- The frame window around `sp`.  Why the bytes below `sp` and those at
and above it are separate arguments is the Rocq definition's note. -/
def stack_rg (sp : word) (below above : Int) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above)

/-- A writable ELF segment, by literal bounds. -/
def seg_rg (lo hi : Int) : region := Rg lo hi

/-- A heap grant `[base, base + cur)`. -/
def heap_rg (base : word) (cur : Int) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur)

theorem heap_rg_bump : ∀ base cur cur' a n,
    cur ≤ cur' → covers (heap_rg base cur) a n → covers (heap_rg base cur') a n := by
  intro base cur cur' a n hle h
  refine covers_mono (heap_rg base cur) (heap_rg base cur') a n h ?_ ?_
  · show bv_unsigned base ≤ bv_unsigned base
    omega
  · show bv_unsigned base + cur ≤ bv_unsigned base + cur'
    omega

/-- A list of well-formed, pairwise disjoint regions. -/
def layout_wf (rs : List region) : Prop :=
  (∀ r ∈ rs, rg_wf r) ∧
  ∀ i j, i < j → j < rs.length →
    rg_disj (rs.getD i (Rg 0 0)) (rs.getD j (Rg 0 0))

end LinuxProcessSemantics.Common.Footprint
