-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/State.v
import LinuxProcessSemantics.LinuxProcessSem.State.Geometry

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Vm — the virtual-memory ledger

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: the allocator decisions the model has committed to
(`VmMaps`, its byte counts, `alloc_top`), the interval arithmetic
over the ledger, and the ledger-only helpers of ticket A11.  Nothing
here reads a `Model`: the first-access accounting over the model is
`State/Backing.lean`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-- Virtual-memory bookkeeping: the allocator decisions the model has
committed to (see the Rocq field notes). -/
structure VmMaps where
  mkVmMapsFull ::
  vm_reserved  : List (word × word)
  vm_maps      : List (word × word)
  vm_noaccess  : List (word × word)
  vm_start_brk : word
  vm_brk       : word
  vm_limit     : Int
  vm_mmap_base : word
  vm_init_sp   : word

def live_bytes (maps : List (word × word)) : Int :=
  match maps with
  | [] => 0
  | (_, sz) :: r => bv_unsigned sz + live_bytes r
def vm_live_bytes (h : VmMaps) : Int := live_bytes h.vm_maps

/-- The highest address any reservation reaches: the page-rounded image
top when applied to `Run.segments_reserved`. -/
def reserved_top (maps : List (word × word)) : Int :=
  match maps with
  | [] => 0
  | (a, sz) :: r => max (bv_unsigned a + bv_unsigned sz) (reserved_top r)

/-- ALLOCATION TOP: no allocator grant may reach at or above this address,
so every grant is disjoint from the dynamic stack `[sp - stack_max_size, sp)`
and from the argv/envp/auxv block above `sp` — for the `sp` THIS run was
started with.  A bound rather than a reservation entry, so a symbolic `sp`
stays one `Int` atom; the argument, and what a hinted grant into the stack
band costs, is on the Rocq definition (`State.alloc_top`). -/
def alloc_top (h : VmMaps) : Int := bv_unsigned h.vm_init_sp - stack_max_size

/-- The whole stack fits above the top, so a grant ending at or below it
ends a stack's width short of `2^64`: its address can never be read as an
encoded errno. -/
theorem alloc_top_room (h : VmMaps) : alloc_top h + stack_max_size < two_pow_64 := by
  unfold alloc_top two_pow_64 stack_max_size bv_unsigned
  have := h.vm_init_sp.isLt
  omega

theorem alloc_top_lt (h : VmMaps) : alloc_top h < two_pow_64 := by
  have := alloc_top_room h
  unfold stack_max_size at this
  omega

/-- One page above the top is still an address: the brk gate tests the
page above the installed ones (`Sys/Mm/Mmap.brk_grow_ok`), and this
is the bound that keeps that range from wrapping. -/
theorem alloc_top_page_lt (h : VmMaps) : alloc_top h + page_size < two_pow_64 := by
  have := alloc_top_room h
  unfold stack_max_size page_size at *
  omega

/-- The five-field ledger the worked examples build: no no-access ranges,
no mmap base recorded, and the stack pointer at the BOTTOM of the SP
window, so a hand-built ledger's `alloc_top` is the lowest any admissible
run has. -/
def mkVmMaps (reserved maps : List (word × word)) (start_brk brk : word)
    (limit : Int) : VmMaps :=
  VmMaps.mkVmMapsFull reserved maps [] start_brk brk limit (Z_to_bv 64 0)
    (Z_to_bv 64 sp_window_lo)

/-! ## Interval arithmetic on the VM ledger -/

def iv_overlap (a1 n1 a2 n2 : word) : Bool :=
  bv_unsigned a1 < bv_unsigned a2 + bv_unsigned n2
  && bv_unsigned a2 < bv_unsigned a1 + bv_unsigned n1

/-- Is `[lo, lo+n)` disjoint from every live mapping? -/
def region_free (maps : List (word × word)) (lo n : word) : Bool :=
  match maps with
  | [] => true
  | (a, sz) :: r => !(iv_overlap lo n a sz) && region_free r lo n

/-- Does ONE entry of `maps` cover `[lo, lo+n)` whole?  The containment
gate of the in-place MAP_FIXED shapes and of `mprotect`: a range covered by
two adjacent entries is NOT contained. -/
def map_contains (maps : List (word × word)) (lo n : word) : Bool :=
  maps.any (fun p =>
    let aZ := bv_unsigned p.1
    let hiZ := aZ + bv_unsigned p.2
    aZ ≤ bv_unsigned lo && bv_unsigned lo + bv_unsigned n ≤ hiZ)

def iv_subtract (a sz : word) (loZ hiZ : Int) : List (word × word) :=
  let aZ := bv_unsigned a
  let szZ := bv_unsigned sz
  let left := if aZ < loZ then [(a, Z_to_bv 64 (min szZ (loZ - aZ)))] else []
  let right := if hiZ < aZ + szZ
               then [(Z_to_bv 64 (max aZ hiZ), Z_to_bv 64 (aZ + szZ - max aZ hiZ))]
               else []
  left ++ right

def maps_subtract (maps : List (word × word)) (lo hi : Int) : List (word × word) :=
  match maps with
  | [] => []
  | (a, sz) :: r => iv_subtract a sz lo hi ++ maps_subtract r lo hi

def maps_subtract_all (maps cuts : List (word × word)) : List (word × word) :=
  match cuts with
  | [] => maps
  | (a, n) :: rest =>
      maps_subtract_all
        (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
        rest

def vm_backed_maps (h : VmMaps) : List (word × word) :=
  maps_subtract_all h.vm_maps h.vm_noaccess

/-! ### Ticket A11: the ledger helpers `mremap` and `munmap` read

One delimited block, appended as BRIEF.md section 4 asks rather than
interleaved where Rocq keeps each (`map_remove` next to `reserved_top`,
`vm_backed_bytes` in the same VmMaps section as the backed maps).  Each
docstring points at the Rocq definition for the argument in full.  The
Model-level half of that ticket, `vm_resize_backing`, is in
`State/Backing.lean`; the privilege test and the UTS pin are in
`State/Model.lean`. -/

/-- Drop any mapping based at `lo` (munmap of a whole anonymous mapping).
Rocq: `State.map_remove`. -/
def map_remove (maps : List (word × word)) (lo : word) : List (word × word) :=
  maps.filter (fun p => !(bv_eqb p.1 lo))

/-- Is `(lo, n)` exactly one of the live-mapping entries?  munmap's
modeled case: the requested range coincides with a whole recorded
mapping.  Linux itself splits a VMA on a partial unmap
(`vms_gather_munmap_vmas` → `__split_vma`, mm/vma.c, Linux v6.18.46,
commit 1f99e9ab748f); the model does not follow it there, and this
predicate is how `Mmap.munmap_spec` tells the whole-mapping case from
the one it declines.  Rocq: `State.map_has`. -/
def map_has (maps : List (word × word)) (lo n : word) : Bool :=
  maps.any (fun p => bv_eqb p.1 lo && bv_eqb p.2 n)

/-- Exposed capacity of a ledger alone: the live mappings with every
inaccessible interval cut out.  NOT a live process's backing charge —
that is `vm_backing_used`, which also cuts the lazy ranges out and adds
the materialized pages back.  Which of the two a site should ask is
argued on the Rocq definition, `State.vm_backed_bytes`. -/
def vm_backed_bytes (h : VmMaps) : Int := live_bytes (vm_backed_maps h)

/-- Rocq: `State.page_in_half_open`, `vm_resize_backing`'s selector for
the source's pages. -/
def page_in_half_open (lo hi : Int) (p : word) : Bool :=
  lo ≤ bv_unsigned p && bv_unsigned p < hi

/-- A materialized page's address once its mapping moved from `old` to
`dst`: the source-relative offset is kept.  Rocq: `State.move_page_base`. -/
def move_page_base (old dst p : word) : word :=
  Z_to_bv 64 (bv_unsigned dst + (bv_unsigned p - bv_unsigned old))

/-- The ledger invariant that keeps allocator placement off protected
memory without `vm_noaccess` ever being consulted: every protected byte
lies on a page some live `vm_maps` entry still touches, and no protected
entry is empty.  Deliberately weaker than "`vm_noaccess` ⊆ `vm_maps`",
which a brk shrink inside its final page genuinely breaks; the
nonemptiness conjunct is what stops a vacuous entry from blocking a
request that touches no protected byte.  The full argument, and what
remains unproved (preservation by the writers of `vm_noaccess`), is on
the Rocq definition, `State.noaccess_pages_owned`. -/
def noaccess_pages_owned (h : VmMaps) : Prop :=
  ∀ a n, (a, n) ∈ h.vm_noaccess →
    0 < bv_unsigned n ∧
    ∀ x, bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned n →
      ∃ b s, (b, s) ∈ h.vm_maps ∧
        (bv_unsigned b < page_round_down_Z x + page_size ∧
         page_round_down_Z x < bv_unsigned b + bv_unsigned s)

/-! ### The nonempty-entry facts the allocator proofs read

`f1006fe8` adds these to `State.v` for the memory arms: `Mm.Mmap`,
`Mm.Mprotect` and `Mm.Madvise` each need to know that a ledger they
built has no empty entry.  Ported under the Rocq names. -/

/-- A `region_free` that says `false` exhibits the entry that overlaps.
Rocq: `State.region_free_false`. -/
theorem region_free_false (maps : List (word × word)) (lo n : word)
    (h : region_free maps lo n = false) :
    ∃ a sz, (a, sz) ∈ maps ∧ iv_overlap lo n a sz = true := by
  induction maps with
  | nil => simp [region_free] at h
  | cons p r ih =>
    obtain ⟨b, s⟩ := p
    cases hov : iv_overlap lo n b s with
    | true => exact ⟨b, s, List.mem_cons_self .., hov⟩
    | false =>
      simp only [region_free, hov, Bool.not_false, Bool.true_and] at h
      obtain ⟨a, sz, hin, h2⟩ := ih h
      exact ⟨a, sz, List.mem_cons_of_mem _ hin, h2⟩

/-- No entry of the ledger is empty.  Rocq: `State.entries_nonzero`. -/
def entries_nonzero (maps : List (word × word)) : Prop :=
  ∀ a n, (a, n) ∈ maps → 0 < bv_unsigned n

/-- Rocq: `State.entries_nonzero_nil`. -/
theorem entries_nonzero_nil : entries_nonzero [] := by
  intro a n h
  cases h

/-- Rocq: `State.entries_nonzero_forallb`. -/
theorem entries_nonzero_forallb (maps : List (word × word))
    (h : maps.all (fun p => 0 < bv_unsigned p.2) = true) : entries_nonzero maps := by
  intro a n hin
  rw [List.all_eq_true] at h
  simpa using h (a, n) hin

/-- Rocq: `State.entries_nonzero_cons`. -/
theorem entries_nonzero_cons (a n : word) (r : List (word × word))
    (hn : 0 < bv_unsigned n) (hr : entries_nonzero r) :
    entries_nonzero ((a, n) :: r) := by
  intro b s hin
  rcases List.mem_cons.1 hin with heq | hin'
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hn
  · exact hr b s hin'

/-- Rocq: `State.bv_unsigned_range_u64`. -/
theorem bv_unsigned_range_u64 (w : word) :
    0 ≤ bv_unsigned w ∧ bv_unsigned w < two_pow_64 := by
  unfold bv_unsigned two_pow_64
  have := w.isLt
  omega

/-- Rocq: `State.bv_unsigned_Z_to_bv_u64`. -/
theorem bv_unsigned_Z_to_bv_u64 (z : Int) (hz : 0 ≤ z ∧ z < two_pow_64) :
    bv_unsigned (Z_to_bv 64 z) = z :=
  bv_unsigned_Z_to_bv_small z hz.1 hz.2

/-- Cutting a nonempty interval leaves nonempty pieces: each side is a
strictly shorter prefix or suffix of it.  Rocq: `State.iv_subtract_nonzero`. -/
theorem iv_subtract_nonzero (a sz : word) (loZ hiZ : Int)
    (hsz : 0 < bv_unsigned sz) : entries_nonzero (iv_subtract a sz loZ hiZ) := by
  intro b s hin
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 sz
  unfold two_pow_64 at ha hs
  simp only [iv_subtract] at hin
  rcases List.mem_append.1 hin with hl | hr
  · by_cases h1 : bv_unsigned a < loZ
    · rw [ite_eq_left h1, List.mem_singleton] at hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨-, rfl⟩ := hl
      rw [bv_unsigned_Z_to_bv_u64 _ (by unfold two_pow_64; omega)]
      omega
    · rw [ite_eq_right h1] at hl
      cases hl
  · by_cases h2 : hiZ < bv_unsigned a + bv_unsigned sz
    · rw [ite_eq_left h2, List.mem_singleton] at hr
      simp only [Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      rw [bv_unsigned_Z_to_bv_u64 _ (by unfold two_pow_64; omega)]
      omega
    · rw [ite_eq_right h2] at hr
      cases hr

/-- Rocq: `State.maps_subtract_nonzero`. -/
theorem maps_subtract_nonzero (maps : List (word × word)) (loZ hiZ : Int)
    (h : entries_nonzero maps) : entries_nonzero (maps_subtract maps loZ hiZ) := by
  induction maps with
  | nil => intro b s hin; cases hin
  | cons p r ih =>
    obtain ⟨a, sz⟩ := p
    intro b s hin
    simp only [maps_subtract] at hin
    rcases List.mem_append.1 hin with hl | hr
    · exact iv_subtract_nonzero a sz loZ hiZ (h a sz (List.mem_cons_self ..)) b s hl
    · exact ih (fun x y hx => h x y (List.mem_cons_of_mem _ hx)) b s hr

/-- Rocq: `State.maps_subtract_all_nonzero`. -/
theorem maps_subtract_all_nonzero (cuts maps : List (word × word))
    (h : entries_nonzero maps) : entries_nonzero (maps_subtract_all maps cuts) := by
  induction cuts generalizing maps with
  | nil => exact h
  | cons p rest ih =>
    obtain ⟨a, n⟩ := p
    simp only [maps_subtract_all]
    exact ih _ (maps_subtract_nonzero maps _ _ h)

/-- The protected intervals of a ledger are all nonempty.
Rocq: `State.vm_noaccess_entries_nonzero`. -/
def vm_noaccess_entries_nonzero (h : VmMaps) : Prop :=
  entries_nonzero h.vm_noaccess

/-- The ledger invariant already says it.  Rocq:
`State.noaccess_pages_owned_nonzero`. -/
theorem noaccess_pages_owned_nonzero (h : VmMaps) (hp : noaccess_pages_owned h) :
    vm_noaccess_entries_nonzero h := fun a n hin => (hp a n hin).1

end LinuxProcessSemantics.LinuxProcessSem.State
