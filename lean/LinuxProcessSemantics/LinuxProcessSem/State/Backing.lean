import LinuxProcessSemantics.LinuxProcessSem.State.Effects
import LinuxProcessSemantics.LinuxProcessSem.State.Model

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Backing — atomic first-access accounting

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: the "Atomic first-access accounting" section of
`State.v` — the pages a syscall's accesses touch, the lazily backed
ranges and the materialized pages a `Model` records, the backing
charge and its limit — and the `mremap` half of ticket A11 that moves
that metadata with a mapping.  The boundary is Rocq's: a definition of
that section belongs here whether or not it takes a `Model` (the page
helpers do not); the section's `VmMaps`-only helpers are `State/Vm.lean`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## Atomic first-access accounting -/

def page_base_of (z : Int) : word := Z_to_bv 64 ((z / page_size) * page_size)
def page_base (a : word) : word := page_base_of (bv_unsigned a)

def page_mem (p : word) (pages : List word) : Bool := pages.any (bv_eqb p)
def page_insert (p : word) (pages : List word) : List word :=
  if page_mem p pages then pages else p :: pages

/-- The byte cursor advances in `Int`, not by bitvector `+`. -/
def access_pages_acc (base : Int) (n : Nat) (pages : List word) : List word :=
  match n with
  | 0 => pages
  | n' + 1 => access_pages_acc (base + 1) n' (page_insert (page_base_of base) pages)

def access_pages (a : word) (n : Nat) : List word :=
  access_pages_acc (bv_unsigned a) n []

def accesses_pages (accesses : List (word × Nat)) (pages : List word) : List word :=
  match accesses with
  | [] => pages
  | (a, n) :: rest => accesses_pages rest (access_pages_acc (bv_unsigned a) n pages)

def page_in_ranges (p : word) (ranges : List (word × word)) : Bool :=
  ranges.any (fun r =>
    let lo := bv_unsigned r.1
    let hi := lo + bv_unsigned r.2
    lo ≤ bv_unsigned p && bv_unsigned p + page_size ≤ hi)

def newly_materialized_pages (lazy : List (word × word))
    (materialized : List word) (accesses : List (word × Nat)) : List word :=
  (accesses_pages accesses []).filter
    (fun p => page_in_ranges p lazy && !(page_mem p materialized))

def materialize_accesses (lazy : List (word × word))
    (materialized : List word) (used limit : Int)
    (accesses : List (word × Nat)) : Option (List word) :=
  let new := newly_materialized_pages lazy materialized accesses
  match new with
  | [] => some materialized
  | _ =>
      if used + (new.length : Int) * page_size ≤ limit
      then some (new ++ materialized)
      else none

/-- A live process's backing charge. -/
def vm_backing_used (m : Model) : Int :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m))
  + ((m_vm_materialized m).length : Int) * page_size

def vm_backing_within_limit (m : Model) : Bool :=
  vm_backing_used m ≤ (m_vmmaps m).vm_limit

def materialize_model_accesses (m : Model) (accesses : List (word × Nat)) : Option Model :=
  match materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
          (vm_backing_used m) (m_vmmaps m).vm_limit accesses with
  | some pages => some (with_vm_backing (m_vm_lazy m) pages m)
  | none => none

def page_outside_range (lo hi : Int) (p : word) : Bool :=
  !(lo ≤ bv_unsigned p && bv_unsigned p < hi)

def vm_forget_range (lo hi : Int) (m : Model) : Model :=
  with_vm_backing
    (maps_subtract (m_vm_lazy m) lo hi)
    ((m_vm_materialized m).filter (page_outside_range lo hi)) m

/-- The page-aligned INTERIOR of `[a, a+n)`: what a MAP_NORESERVE grant
records as lazily backed.  Every caller is page-aligned already, so this
is the identity on the reachable domain; an unaligned caller records LESS
than it asked for, which over-charges — the safe direction (the argument
is on the Rocq definition, `State.lazy_interior`). -/
def lazy_interior (a n : word) : List (word × word) :=
  let lo := bv_unsigned a
  let hi := lo + bv_unsigned n
  let lo' := ((lo + page_size - 1) / page_size) * page_size
  let hi' := (hi / page_size) * page_size
  if lo' < hi' then [(Z_to_bv 64 lo', Z_to_bv 64 (hi' - lo'))] else []

def vm_add_lazy (a n : word) (m : Model) : Model :=
  with_vm_backing (lazy_interior a n ++ m_vm_lazy m) (m_vm_materialized m) m

theorem page_in_ranges_nil (p : word) : page_in_ranges p [] = false := rfl

theorem newly_materialized_pages_no_lazy (materialized : List word)
    (accesses : List (word × Nat)) :
    newly_materialized_pages [] materialized accesses = [] := by
  unfold newly_materialized_pages
  induction accesses_pages accesses [] with
  | nil => rfl
  | cons p pages _ => simp [List.filter, page_in_ranges_nil]

theorem materialize_model_accesses_no_lazy (m : Model) (accesses : List (word × Nat)) :
    m_vm_lazy m = [] → materialize_model_accesses m accesses = some m := by
  intro hlazy
  unfold materialize_model_accesses materialize_accesses
  rw [hlazy, newly_materialized_pages_no_lazy]
  simp only
  cases m with
  | mkModelOf fd vm io fs proc lim time =>
    cases vm with
    | mkVmState maps lazy materialized =>
      simp only [m_vm_lazy] at hlazy
      subst hlazy
      rfl

def write_accesses (writes : List (word × List byte)) : List (word × Nat) :=
  match writes with
  | [] => []
  | (a, bs) :: rest => (a, bs.length) :: write_accesses rest

/-- User-memory ranges named by a successful syscall effect. -/
def syscall_effect_accesses (eff : SyscallEffect) : List (word × Nat) :=
  eff.eff_copyins ++ write_accesses eff.eff_writes

theorem materialize_model_accesses_frame (m : Model) (accesses : List (word × Nat)) (m' : Model) :
    materialize_model_accesses m accesses = some m' →
    m'.m_fd = m.m_fd ∧
    m_vmmaps m' = m_vmmaps m ∧
    m_vm_lazy m' = m_vm_lazy m ∧
    m'.m_io = m.m_io ∧
    m'.m_fsys = m.m_fsys ∧
    m'.m_proc = m.m_proc ∧
    m'.m_lim = m.m_lim := by
  intro h
  unfold materialize_model_accesses at h
  cases hm : materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
      (vm_backing_used m) (m_vmmaps m).vm_limit accesses with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some pages =>
    rw [hm] at h
    cases h
    simp [with_vm_backing, m_vmmaps, m_vm_lazy]

/-! ### Ticket A11: moving the backing metadata with a mapping

Ported by ticket A11 beside what it serves; `vm_resize_backing` reads
`lazy_interior`, which the mmap port defined above.  The docstring
points at the Rocq definition for the argument in full. -/

/-- Move or resize the sparse-backing metadata belonging to one whole
anonymous mapping.  `source_lazy` says the source is uniformly
MAP_NORESERVE; callers reject mixed lazy/eager sources.  Materialized
pages retain their source-relative offset, pages cut by a shrink are
released, and a grown lazy tail starts unmaterialized.  Destination
metadata is removed first so even a hand-built stale ledger cannot
manufacture backing by colliding with the move.  The kernel behaviour
this tracks is `mremap`'s: a shrink unmaps the excess (`shrink_vma`,
mm/mremap.c, Linux v6.18.46, commit 1f99e9ab748f, → `do_vmi_munmap`,
mm/vma.c, same version) and
a move carries the page tables over (`copy_vma_and_data` →
`move_page_tables`, mm/mremap.c, with the VMA copied by `copy_vma`,
mm/vma.c, same version); the grown delta's zero-fill is argued on
`Sys/Mm/Mremap.v`.  Rocq: `State.vm_resize_backing`. -/
def vm_resize_backing (source_lazy : Bool) (old old_n dst new_n : word)
    (m : Model) : Model :=
  let old_lo := bv_unsigned old
  let old_hi := old_lo + bv_unsigned old_n
  let dst_lo := bv_unsigned dst
  let dst_hi := dst_lo + bv_unsigned new_n
  let kept_lazy :=
    maps_subtract (maps_subtract (m_vm_lazy m) old_lo old_hi) dst_lo dst_hi
  let kept_pages :=
    ((m_vm_materialized m).filter (page_outside_range old_lo old_hi)).filter
      (page_outside_range dst_lo dst_hi)
  let moved_pages :=
    if source_lazy then
      ((m_vm_materialized m).filter
        (fun p => page_in_half_open old_lo old_hi p
                  && bv_unsigned p - old_lo < bv_unsigned new_n)).map
        (move_page_base old dst)
    else []
  with_vm_backing
    (if source_lazy then lazy_interior dst new_n ++ kept_lazy else kept_lazy)
    (moved_pages ++ kept_pages) m

end LinuxProcessSemantics.LinuxProcessSem.State
