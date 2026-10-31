import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.ImageBytes
import LinuxProcessSemantics.Common.AllocSim
import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.SymBranch

/-! # Common.StoreOk — discharging the machine-store bound

Ported from `theories/Common/StoreOk.v` at
2cde689f94c086b868999970834b76a25616b94a, with the Rocq statements.

`RiscvSemantics.store_ok segs m a n` is the premise every machine store
carries: each of the `n` bytes from `a` must be writable in `wview`, the
overlay merged over the 'w' segments.  Proofs never unfold it.  A store
site is one of three shapes and this file turns each into a side
condition: the STACK window `PropExec.wrap_mem` zero-maps up front
(`store_ok_wrap_window`); a writable segment, where `wview` falls through
to the segment image whatever the overlay holds, decided once per image by
`StreamSim.wseg_ok` (`store_ok_window`); and anywhere the proof has
ALREADY stored, since the overlay only grows (`store_ok_mono` and the
`mem_grows` instances).  The monotonicity story is what keeps a port
cheap: a store site deep in a long `wbytes` chain proves its bound against
the ORIGINAL memory and lifts it through the chain. -/

namespace LinuxProcessSemantics.Common.StoreOk

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.StreamSim

/-! ## Overlay growth

`store_ok` only ever asks whether a byte is DEFINED, so the relevant order
on overlays is definedness, not equality: writing bytes, or zero-filling a
grant, can only add. -/

def mem_grows (m m' : word → Option byte) : Prop :=
  ∀ x, m x ≠ none → m' x ≠ none

theorem mem_grows_refl (m : word → Option byte) : mem_grows m m :=
  fun _ h => h

theorem mem_grows_trans (m1 m2 m3 : word → Option byte)
    (h12 : mem_grows m1 m2) (h23 : mem_grows m2 m3) : mem_grows m1 m3 :=
  fun x hx => h23 x (h12 x hx)

/-- `wview`'s segment fallback does not depend on the overlay, so a
byte that was writable stays writable however the overlay grows:
if the overlay had it, the larger one does; if it did not, both
fall through to the same segment. -/
theorem wview_grows (segs : List Segment) (m m' : word → Option byte) (x : word)
    (hg : mem_grows m m') (hx : wview segs m x ≠ none) : wview segs m' x ≠ none := by
  unfold wview at hx ⊢
  cases hm' : m' x with
  | some b' => exact Option.some_ne_none b'
  | none =>
    cases hm : m x with
    | some b => exact absurd hm' (hg x (by rw [hm]; exact Option.some_ne_none b))
    | none =>
      rw [hm] at hx
      exact hx

theorem store_ok_mono (segs : List Segment) (n : Nat) (m m' : word → Option byte) (a : word)
    (hg : mem_grows m m') (h : store_ok segs m a n = true) : store_ok segs m' a n = true := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    cases hv : wview segs m a with
    | none =>
      simp only [store_ok, hv] at h
      cases h
    | some b =>
      simp only [store_ok, hv] at h
      cases hv' : wview segs m' a with
      | some b' =>
        simp only [store_ok, hv']
        exact ih (a + 1) h
      | none =>
        exact absurd hv' (wview_grows segs m m' a hg (by rw [hv]; exact Option.some_ne_none b))

/-! ### The overlay operations grow it -/

theorem wbytes_grows (bs : List byte) (m : word → Option byte) (a : word) :
    mem_grows m (wbytes m a bs) := by
  induction bs generalizing m a with
  | nil => exact mem_grows_refl m
  | cons b rest ih =>
    intro x hx
    apply ih
    show (if bv_eqb x a then some b else m x) ≠ none
    split
    · exact Option.some_ne_none b
    · exact hx

/-! ## Ranges -/

/-- The workhorse: a range every byte of which the overlay already
defines.  Stated over `wview` so the segment fallback counts too
(a store into .data needs no overlay entry). -/
theorem store_ok_of_all (segs : List Segment) (n : Nat) (m : word → Option byte) (a : word)
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hall : ∀ x : word,
      bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (n : Int) →
      wview segs m x ≠ none) :
    store_ok segs m a n = true := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have ha := hall a ⟨Int.le_refl _, by omega⟩
    cases hv : wview segs m a with
    | none => exact absurd hv ha
    | some b =>
      -- The successor address is only ever needed when bytes remain: on the
      -- LAST byte `a + 1` may wrap (a one-byte store at the top of the
      -- address space is legal), and the recursion stops before using it.
      cases n with
      | zero => simp only [store_ok, hv]
      | succ n' =>
        have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
        show (match wview segs m a with
          | some _ => store_ok segs m (a + 1) (n' + 1)
          | none => false) = true
        rw [hv]
        exact ih (a + 1) (by omega) (fun x hx => hall x (by omega))

/-! ## The stack window

`PropExec.wrap_mem` is the proof-side mirror of the initial overlay: the
argv/envp/auxv block, then `some 0` everywhere in `[sp - stack_max_size, sp)`.
A store wholly inside that window is therefore always in bounds -- which is
the point of the window, and the reason `store_ok`, the bound every machine
store carries (the comment at Rocq's `RiscvSemantics.store_ok` says why an
unbounded store made `strong_universal` falsifiable), does not need `sp`
threaded into `step`. -/

theorem wrap_mem_window_defined (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (x : word) (uid hw : word) (rnd : EntryDraw)
    (hlo : bv_unsigned sp - stack_max_size ≤ bv_unsigned x)
    (hhi : bv_unsigned x < bv_unsigned sp) :
    wrap_mem ph sp argv envp uid hw rnd x ≠ none := by
  simp only [wrap_mem]
  split
  · exact Option.some_ne_none _
  · simp only [hlo, hhi, decide_true, Bool.and_self, ↓reduceIte]
    exact Option.some_ne_none _

theorem store_ok_wrap_window (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (a : word) (n : Nat) (uid hw : word) (rnd : EntryDraw)
    (hlo : bv_unsigned sp - stack_max_size ≤ bv_unsigned a)
    (hhi : bv_unsigned a + (n : Int) ≤ bv_unsigned sp) :
    store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a n = true := by
  have hsp := u64_range sp
  apply store_ok_of_all segs n _ a (by omega)
  intro x hx
  unfold wview
  cases hwm : wrap_mem ph sp argv envp uid hw rnd x with
  | some b => exact Option.some_ne_none b
  | none =>
    exact absurd hwm (wrap_mem_window_defined ph sp argv envp x uid hw rnd (by omega) (by omega))

/-! ## Writable segments

A per-byte writable-segment condition is awkward for a SYMBOLIC target
such as `buf + i`: `find_segment` cannot be computed on an open address.
`StreamSim.wseg_ok` decides exactly that per-byte condition on a CONCRETE
range, so an image proves its writable window good once by evaluation and
every store site inside it becomes two `omega`s.  Nothing here mentions
the overlay: the segment fallback is what carries the window, so the fact
holds for every memory the proof ever reaches. -/

theorem store_ok_wseg (segs : List Segment) (m : word → Option byte) (a : word) (n : Nat)
    (h : wseg_ok segs a n = true) : store_ok segs m a n = true := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [wseg_ok] at h
    cases hseg : find_segment segs (bv_unsigned a) 1 with
    | none =>
      simp only [hseg] at h
      cases h
    | some seg =>
      simp only [hseg, Bool.and_eq_true] at h
      obtain ⟨⟨hwr, hbyte⟩, hrec⟩ := h
      cases hb : segment_byte_at seg.seg_bytes (Int.toNat (bv_unsigned a - (seg.seg_base : Int))) with
      | none =>
        simp only [hb] at hbyte
        cases hbyte
      | some b =>
        cases hm : m a with
        | some b0 =>
          simp only [store_ok, wview, hm]
          exact ih (a + 1) hrec
        | none =>
          simp only [store_ok, wview, hm, hseg, hwr, ↓reduceIte, hb]
          exact ih (a + 1) hrec

/-- The converse of `store_ok_of_all`: a good range is good byte by
byte.  Only used to cut a window down to one of its sub-ranges
(`store_ok_sub`), which is what a store site actually needs. -/
theorem store_ok_all (segs : List Segment) (m : word → Option byte) (n : Nat) (a : word)
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64) (h : store_ok segs m a n = true) :
    ∀ x : word,
      bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (n : Int) →
      wview segs m x ≠ none := by
  induction n generalizing a with
  | zero => intro x hx; omega
  | succ n ih =>
    intro x hx
    cases hv : wview segs m a with
    | none =>
      simp only [store_ok, hv] at h
      cases h
    | some b =>
      by_cases heq : bv_unsigned x = bv_unsigned a
      · rw [bv_eq_of_unsigned x a heq, hv]
        exact Option.some_ne_none b
      · -- `x` is past `a`, so at least one byte remains and `a + 1` cannot
        -- wrap — the only address at which it could is the last one.
        have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
        simp only [store_ok, hv] at h
        exact ih (a + 1) (by omega) h x (by omega)

theorem store_ok_sub (segs : List Segment) (m : word → Option byte) (lo a : word) (N n : Nat)
    (hnw : bv_unsigned lo + (N : Int) ≤ 2 ^ 64)
    (hok : store_ok segs m lo N = true)
    (hl : bv_unsigned lo ≤ bv_unsigned a)
    (hh : bv_unsigned a + (n : Int) ≤ bv_unsigned lo + (N : Int)) :
    store_ok segs m a n = true := by
  apply store_ok_of_all segs n m a (by omega)
  intro x hx
  exact store_ok_all segs m N lo hnw hok x (by omega)

/-- The per-image workhorse.  `base`/`hi` are the window's bounds as `Int`
numerals, tied to the `word` base and the `Nat` length by two equations,
the shape Rocq chose because `lia` cannot see through `Z.of_nat` of a
large decimal literal: two evaluated equations for the numerals, the
evaluated window fact, and the caller's two `Int` bounds. -/
theorem store_ok_window (segs : List Segment) (m : word → Option byte) (lo a : word)
    (N n : Nat) (base hi : Int)
    (hbase : bv_unsigned lo = base)
    (htop : base + (N : Int) = hi)
    (hnw : hi ≤ 2 ^ 64)
    (hw : wseg_ok segs lo N = true)
    (hl : base ≤ bv_unsigned a)
    (hh : bv_unsigned a + (n : Int) ≤ hi) :
    store_ok segs m a n = true :=
  store_ok_sub segs m lo a N n (by omega) (store_ok_wseg segs m lo N hw) (by omega) (by omega)

/-! ## T157: overlay growth -/

open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.Footprint

theorem apply_zeros_grows (zs : List (word × word)) (m : word → Option byte) :
    mem_grows m (apply_zeros m zs) := by
  intro x hx
  cases zs with
  | nil => exact hx
  | cons z zs =>
    simp only [apply_zeros]
    split
    · exact Option.some_ne_none _
    · exact hx

theorem zmem_grows (m : word → Option byte) (b l : word) :
    mem_grows m (zmem m b l) := by
  intro x hx
  unfold zmem
  split
  · exact Option.some_ne_none _
  · exact hx

theorem write_to_mem_grows (bs : List byte) (m : word → Option byte) (a : word) :
    mem_grows m (write_to_mem m a bs) := by
  induction bs generalizing m a with
  | nil => exact mem_grows_refl m
  | cons b rest ih =>
    intro x hx
    apply ih
    show (if bv_eqb x a then some b else m x) ≠ none
    split
    · exact Option.some_ne_none b
    · exact hx

theorem apply_writes_grows (ws : List (word × List byte)) (m : word → Option byte) :
    mem_grows m (apply_writes m ws) := by
  induction ws generalizing m with
  | nil => exact mem_grows_refl m
  | cons w ws ih =>
    rcases w with ⟨a, bs⟩
    exact mem_grows_trans m (write_to_mem m a bs) _ (write_to_mem_grows bs m a) (ih _)

/-! ## T157: grants -/

theorem store_ok_zeros_hit (segs : List Segment) (m : word → Option byte)
    (zs : List (word × word)) (a : word) (n : Nat)
    (hne : zs ≠ []) (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hcov : ∀ x : word,
      bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (n : Int) →
      zeros_cover zs x = true) :
    store_ok segs (apply_zeros m zs) a n = true := by
  apply store_ok_of_all segs n _ a hnw
  intro x hx
  cases zs with
  | nil => exact False.elim (hne rfl)
  | cons z zs =>
    simp only [wview, apply_zeros, hcov x hx, ↓reduceIte]
    exact Option.some_ne_none _

theorem store_ok_zmem (segs : List Segment) (m : word → Option byte)
    (b l a : word) (n : Nat)
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hlo : bv_unsigned b ≤ bv_unsigned a)
    (hhi : bv_unsigned a + (n : Int) ≤ bv_unsigned b + bv_unsigned l) :
    store_ok segs (zmem m b l) a n = true := by
  apply store_ok_of_all segs n _ a hnw
  intro x hx
  have hl : bv_unsigned b ≤ bv_unsigned x := by omega
  have hh : bv_unsigned x < bv_unsigned b + bv_unsigned l := by omega
  simp only [wview, zmem, hl, hh, decide_true, Bool.and_self, ↓reduceIte]
  exact Option.some_ne_none _

def store_grant_ok (segs : List Segment) (m : word → Option byte) (b l : word) : Prop :=
  ∀ (a : word) (n : Nat),
    bv_unsigned b ≤ bv_unsigned a →
    bv_unsigned a + (n : Int) ≤ bv_unsigned b + bv_unsigned l →
    store_ok segs m a n = true

theorem store_grant_zmem (segs : List Segment) (m : word → Option byte) (b l : word)
    (hnw : bv_unsigned b + bv_unsigned l ≤ 2 ^ 64) :
    store_grant_ok segs (zmem m b l) b l := by
  intro a n hlo hhi
  exact store_ok_zmem segs m b l a n (by omega) hlo hhi

theorem store_grant_zmem_prefix (segs : List Segment) (m : word → Option byte)
    (b logical physical : word) (hle : bv_unsigned logical ≤ bv_unsigned physical)
    (hnw : bv_unsigned b + bv_unsigned physical ≤ 2 ^ 64) :
    store_grant_ok segs (zmem m b physical) b logical := by
  intro a n hlo hhi
  exact store_ok_zmem segs m b physical a n (by omega) hlo (by omega)

theorem store_grant_mono (segs : List Segment) (m m' : word → Option byte) (b l : word)
    (hg : mem_grows m m') (h : store_grant_ok segs m b l) :
    store_grant_ok segs m' b l := by
  intro a n hlo hhi
  exact store_ok_mono segs n m m' a hg (h a n hlo hhi)

/-! ## T157: writable segments -/

theorem store_ok_seg_writable (segs : List Segment) (m : word → Option byte)
    (a : word) (n : Nat) (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hall : ∀ x : word,
      bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (n : Int) →
      ∃ seg, find_segment segs (bv_unsigned x) 1 = some seg ∧
        seg_writable seg = true ∧
        segment_byte_at seg.seg_bytes (Int.toNat (bv_unsigned x - (seg.seg_base : Int))) ≠ none) :
    store_ok segs m a n = true := by
  apply store_ok_of_all segs n m a hnw
  intro x hx
  unfold wview
  cases hm : m x with
  | some b => exact Option.some_ne_none b
  | none =>
    rcases hall x hx with ⟨seg, hf, hw, hb⟩
    simp only [hf, hw, ↓reduceIte]
    exact hb

/-! ## T157: read buffers -/

theorem store_ok_read_aux (segs : List Segment) (m : word → Option byte)
    (n : Nat) (a : word) (h : store_ok segs m a n = true) :
    ∃ w, read_bytes_aux (wview segs m) a n = some w := by
  induction n generalizing a with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    cases hv : wview segs m a with
    | none => simp only [store_ok, hv, Bool.false_eq_true] at h
    | some b =>
      simp only [store_ok, hv] at h
      rcases ih (a + 1) h with ⟨w, hw⟩
      exact ⟨b :: w, by simp only [read_bytes_aux, hv, hw]⟩

theorem store_ok_wbuf (segs : List Segment) (ms : machine_state) (buf cnt : word)
    (h : store_ok segs ms.ms_mem buf (word_to_nat cnt) = true) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  simp only [read_bytes_map_eq]
  exact store_ok_read_aux segs ms.ms_mem (word_to_nat cnt) buf h

theorem of_nat_word_to_nat (w : word) : (word_to_nat w : Int) = bv_unsigned w := rfl

theorem store_grant_wbuf (segs : List Segment) (ms : machine_state) (b l buf cnt : word)
    (hg : store_grant_ok segs ms.ms_mem b l)
    (hlo : bv_unsigned b ≤ bv_unsigned buf)
    (hhi : bv_unsigned buf + bv_unsigned cnt ≤ bv_unsigned b + bv_unsigned l) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  apply store_ok_wbuf
  apply hg buf (word_to_nat cnt) hlo
  rw [of_nat_word_to_nat]
  exact hhi

theorem heap_rg_wbuf (segs : List Segment) (ms : machine_state)
    (b l buf cnt : word) (cur : Int) (hg : store_grant_ok segs ms.ms_mem b l)
    (hcur : cur ≤ bv_unsigned b + bv_unsigned l - bv_unsigned b)
    (hc : covers (heap_rg b cur) buf (word_to_nat cnt)) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  rcases hc with ⟨hlo, hhi⟩
  dsimp only [heap_rg] at hlo hhi
  rw [of_nat_word_to_nat] at hhi
  exact store_grant_wbuf segs ms b l buf cnt hg hlo (by omega)

theorem zmem_wbuf (segs : List Segment) (ms : machine_state) (m : word → Option byte)
    (b l buf cnt : word) (hgr : mem_grows (zmem m b l) ms.ms_mem)
    (hnw : bv_unsigned b + bv_unsigned l ≤ 2 ^ 64)
    (hlo : bv_unsigned b ≤ bv_unsigned buf)
    (hhi : bv_unsigned buf + bv_unsigned cnt ≤ bv_unsigned b + bv_unsigned l) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  apply store_grant_wbuf segs ms b l buf cnt _ hlo hhi
  exact store_grant_mono segs _ _ b l hgr (store_grant_zmem segs m b l hnw)

theorem drain_buffer_in_grant (segs : List Segment) (ms : machine_state)
    (m : word → Option byte) (b l buf cnt a : word) (bs : List byte)
    (hm : ms.ms_mem = wbytes (zmem m b l) a bs)
    (hnw : bv_unsigned b + bv_unsigned l ≤ 2 ^ 64)
    (hlo : bv_unsigned b ≤ bv_unsigned buf)
    (hhi : bv_unsigned buf + bv_unsigned cnt ≤ bv_unsigned b + bv_unsigned l) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  apply zmem_wbuf segs ms m b l buf cnt _ hnw hlo hhi
  rw [hm]
  exact wbytes_grows bs _ a

/-! ## T157: dispatch -/

macro "store_ok_peel" : tactic => `(tactic|
  repeat first
    | (apply store_ok_mono; apply wbytes_grows)
    | (apply store_ok_mono; apply write_to_mem_grows)
    | (apply store_ok_mono; apply apply_zeros_grows)
    | (apply store_ok_mono; apply apply_writes_grows))

-- Rocq's unported `u_norm` is SymBranch's `sym_u_norm` here.
-- `simp only [List.cons_ne_nil]` replaces `discriminate` on a nonempty grant list.
macro "store_ok_base" : tactic => `(tactic| first
  | (apply store_ok_wrap_window <;> (try unfold stack_max_size) <;> sym_u_norm <;> omega)
  | (apply store_ok_zeros_hit
     · simp only [List.cons_ne_nil, ne_eq, not_false_eq_true]
     · sym_u_norm; omega
     · intro x hx; sym_u_norm; omega)
  | (apply store_ok_zmem <;> sym_u_norm <;> omega))

macro "solve_store_ok" : tactic => `(tactic| (
  store_ok_peel
  first
    | store_ok_base
    | (apply store_ok_mono
       · apply zmem_grows
       · store_ok_peel; store_ok_base)))

/-- Rocq's `store_ok_db` is represented by this extensible tactic.
Register an invariant projection taking a local invariant with:
```
macro_rules
  | `(tactic| store_ok_grows) => `(tactic| (apply my_proj; assumption))
```
Use `local macro_rules` inside a section to limit a registration's scope.
Lean tries the newest alternative first and backtracks if its tactic fails.
The base rule is assumption, standing for the context hypotheses eauto tries; solve_mem_grows uses this same extension point. -/
syntax (name := store_ok_db) "store_ok_grows" : tactic

macro_rules
  | `(tactic| store_ok_grows) => `(tactic| assumption)

macro "solve_store_ok_inv" : tactic => `(tactic| first
  | solve_store_ok
  | (store_ok_peel
     apply store_ok_mono
     · store_ok_grows
     · solve_store_ok))

macro "solve_mem_grows" : tactic => `(tactic|
  repeat first
    | (solve | store_ok_grows)
    | apply mem_grows_refl
    | (focus (apply mem_grows_trans; rotate_left; apply wbytes_grows))
    | (focus (apply mem_grows_trans; rotate_left; apply zmem_grows))
    | (focus (apply mem_grows_trans; rotate_left; apply write_to_mem_grows))
    | (focus (apply mem_grows_trans; rotate_left; apply apply_zeros_grows))
    | (focus (apply mem_grows_trans; rotate_left; apply apply_writes_grows)))

/-! ## T157: deciding `wseg_ok` once per segment

These declarations are Lean-only and have no Rocq twin.
`wseg_ok_app` splits writable windows, `wseg_cover` checks first-segment
coverage, and `wseg_ok_backed` proves a writable window from coverage,
permissions, character-list backing, and bounds. The private helpers
`wseg_cover_spec`, `ascii_segment_byte_at_isSome`, and `wseg_ok_of_bytes`
provide per-byte lookup, backing availability, and writable-window induction.
The side conditions are meant to be discharged from the per-chunk theorems
that the image generator emits. -/

open LinuxProcessSemantics.Common.ImageBytes

theorem wseg_ok_app (segs : List Segment) (a : word) (m n : Nat) :
    wseg_ok segs a (m + n) =
      (wseg_ok segs a m && wseg_ok segs (a + nat_to_word m) n) := by
  induction m generalizing a with
  | zero => simp [wseg_ok, word_add_0]
  | succ m ih =>
    have ha : a + 1 + nat_to_word m = a + nat_to_word (m + 1) := by
      rw [word1_nat, nat_to_word_add_merge, Nat.add_comm 1 m]
    simp only [Nat.succ_add, wseg_ok]
    split
    · rw [ih, ha]
      simp only [Bool.and_assoc]
    · rfl

/-- Stop at the first intersection: skipping a partial intersection could
hide an earlier segment from the per-byte lookup. Empty ranges return none. -/
def wseg_cover (segs : List Segment) (lo : Int) (n : Nat) : Option Segment :=
  match segs with
  | [] => none
  | seg :: rest =>
    let base : Int := seg.seg_base
    let top : Int := base + seg.seg_size
    if lo < lo + (n : Int) ∧ base < top ∧ base < lo + (n : Int) ∧ lo < top then
      if base ≤ lo ∧ lo + (n : Int) ≤ top then some seg else none
    else wseg_cover rest lo n

private theorem wseg_cover_spec (segs : List Segment) (seg : Segment) (lo : Int) (n : Nat)
    (hcov : wseg_cover segs lo n = some seg) :
    (seg.seg_base : Int) ≤ lo ∧ lo + (n : Int) ≤ (seg.seg_base : Int) + seg.seg_size ∧
    ∀ x : Int, lo ≤ x → x < lo + (n : Int) → find_segment segs x 1 = some seg := by
  induction segs with
  | nil => simp [wseg_cover] at hcov
  | cons head rest ih =>
    simp only [wseg_cover] at hcov
    split at hcov
    · split at hcov
      · next hc =>
        cases hcov
        refine ⟨hc.1, hc.2, ?_⟩
        intro x hx hx'
        have hb : (seg.seg_base : Int) ≤ x := by omega
        have ht : x + 1 ≤ (seg.seg_base : Int) + seg.seg_size := by omega
        simp [find_segment, hb, ht]
      · cases hcov
    · next hm =>
      obtain ⟨hb, ht, hf⟩ := ih hcov
      refine ⟨hb, ht, ?_⟩
      intro x hx hx'
      have hn : ¬ ((head.seg_base : Int) ≤ x ∧
          x + 1 ≤ (head.seg_base : Int) + head.seg_size) := by omega
      simpa [find_segment, hn] using hf x hx hx'

private theorem ascii_segment_byte_at_isSome (chunks : List (List Char)) (off : Nat)
    (hhex : ∀ cs ∈ chunks, cs.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true)
    (heven : ∀ cs ∈ chunks, cs.length % 2 = 0)
    (hoff : off < (chunks.map (fun cs => cs.length / 2)).sum) :
    (ascii_segment_byte_at chunks off).isSome = true := by
  induction chunks generalizing off with
  | nil => simp at hoff
  | cons cs rest ih =>
    simp only [ascii_segment_byte_at]
    split
    · next h =>
      have he := heven cs List.mem_cons_self
      exact hex_chars_byte_at_isSome cs off (hhex cs List.mem_cons_self) (by omega)
    · next h =>
      apply ih _ (fun c hm => hhex c (List.mem_cons_of_mem cs hm))
        (fun c hm => heven c (List.mem_cons_of_mem cs hm))
      simp only [List.map_cons, List.sum_cons] at hoff
      omega

private theorem wseg_ok_of_bytes (segs : List Segment) (a : word) (n : Nat)
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hall : ∀ x : word, bv_unsigned a ≤ bv_unsigned x →
      bv_unsigned x < bv_unsigned a + (n : Int) →
      ∃ seg, find_segment segs (bv_unsigned x) 1 = some seg ∧
        seg_writable seg = true ∧
        (segment_byte_at seg.seg_bytes (Int.toNat (bv_unsigned x - seg.seg_base))).isSome = true) :
    wseg_ok segs a n = true := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    obtain ⟨seg, hf, hw, hb⟩ := hall a (by omega) (by omega)
    have hrec : wseg_ok segs (a + 1) n = true := by
      cases n with
      | zero => rfl
      | succ k =>
        have hu := u_add1 a (by omega)
        exact ih (a + 1) (by omega) (fun x hl hh => hall x (by omega) (by omega))
    cases he : segment_byte_at seg.seg_bytes (Int.toNat (bv_unsigned a - seg.seg_base)) with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb
    | some b => simp only [wseg_ok, hf, hw, he, hrec, Bool.and_self]

theorem wseg_ok_backed (segs : List Segment) (seg : Segment) (a : word) (n : Nat)
    (chunks : List (List Char))
    (hcov : wseg_cover segs (bv_unsigned a) n = some seg)
    (hw : seg_writable seg = true)
    (hbytes : seg.seg_bytes = chunks.map String.ofList)
    (hascii : ∀ cs ∈ chunks, cs.all (fun c => c.utf8Size == 1) = true)
    (hhex : ∀ cs ∈ chunks, cs.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true)
    (heven : ∀ cs ∈ chunks, cs.length % 2 = 0)
    (hlen : bv_unsigned a + (n : Int) ≤ (seg.seg_base : Int) + (((chunks.map (fun cs => cs.length / 2)).sum : Nat) : Int))
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    wseg_ok segs a n = true := by
  obtain ⟨hb, _, hf⟩ := wseg_cover_spec segs seg (bv_unsigned a) n hcov
  apply wseg_ok_of_bytes segs a n hnw
  intro x hl hh
  refine ⟨seg, hf _ hl hh, hw, ?_⟩
  rw [hbytes, segment_byte_at_ascii chunks hascii]
  apply ascii_segment_byte_at_isSome _ _ hhex heven
  omega

section T157Tests

private def fixture_rx : Segment :=
  ⟨0x10000, 16, "r-x", ["0123456789abcdef0123456789abcdef"]⟩

set_option maxRecDepth 32768

private def fixture_chunk0 : String := "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012af"

private def fixture_chunk0_chars : List Char :=
  List.replicate 4092 '0' ++ ['1', '2', 'a', 'f']

private theorem fixture_chunk0_chars_eq : fixture_chunk0 = String.ofList fixture_chunk0_chars := rfl

private theorem fixture_chunk0_ascii :
    fixture_chunk0_chars.all (fun c => c.utf8Size == 1) = true := by
  simp only [fixture_chunk0_chars, List.all_append, List.all_replicate]
  decide +kernel

private theorem fixture_chunk0_hex :
    fixture_chunk0_chars.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true := by
  simp only [fixture_chunk0_chars, List.all_append, List.all_replicate]
  decide +kernel

private theorem fixture_chunk0_size : fixture_chunk0.utf8ByteSize = 4096 := by
  rw [fixture_chunk0_chars_eq, utf8ByteSize_ofList_ascii _ fixture_chunk0_ascii]
  simp only [fixture_chunk0_chars, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]

private def fixture_chunk1 : String := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa9b0"

private def fixture_chunk1_chars : List Char :=
  List.replicate 4092 'f' ++ ['a', '9', 'b', '0']

private theorem fixture_chunk1_chars_eq : fixture_chunk1 = String.ofList fixture_chunk1_chars := rfl

private theorem fixture_chunk1_ascii :
    fixture_chunk1_chars.all (fun c => c.utf8Size == 1) = true := by
  simp only [fixture_chunk1_chars, List.all_append, List.all_replicate]
  decide +kernel

private theorem fixture_chunk1_hex :
    fixture_chunk1_chars.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true := by
  simp only [fixture_chunk1_chars, List.all_append, List.all_replicate]
  decide +kernel

private theorem fixture_chunk1_size : fixture_chunk1.utf8ByteSize = 4096 := by
  rw [fixture_chunk1_chars_eq, utf8ByteSize_ofList_ascii _ fixture_chunk1_ascii]
  simp only [fixture_chunk1_chars, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]

private def fixture_rw : Segment :=
  ⟨0x13000, 4096, "rw-", [fixture_chunk0, fixture_chunk1]⟩

private def fixture : List Segment := [fixture_rx, fixture_rw]

example : wseg_ok fixture (Z_to_bv 64 0x13000) 4096 = true := by
  apply wseg_ok_backed fixture fixture_rw _ _ [fixture_chunk0_chars, fixture_chunk1_chars]
  · rfl
  · decide +kernel
  · change [fixture_chunk0, fixture_chunk1] = _
    rw [fixture_chunk0_chars_eq, fixture_chunk1_chars_eq]
    rfl
  · intro cs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact fixture_chunk0_ascii
    · exact fixture_chunk1_ascii
  · intro cs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact fixture_chunk0_hex
    · exact fixture_chunk1_hex
  · intro cs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;>
      simp only [fixture_chunk0_chars, fixture_chunk1_chars, List.length_append,
        List.length_replicate, List.length_cons, List.length_nil] <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fixture_chunk0_chars, fixture_chunk1_chars, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    decide +kernel
  · decide +kernel

example : wseg_ok [{ fixture_rx with seg_perms := "rw-" }]
    (Z_to_bv 64 0x10000) (2 + 2) = true := by
  rw [wseg_ok_app]
  decide +kernel

example : wseg_cover fixture (0x13000 + 4090) 16 = none := by
  -- This is the coverage premise required by `wseg_ok_backed`.
  fail_if_success
    have h : wseg_cover fixture (0x13000 + 4090) 16 = some fixture_rw := by rfl
  rfl

example : seg_writable fixture_rx = false := by
  fail_if_success
    have h : seg_writable fixture_rx = true := by decide
  decide

example : wseg_ok fixture (Z_to_bv 64 0x10000) 4 = false := by
  fail_if_success
    have h : wseg_ok fixture (Z_to_bv 64 0x10000) 4 = true := by decide +kernel
  decide +kernel

end T157Tests

/-! ## T157: tactic tests -/

section T157TacticTests

-- Peeling preserves the original store goal, including its address and length.
example (segs : List Segment) (m : word → Option byte) (a dst b l : word)
    (bs : List byte) (zs : List (word × word)) (ws : List (word × List byte))
    (n : Nat) (h : store_ok segs (zmem m b l) dst n = true) :
    store_ok segs
      (apply_writes (apply_zeros (write_to_mem (wbytes (zmem m b l) a bs) a bs) zs) ws)
      dst n = true := by
  store_ok_peel
  guard_target =ₛ store_ok segs (zmem m b l) dst n = true
  exact h

-- Like Rocq's repeat, peel may succeed without closing or changing a goal.
example (segs : List Segment) (m : word → Option byte) (b l a : word) (n : Nat)
    (h : store_ok segs (zmem m b l) a n = true) :
    store_ok segs (zmem m b l) a n = true := by
  fail_if_success solve | store_ok_peel
  store_ok_peel
  guard_target =ₛ store_ok segs (zmem m b l) a n = true
  exact h

example (segs : List Segment) (m : word → Option byte) (b l a : word) (n : Nat)
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hlo : bv_unsigned b ≤ bv_unsigned a)
    (hhi : bv_unsigned a + (n : Int) ≤ bv_unsigned b + bv_unsigned l) :
    store_ok segs (zmem m b l) a n = true := by
  store_ok_base

example : store_ok [] (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8))
    (Z_to_bv 64 7) 1 = false := by
  fail_if_success (have : store_ok [] (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8)) (Z_to_bv 64 7) 1 = true := by store_ok_base)
  rfl

-- The zero-list branch proves its nonempty premise without consuming context.
example (segs : List Segment) (m : word → Option byte) (b l : word) :
    store_ok segs (apply_zeros m [(b, l)]) (Z_to_bv 64 0) 0 = true := by
  store_ok_base

example (segs : List Segment) (m : word → Option byte) (a : word) :
    store_ok segs (apply_zeros m []) a 0 = true := by
  fail_if_success store_ok_base
  rfl

-- Stack bounds still normalize unsigned word expressions.
example (segs : List Segment) (ph : PhdrInfo) (sp uid hw : word)
    (argv envp : List (List byte)) (rnd : EntryDraw)
    (hlo : 16 ≤ bv_unsigned sp) :
    store_ok segs (wrap_mem ph sp argv envp uid hw rnd)
      (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = true := by
  have hsp := u64_range sp
  store_ok_base

example (segs : List Segment) (m : word → Option byte) (b l a dst : word)
    (bs : List byte) (n : Nat)
    (hnw : bv_unsigned dst + (n : Int) ≤ 2 ^ 64)
    (hlo : bv_unsigned b ≤ bv_unsigned dst)
    (hhi : bv_unsigned dst + (n : Int) ≤ bv_unsigned b + bv_unsigned l) :
    store_ok segs (wbytes (zmem m b l) a bs) dst n = true := by
  solve_store_ok

example : store_ok [] (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8))
    (Z_to_bv 64 16) 1 = false := by
  fail_if_success (have : store_ok [] (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8)) (Z_to_bv 64 16) 1 = true := by solve_store_ok)
  rfl

-- An address below the stack window cannot satisfy the stack dispatcher.
example (_segs : List Segment) (_ph : PhdrInfo) (sp _uid _hw : word)
    (_argv _envp : List (List byte)) (_rnd : EntryDraw)
    (_hlo : stack_max_size + 1 ≤ bv_unsigned sp) : True := by
  have hsp := u64_range sp
  fail_if_success (have : store_ok _segs (wrap_mem _ph sp _argv _envp _uid _hw _rnd) (Z_to_bv 64 (bv_unsigned sp - stack_max_size - 1)) 1 = true := by solve_store_ok)
  trivial

-- A grant outside the stack is stripped only by the fallback branch.
example (segs : List Segment) (ph : PhdrInfo) (sp uid hw b l a : word)
    (argv envp : List (List byte)) (rnd : EntryDraw) (bs : List byte)
    (hlo : 16 ≤ bv_unsigned sp) :
    store_ok segs (zmem (wbytes (wrap_mem ph sp argv envp uid hw rnd) a bs) b l)
      (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = true := by
  have hsp := u64_range sp
  solve_store_ok

-- The empty database cannot manufacture even a reflexive growth fact.
example (m : word → Option byte) : mem_grows m m := by
  fail_if_success store_ok_grows
  exact mem_grows_refl m

section ProjectionRegistration

private def growthInvariant (base mem : word → Option byte) : Prop :=
  True ∧ mem_grows base mem

private theorem growthProjection (base mem : word → Option byte)
    (h : growthInvariant base mem) : mem_grows base mem := h.2

local macro_rules
  | `(tactic| store_ok_grows) => `(tactic| (apply growthProjection; assumption))

-- A failing newer registration must backtrack to the working projection.
local macro_rules
  | `(tactic| store_ok_grows) => `(tactic| fail "test registration does not match")

example (base mem : word → Option byte) (h : growthInvariant base mem) :
    mem_grows base mem := by
  store_ok_grows

example (m : word → Option byte) : mem_grows m m := by
  fail_if_success store_ok_grows
  exact mem_grows_refl m

example (segs : List Segment) (m mem : word → Option byte) (b l a dst : word)
    (bs : List byte) (n : Nat) (h : growthInvariant (zmem m b l) mem)
    (hnw : bv_unsigned dst + (n : Int) ≤ 2 ^ 64)
    (hlo : bv_unsigned b ≤ bv_unsigned dst)
    (hhi : bv_unsigned dst + (n : Int) ≤ bv_unsigned b + bv_unsigned l) :
    store_ok segs (wbytes mem a bs) dst n = true := by
  solve_store_ok_inv

example (base mem : word → Option byte) (a b l : word) (bs : List byte)
    (zs : List (word × word)) (ws : List (word × List byte))
    (h : growthInvariant base mem) :
    mem_grows base (apply_writes (apply_zeros
      (write_to_mem (zmem (wbytes mem a bs) b l) a bs) zs) ws) := by
  solve_mem_grows

end ProjectionRegistration

-- Test registrations are local: importing this module leaves the base rule.
example (base mem : word → Option byte) (h : growthInvariant base mem) :
    mem_grows base mem := by
  fail_if_success store_ok_grows
  exact growthProjection base mem h

example : store_ok [] (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8))
    (Z_to_bv 64 16) 1 = false := by
  fail_if_success (have : store_ok [] (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8)) (Z_to_bv 64 16) 1 = true := by solve_store_ok_inv)
  rfl

example (m : word → Option byte) (a b l : word) (bs : List byte) :
    mem_grows m (wbytes (zmem m b l) a bs) := by
  solve_mem_grows

example : ¬ mem_grows (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8))
    (fun _ => none) := by
  fail_if_success (have : mem_grows (zmem (fun _ => none) (Z_to_bv 64 8) (Z_to_bv 64 8)) (fun _ => none) := by solve_mem_grows)
  intro h
  exact h (Z_to_bv 64 8) (by decide) rfl

-- Context hypotheses close growth goals directly and after peeling writes.
example (m m' : word → Option byte) (h : mem_grows m m') : mem_grows m m' := by
  store_ok_grows

example (m m' : word → Option byte) (a : word) (bs : List byte)
    (h : mem_grows m m') : mem_grows m (wbytes m' a bs) := by
  solve_mem_grows

example (store_ok_peel store_ok_base solve_store_ok store_ok_grows
    solve_store_ok_inv solve_mem_grows : Nat)
    (h : store_ok_peel + store_ok_base + solve_store_ok + store_ok_grows +
      solve_store_ok_inv + solve_mem_grows = 0) : store_ok_peel = 0 := by
  omega

end T157TacticTests

/-! ## Lean-only pins of Footprint's docstrings -/

section FootprintDocstringPins

open LinuxProcessSemantics.Common.Footprint

-- Pins clause (b)'s ordering premise for CatExec, with clause (a)
-- supplying the no-wrap bounds separately from covers_disj.
theorem covers_disj_wbytes (r1 r2 : region) (segs : List Segment)
    (bs : List byte) (m : word → Option byte) (addr a : word) (n : Nat)
    (hw1 : rg_wf r1) (hw2 : rg_wf r2) (hd : rg_disj r1 r2)
    (h1 : covers r1 addr bs.length) (h2 : covers r2 a n) :
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  rcases covers_disj r1 r2 addr bs.length a n hd h1 h2 with h | h
  · exact rdn_wbytes_disjoint segs bs m addr a n h (covers_nowrap r2 a n hw2 h2)
  · exact rdn_wbytes_below segs bs m addr a n h (covers_nowrap r1 addr bs.length hw1 h1)

-- Pins clause (b)'s absence of rg_wf: integer ordering admits this
-- wrapping region even though it does not give address-space disjointness.
set_option maxRecDepth 4096 in
theorem covers_disj_wrapping_region :
    bv_unsigned (2 ^ 64 - 1 : word) + (2 : Int) ≤ bv_unsigned (0 : word) ∨
    bv_unsigned (0 : word) + (1 : Int) ≤ bv_unsigned (2 ^ 64 - 1 : word) :=
  covers_disj (Rg (2 ^ 64 - 1) (2 ^ 64 + 1)) (Rg 0 1)
    (2 ^ 64 - 1) 2 0 1
    (by unfold rg_disj; decide) (by unfold covers; decide) (by unfold covers; decide)

-- Pins clause (b)'s distinction between integer ordering and address-space
-- disjointness: covers_disj_wrapping_region's region fails rg_wf, and its write reaches address zero.
set_option maxRecDepth 4096 in
theorem covers_disj_wrapping_readback :
    ¬ rg_wf (Rg (2 ^ 64 - 1) (2 ^ 64 + 1)) ∧
    rdn [] (wbytes (fun _ => none) (2 ^ 64 - 1) [1, 2]) 0 1 = some [2] ∧
    rdn [] (fun _ => none) 0 1 = none := by
  unfold rg_wf
  decide

-- Pins clause (c) at the statement level: the result has the supplied
-- ordering's type. Proof irrelevance makes this insensitive to proof-body use
-- of coverage, so this equality does not inspect how the proof was obtained.
theorem covers_same_disj_returns_order (r : region) (a1 : word) (n1 : Nat)
    (a2 : word) (n2 : Nat) (h1 : covers r a1 n1) (h2 : covers r a2 n2)
    (h : bv_unsigned a1 + (n1 : Int) ≤ bv_unsigned a2 ∨
      bv_unsigned a2 + (n2 : Int) ≤ bv_unsigned a1) :
    covers_same_disj r a1 n1 a2 n2 h1 h2 h = h := rfl

end FootprintDocstringPins

end LinuxProcessSemantics.Common.StoreOk
