import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.Hoare — a Hoare/WP-style program logic over `msteps`

Ported from `theories/Common/Hoare.v` at the baseline above, with the Rocq
names and statements: the `at_` address arithmetic, the assertions and
footprints, `triple` and its structural, frame, call and loop rules, and
the two hand-offs `triple_msteps` and `triple_wexit`.  What the triple
means and why it carries footprints is the Rocq file's header, not
repeated here.

Spellings that differ:
- `assn`, `regset` and `memset` are `abbrev`s where Rocq has `Definition`s.
- Rocq's `Z.land` is `PropExec.Z_land`; `z mod 2` is `z % 2`, which agrees
  with Rocq's floor `mod` because the divisor is positive.
- `(0 <= i < Z.of_nat n)%Z` is `0 ≤ i ∧ i < (n : Int)`; Rocq `S i` and `O`
  are `i + 1` and `0`.
- The side goal `(1 : reg) ≠ 0` that Rocq's `triple_call` closes with
  `reg_neq_tac` is closed here by `decide`. -/

namespace LinuxProcessSemantics.Common.Hoare

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec

/-! ## Address arithmetic for address-parametric summaries -/

/-- `at_ base d` is `base + d`, the address of the instruction at byte
offset `d` of a relocatable code blob loaded at `base`. -/
def at_ (base : word) (d : Int) : word := Z_to_bv 64 (bv_unsigned base + d)

theorem at_0 (base : word) : at_ base 0 = base := v_addi_0 base

/-- The workhorse: stepping the pc by any (possibly negative) displacement
stays inside the `at_` normal form. -/
theorem at_addi (base : word) (d e : Int) : v_addi (at_ base d) e = at_ base (d + e) := by
  apply bv_eq_of_unsigned
  unfold v_addi at_
  simp only [Z_to_bv_unsigned]
  unfold bv_wrap
  rw [Int.emod_add_emod, Int.add_assoc]

theorem at_btgt (base : word) (d e : Int) : btgt (at_ base d) e = at_ base (d + e) :=
  at_addi base d e

/-- `at_` of a literal base collapses to a literal address. -/
theorem at_lit (base : word) (d : Int) (a : word) (h : Z_to_bv 64 (bv_unsigned base + d) = a) :
    at_ base d = a := h

/-- `at_` composes: an offset from an already-offset address. -/
theorem at_at (base : word) (d e : Int) : at_ (at_ base d) e = at_ base (d + e) :=
  at_addi base d e

/-- Byte-walk helper: `wbytes`/`rdn` recurse on `a + 1`. -/
theorem u_succ_shift (a : word) (i : Int) :
    Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_unsigned_add]
  have h1 : bv_unsigned (1 : word) = 1 := rfl
  rw [h1]
  unfold bv_wrap
  rw [Int.emod_add_emod, Int.add_assoc]

theorem at_self (a : word) : Z_to_bv 64 (bv_unsigned a + 0) = a := at_0 a

/-! ## Assertions and footprints -/

/-- An assertion talks about the register file, the writable memory
overlay and the read-only image, never the pc. -/
abbrev assn := bvmap 5 word → (word → Option byte) → (word → Option byte) → Prop

/-- A register footprint: the registers a fragment may clobber. -/
abbrev regset := reg → Prop
/-- A memory footprint: the memory bytes a fragment may write. -/
abbrev memset := word → Prop

def regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  ∀ r, ¬ C r → getr regs' r = getr regs r

def mem_agree (W : memset) (m m' : word → Option byte) : Prop :=
  ∀ x, ¬ W x → m' x = m x

theorem regs_agree_refl (C : regset) (regs : bvmap 5 word) : regs_agree C regs regs :=
  fun _ _ => rfl

theorem mem_agree_refl (W : memset) (m : word → Option byte) : mem_agree W m m :=
  fun _ _ => rfl

theorem regs_agree_trans (C : regset) (regs1 regs2 regs3 : bvmap 5 word)
    (h1 : regs_agree C regs1 regs2) (h2 : regs_agree C regs2 regs3) :
    regs_agree C regs1 regs3 :=
  fun r hr => (h2 r hr).trans (h1 r hr)

theorem mem_agree_trans (W : memset) (m1 m2 m3 : word → Option byte)
    (h1 : mem_agree W m1 m2) (h2 : mem_agree W m2 m3) : mem_agree W m1 m3 :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem regs_agree_mono (C C' : regset) (regs regs' : bvmap 5 word)
    (hsub : ∀ r, C r → C' r) (h : regs_agree C regs regs') : regs_agree C' regs regs' :=
  fun r hr => h r (fun hc => hr (hsub r hc))

theorem mem_agree_mono (W W' : memset) (m m' : word → Option byte)
    (hsub : ∀ x, W x → W' x) (h : mem_agree W m m') : mem_agree W' m m' :=
  fun x hx => h x (fun hw => hx (hsub x hw))

/-- A register writeback inside the clobber set keeps the agreement. -/
theorem regs_agree_upd (C : regset) (regs regs' : bvmap 5 word) (r : reg) (v : word)
    (hin : C r) (h : regs_agree C regs regs') : regs_agree C regs (regupd regs' r v) := by
  intro s hs
  rw [getr_other regs' r v s (fun heq => hs (heq ▸ hin))]
  exact h s hs

/-- A store inside the write set keeps the agreement. -/
theorem mem_agree_wbytes (W : memset) (m m' : word → Option byte) (a : word) (bs : List byte)
    (hin : ∀ i : Int, 0 ≤ i ∧ i < (bs.length : Int) → W (Z_to_bv 64 (bv_unsigned a + i)))
    (h : mem_agree W m m') : mem_agree W m (wbytes m' a bs) := by
  induction bs generalizing m' a with
  | nil => exact h
  | cons b bs ih =>
    have ha : W a := by
      have h0 := hin 0 ⟨Int.le_refl 0, by simp only [List.length_cons]; omega⟩
      rwa [at_self] at h0
    apply ih
    · intro i ⟨hi0, hi1⟩
      rw [u_succ_shift]
      exact hin (1 + i) ⟨by omega, by simp only [List.length_cons]; omega⟩
    · intro x hx
      show (if bv_eqb x a then some b else m' x) = m x
      cases heq : bv_eqb x a with
      | true =>
        have hxa : x = a := (bv_eqb_eq x a).1 heq
        exact absurd (hxa ▸ ha) hx
      | false => exact h x hx

/-! ## The triple -/

/-- `triple segs C W P a b Q`: from every `P`-state at pc `a` there is an
`msteps` run to pc `b` landing in `Q`, in a state that agrees with the start
outside `C` and `W`. -/
def triple (segs : List Segment) (C : regset) (W : memset) (P : assn) (a b : word)
    (Q : assn) : Prop :=
  ∀ (regs : bvmap 5 word) (mem rom : word → Option byte), P regs mem rom →
    ∃ (regs' : bvmap 5 word) (mem' : word → Option byte),
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      ∧ Q regs' mem' rom
      ∧ regs_agree C regs regs'
      ∧ mem_agree W mem mem'

theorem triple_intro (segs : List Segment) (C : regset) (W : memset) (P : assn) (a b : word)
    (Q : assn)
    (h : ∀ (regs : bvmap 5 word) (mem rom : word → Option byte), P regs mem rom →
      ∃ (regs' : bvmap 5 word) (mem' : word → Option byte),
        msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
        ∧ Q regs' mem' rom
        ∧ regs_agree C regs regs'
        ∧ mem_agree W mem mem') :
    triple segs C W P a b Q := h

/-! ### Structural rules -/

/-- SKIP. -/
theorem triple_skip (segs : List Segment) (C : regset) (W : memset) (P : assn) (a : word) :
    triple segs C W P a a P :=
  fun regs mem _ hp =>
    ⟨regs, mem, msteps.mst_refl _, hp, regs_agree_refl C regs, mem_agree_refl W mem⟩

/-- SEQUENCING.  The footprints add up. -/
theorem triple_seq (segs : List Segment) (C1 : regset) (W1 : memset) (C2 : regset)
    (W2 : memset) (P Q R : assn) (a b c : word)
    (h1 : triple segs C1 W1 P a b Q) (h2 : triple segs C2 W2 Q b c R) :
    triple segs (fun r => C1 r ∨ C2 r) (fun x => W1 x ∨ W2 x) P a c R := by
  intro regs mem rom hp
  obtain ⟨regs1, mem1, hst1, hq, hr1, hm1⟩ := h1 regs mem rom hp
  obtain ⟨regs2, mem2, hst2, hr, hr2, hm2⟩ := h2 regs1 mem1 rom hq
  refine ⟨regs2, mem2, msteps_trans segs _ _ _ hst1 hst2, hr, ?_, ?_⟩
  · exact regs_agree_trans _ _ _ _
      (regs_agree_mono _ _ _ _ (fun _ h => Or.inl h) hr1)
      (regs_agree_mono _ _ _ _ (fun _ h => Or.inr h) hr2)
  · exact mem_agree_trans _ _ _ _
      (mem_agree_mono _ _ _ _ (fun _ h => Or.inl h) hm1)
      (mem_agree_mono _ _ _ _ (fun _ h => Or.inr h) hm2)

/-- CONSEQUENCE, both on the assertions and (weakening) on the footprints. -/
theorem triple_conseq (segs : List Segment) (C C' : regset) (W W' : memset)
    (P P' Q Q' : assn) (a b : word)
    (h : triple segs C W P a b Q)
    (hP : ∀ regs mem rom, P' regs mem rom → P regs mem rom)
    (hQ : ∀ regs mem rom, Q regs mem rom → Q' regs mem rom)
    (hC : ∀ r, C r → C' r) (hW : ∀ x, W x → W' x) :
    triple segs C' W' P' a b Q' := by
  intro regs mem rom hp'
  obtain ⟨regs', mem', hst, hq0, hr, hm⟩ := h regs mem rom (hP regs mem rom hp')
  exact ⟨regs', mem', hst, hQ _ _ _ hq0, regs_agree_mono C C' regs regs' hC hr,
    mem_agree_mono W W' mem mem' hW hm⟩

theorem triple_seq_same (segs : List Segment) (C : regset) (W : memset) (P Q R : assn)
    (a b c : word)
    (h1 : triple segs C W P a b Q) (h2 : triple segs C W Q b c R) :
    triple segs C W P a c R := by
  intro regs mem rom hp
  obtain ⟨regs1, mem1, hst1, hq, hr1, hm1⟩ := h1 regs mem rom hp
  obtain ⟨regs2, mem2, hst2, hr, hr2, hm2⟩ := h2 regs1 mem1 rom hq
  exact ⟨regs2, mem2, msteps_trans segs _ _ _ hst1 hst2, hr,
    regs_agree_trans _ _ _ _ hr1 hr2, mem_agree_trans _ _ _ _ hm1 hm2⟩

/-! ### The frame rule -/

/-- `R` is FRAMEABLE past a fragment with footprints `(C, W)` when it is
stable under any change confined to those footprints. -/
def frameable (C : regset) (W : memset) (R : assn) : Prop :=
  ∀ regs mem rom regs' mem',
    regs_agree C regs regs' → mem_agree W mem mem' →
    R regs mem rom → R regs' mem' rom

/-- FRAME. -/
theorem triple_frame (segs : List Segment) (C : regset) (W : memset) (P Q R : assn)
    (a b : word)
    (h : triple segs C W P a b Q) (hR : frameable C W R) :
    triple segs C W (fun regs mem rom => P regs mem rom ∧ R regs mem rom) a b
                    (fun regs mem rom => Q regs mem rom ∧ R regs mem rom) := by
  rintro regs mem rom ⟨hp, hrr⟩
  obtain ⟨regs', mem', hst, hq, hr, hm⟩ := h regs mem rom hp
  exact ⟨regs', mem', hst, ⟨hq, hR regs mem rom regs' mem' hr hm hrr⟩, hr, hm⟩

theorem frameable_and (C : regset) (W : memset) (R1 R2 : assn)
    (h1 : frameable C W R1) (h2 : frameable C W R2) :
    frameable C W (fun regs mem rom => R1 regs mem rom ∧ R2 regs mem rom) := by
  rintro regs mem rom regs' mem' hr hm ⟨ha, hb⟩
  exact ⟨h1 regs mem rom regs' mem' hr hm ha, h2 regs mem rom regs' mem' hr hm hb⟩

theorem frameable_reg (C : regset) (W : memset) (r : reg) (v : word) (hnc : ¬ C r) :
    frameable C W (fun regs _ _ => getr regs r = v) :=
  fun _ _ _ _ _ hr _ hv => (hr r hnc).trans hv

/-- A byte-range read is frameable when the range misses the write set. -/
theorem frameable_rdn (segs : List Segment) (C : regset) (W : memset) (a : word) (n : Nat)
    (bs : List byte)
    (hdisj : ∀ i : Int, 0 ≤ i ∧ i < (n : Int) → ¬ W (Z_to_bv 64 (bv_unsigned a + i))) :
    frameable C W (fun _ mem _ => rdn segs mem a n = some bs) := by
  intro _ mem _ _ mem' _ hm hrd
  show rdn segs mem' a n = some bs
  have hrd' : rdn segs mem a n = some bs := hrd
  rw [← hrd']
  clear hrd hrd'
  revert a
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a hdisj
    have ha : ¬ W a := by
      have h0 := hdisj 0 ⟨Int.le_refl 0, by omega⟩
      rwa [at_self] at h0
    have hrest := ih (a + 1) (fun i ⟨hi0, hi1⟩ => by
      rw [u_succ_shift]
      exact hdisj (1 + i) ⟨by omega, by omega⟩)
    simp only [rdn, hm a ha, hrest]

/-! ### The call rule -/

/-- `ret_ok k`: `k` is a legal `ret` target. -/
def ret_ok (k : word) : Prop := v_jalr k 0 = k

theorem land_m2_even (z : Int) (hz : z % 2 = 0) : Z_land z (-2) = z := by
  rw [Z_land_m2, hz, Int.sub_zero]

/-- Pin the header's "`z mod 2` is `z % 2`, which agrees with Rocq's floor
`mod` because the divisor is positive" by deriving `land_m2_even` from
Rocq's floor-modulo premise. -/
example (z : Int) (h : Int.fmod z 2 = 0) : Z_land z (-2) = z :=
  land_m2_even z (by rwa [← Int.fmod_eq_emod_of_nonneg z (by decide)])

/-- Pin the positive-divisor limit of the header's "`z mod 2` is `z % 2`,
which agrees with Rocq's floor `mod` because the divisor is positive": at
the negative divisor `-2`, floor and Euclidean modulo differ on `3`. -/
example : Int.fmod 3 (-2) ≠ 3 % (-2) := by decide

theorem ret_ok_even (k : word) (hk : bv_unsigned k % 2 = 0) : ret_ok k := by
  unfold ret_ok v_jalr jalr_tgtZ
  rw [Int.add_zero, land_m2_even _ hk]
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, bv_wrap]
  have hk' := u64_range k
  exact Int.emod_eq_of_lt hk'.1 hk'.2

/-- A PROCEDURE summary: the address-parametric form. -/
def proc (segs : List Segment) (C : regset) (W : memset) (P : assn) (entry : word)
    (Q : assn) : Prop :=
  ∀ k : word, ret_ok k →
    triple segs C W (fun regs mem rom => P regs mem rom ∧ getr regs 1 = k) entry k Q

/-- `P` does not look at `ra`. -/
def ra_indep (P : assn) : Prop :=
  ∀ regs v mem rom, P regs mem rom → P (regupd regs 1 v) mem rom

/-- CALL. -/
theorem triple_call (segs : List Segment) (C : regset) (W : memset) (P Q : assn)
    (callsite entry ret : word)
    (hjal : ∀ regs mem rom,
      RiscvSemantics.step segs (mkst regs callsite mem rom)
        = MachineOk (mkst (regupd regs 1 ret) entry mem rom))
    (hret : ret_ok ret) (hraP : ra_indep P) (hproc : proc segs C W P entry Q) :
    triple segs (fun r => C r ∨ r = 1) W P callsite ret Q := by
  intro regs mem rom hp
  have hpre : P (regupd regs 1 ret) mem rom ∧ getr (regupd regs 1 ret) 1 = ret :=
    ⟨hraP regs ret mem rom hp, getr_same regs 1 ret (by decide)⟩
  obtain ⟨regs', mem', hst, hq, hr, hm⟩ := hproc ret hret (regupd regs 1 ret) mem rom hpre
  refine ⟨regs', mem', msteps.mst_step _ _ _ rfl (hjal regs mem rom) hst, hq, ?_, hm⟩
  intro r hr0
  have hnC : ¬ C r := fun h => hr0 (Or.inl h)
  have hne : r ≠ 1 := fun h => hr0 (Or.inr h)
  rw [hr r hnC, getr_other regs 1 ret r hne]

/-! ### The loop rule -/

/-- LOOP, in the measure-decreasing form. -/
theorem triple_loop (segs : List Segment) (C : regset) (W : memset) (I : Nat → assn)
    (hd out : word) (Q : assn)
    (hbody : ∀ i, triple segs C W (I (i + 1)) hd hd (I i))
    (hexit : triple segs C W (I 0) hd out Q) :
    ∀ n, triple segs C W (I n) hd out Q := by
  intro n
  induction n with
  | zero => exact hexit
  | succ n ih => exact triple_seq_same segs C W _ _ _ hd hd out (hbody n) ih

/-- The same, with the measure read off the state. -/
theorem triple_loop_measure (segs : List Segment) (C : regset) (W : memset) (I : Nat → assn)
    (hd out : word) (Q P : assn)
    (hbody : ∀ i, triple segs C W (I (i + 1)) hd hd (I i))
    (hexit : triple segs C W (I 0) hd out Q)
    (hmeas : ∀ regs mem rom, P regs mem rom → ∃ n, I n regs mem rom) :
    triple segs C W P hd out Q := by
  intro regs mem rom hp
  obtain ⟨n, hi⟩ := hmeas regs mem rom hp
  exact triple_loop segs C W I hd out Q hbody hexit n regs mem rom hi

/-! ### Hand-off to the behaviour-shape relations -/

/-- Forget the footprints: a triple is an `msteps` lemma. -/
theorem triple_msteps (segs : List Segment) (C : regset) (W : memset) (P : assn) (a b : word)
    (Q : assn) (regs : bvmap 5 word) (mem rom : word → Option byte)
    (h : triple segs C W P a b Q) (hp : P regs mem rom) :
    ∃ (regs' : bvmap 5 word) (mem' : word → Option byte),
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) ∧ Q regs' mem' rom := by
  obtain ⟨regs', mem', hst, hq, _, _⟩ := h regs mem rom hp
  exact ⟨regs', mem', hst, hq⟩

/-- Prepend a triple to a `to_wexit` derivation. -/
theorem triple_wexit (segs : List Segment) (C : regset) (W : memset) (P : assn) (a b : word)
    (Q : assn) (bufs : List (List byte)) (code : word) (regs : bvmap 5 word)
    (mem rom : word → Option byte)
    (h : triple segs C W P a b Q) (hp : P regs mem rom)
    (hcont : ∀ regs' mem', Q regs' mem' rom →
      to_wexit segs (mkst regs' b mem' rom) bufs code) :
    to_wexit segs (mkst regs a mem rom) bufs code := by
  obtain ⟨regs', mem', hst, hq, _, _⟩ := h regs mem rom hp
  exact msteps_to_wexit segs _ _ bufs code hst (hcont regs' mem' hq)

end LinuxProcessSemantics.Common.Hoare
