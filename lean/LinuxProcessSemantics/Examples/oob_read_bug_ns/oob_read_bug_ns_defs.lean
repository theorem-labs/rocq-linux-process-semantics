import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.AllocSim
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.NumPrint
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.MuslStrlen
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_code

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/oob_read_bug_ns/oob_read_bug_ns_defs.v` at the
baseline above; see that Rocq file for the argument (the outcome sets, the
byte sum `sumb` feeding `udec`, and the machine-level SWAR zero test).
Rocq `Z` becomes `Int`, `nat` becomes `Nat`, `nth j s d` becomes
`List.getD s j d`, `nth_error` becomes `s[i]?`, `firstn` becomes `List.take`
and `Forall P s` becomes `∀ b ∈ s, P b`.  The closed-equation tactic `bveq`
is replaced by `decide` and `bv_eq_of_unsigned`.

unported: region_free_above -- `Common/AllocSim.lean` carries the same statement under the same name (Rocq's copy here predates the Common one); the example reaches that one.
unported: step_sb_at -- `Common/MmapSim.lean` carries the same lemma under the same name, with the stored value `v` named as an extra argument; the example reaches that one.
-/

namespace LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.NumPrint
open LinuxProcessSemantics.Common.MuslStrlen
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_code

/-! ## The spec functions: byte sum and unsigned decimal rendering -/

/-- Sum of the bytes of a string, in unbounded `Int` over `bv_unsigned`. -/
def sumb (s : List byte) : Int :=
  s.foldr (fun b acc => bv_unsigned b + acc) 0

/-- The two output buffers of a successful run. -/
def outbufs (s : List byte) : List (List byte) :=
  [udec (sumb s), [Z_to_bv 8 10]]

/-- Both output buffers are small enough for the model to transfer in one
`write`: the decimal rendering is capped by `udec`'s own fuel (24 digits)
whatever the byte sum is, and the newline is a single byte. -/
theorem outbufs_modeled (s : List byte) : bufs_modeled (outbufs s) := by
  have hdec : (udec (sumb s)).length ≤ 24 := by
    unfold udec
    split
    · simp only [List.length_singleton]
      omega
    · exact udec_aux_len 24 (sumb s)
  have hmax : (24 : Int) ≤ rw_bytes_max := by decide
  intro b hb
  simp only [outbufs, List.mem_cons, List.not_mem_nil, or_false] at hb
  unfold buf_modeled
  rcases hb with rfl | rfl
  · omega
  · simp only [List.length_singleton]
    omega

/-! ### sumb lemmas -/

theorem sumb_app (a b : List byte) : sumb (a ++ b) = sumb a + sumb b := by
  induction a with
  | nil => simp only [sumb, List.nil_append, List.foldr_nil, Int.zero_add]
  | cons x a ih =>
    simp only [sumb, List.cons_append, List.foldr_cons] at ih ⊢
    omega

theorem sumb_le (s : List byte) (hf : ∀ b ∈ s, bv_unsigned b < 256) :
    sumb s ≤ 255 * (s.length : Int) := by
  induction s with
  | nil => simp only [sumb, List.foldr_nil, List.length_nil, Int.ofNat_zero, Int.mul_zero,
      Int.le_refl]
  | cons x s ih =>
    have hx := u8_range x
    have ih' := ih (fun b hb => hf b (List.mem_cons_of_mem x hb))
    simp only [sumb, List.foldr_cons, List.length_cons] at ih' ⊢
    omega

theorem firstn_snoc (s : List byte) (k : Nat) (hk : k < s.length) :
    s.take (k + 1) = s.take k ++ [s.getD k (Z_to_bv 8 0)] := by
  simpa only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some] using
    (List.take_succ_eq_append_getElem hk)

theorem sumb_firstn_S (s : List byte) (k : Nat) (hk : k < s.length) :
    sumb (s.take (k + 1)) = sumb (s.take k) + bv_unsigned (s.getD k (Z_to_bv 8 0)) := by
  rw [firstn_snoc s k hk, sumb_app]
  simp only [sumb, List.foldr_cons, List.foldr_nil, Int.add_zero]

/-- The same recurrence with a zero default, including indices in a
page-rounded padding tail past the end of the list. -/
theorem sumb_firstn_S_default (s : List byte) (k : Nat) :
    sumb (s.take (k + 1)) = sumb (s.take k) + bv_unsigned (s.getD k (Z_to_bv 8 0)) := by
  induction s generalizing k with
  | nil =>
    simp only [List.take_nil, List.getD_nil, u8_zero, Int.add_zero]
  | cons b s ih =>
    cases k with
    | zero =>
      simp only [List.take_succ_cons, List.take_zero, List.getD_cons_zero,
        sumb, List.foldr_cons, List.foldr_nil, Int.add_zero, Int.zero_add]
    | succ k =>
      have h := ih k
      simp only [List.take_succ_cons, List.getD_cons_succ,
        sumb, List.foldr_cons] at h ⊢
      omega

theorem sumb_firstn_all (s : List byte) : sumb (s.take s.length) = sumb s := by
  rw [List.take_length]

/-- The digit-char formation `addiw d 48` for a digit d. -/
theorem v_addiw_d48 (d : word) (hd : bv_unsigned d ≤ 9) :
    bv_unsigned (v_addiw d 48) = 48 + bv_unsigned d := by
  have := u64_range d
  rw [v_addiw_small d 48 (by omega) (by omega) (by decide)]
  omega

/-! ## The shared outcome sets and the resolution-set algebra -/

/-- The outcome set, parameterized by the grow amount `n` (= strlen):
the silent exit-4 outcome exists exactly when the second brk is a
GENUINE grow (`n ≠ 0`) that the kernel may refuse.  For `n = 0` the
second brk re-requests the current break, which never fails (the
same on Linux: newbrk = oldbrk short-circuits to success), so the
run is deterministic. -/
def oobU (n : word) (bufs : List (List byte)) : (List (List byte) × word) → Prop :=
  fun o => (n ≠ Z_to_bv 64 0 ∧ o = ([], Z_to_bv 64 4)) ∨ o = (bufs, Z_to_bv 64 0)

/-- The first brk node: brk(0) is DETERMINISTIC, it reports the
quantified ASLR base `b`, so the resolution set is the singleton
{b} and the outcome set is `T1` AT `b`.  Works for `n = 0` too:
`growable` then excludes the exit-4 element on both sides. -/
theorem oobU_iff_T1 (reserved : List (word × word)) (lim top : Int) (n : word)
    (bufs : List (List byte)) (b : word) (P : word → Prop)
    (HP : ∀ r, P r ↔ r = b) (Hg : growable reserved lim top n b) :
    ∀ o, oobU n bufs o ↔ (∃ r, P r ∧ T1 reserved lim top n bufs r o) := by
  intro o
  constructor
  · intro ho
    refine ⟨b, (HP b).mpr rfl, ?_⟩
    rcases ho with ⟨hn, ho⟩ | ho
    · exact Or.inl ⟨ho, Or.inr (Or.inr hn)⟩
    · exact Or.inr ⟨Hg, ho⟩
  · rintro ⟨r, hr, ho⟩
    have hrb : r = b := (HP r).mp hr
    subst r
    rcases ho with ⟨ho, hz | hw | hn⟩ | ⟨_, ho⟩
    · exact (Hg.1 hz).elim
    · exact (Int.not_le_of_gt Hg.2.1 hw).elim
    · exact Or.inl ⟨hn, ho⟩
    · exact Or.inr ho

/-! ## argv helpers -/

theorem nth_bound (s : List byte) (j : Nat) (_hf : ∀ b ∈ s, bv_unsigned b < 256)
    (_hj : j < s.length) : bv_unsigned (s.getD j (Z_to_bv 8 0)) < 256 :=
  (u8_range _).2

/-! ## Value-shape facts -/

theorem v_mul_small (x y : word) (Hxy : bv_unsigned x * bv_unsigned y < 2 ^ 64) :
    bv_unsigned (v_mul x y) = bv_unsigned x * bv_unsigned y := by
  unfold v_mul
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  exact Int.emod_eq_of_lt (Int.mul_nonneg (u64_range x).1 (u64_range y).1) Hxy

/-! ## wbytes pointwise theory: in-range lookup and disjoint commutation -/

theorem wbytes_get (bs : List byte) (m : word → Option byte) (a x : word)
    (Hnw : bv_unsigned a + (bs.length : Int) < 2 ^ 64)
    (Hax : bv_unsigned a ≤ bv_unsigned x)
    (Hlen : (bv_unsigned x - bv_unsigned a).toNat < bs.length) :
    wbytes m a bs x = bs[(bv_unsigned x - bv_unsigned a).toNat]? := by
  induction bs generalizing m a with
  | nil => simp only [List.length_nil] at Hlen; omega
  | cons b bs ih =>
    simp only [List.length_cons] at Hnw Hlen
    have ha1 : bv_unsigned (a + 1) = bv_unsigned a + 1 :=
      u_add1 a (by omega)
    by_cases hxa : x = a
    · subst x
      rw [wbytes, wbytes_below bs _ (a + 1) a (by omega) (by omega)]
      simp only [(bv_eqb_eq a a).2 rfl, ↓reduceIte, Int.sub_self,
        Int.toNat_zero, List.getElem?_cons_zero]
    · have hlt : bv_unsigned a < bv_unsigned x := by
        have hne : bv_unsigned x ≠ bv_unsigned a := by
          intro h
          exact hxa (bv_eq_of_unsigned x a h)
        omega
      have hidx : (bv_unsigned x - bv_unsigned a).toNat =
          (bv_unsigned x - bv_unsigned (a + 1)).toNat + 1 := by omega
      rw [wbytes, hidx, List.getElem?_cons_succ]
      exact ih _ (a + 1) (by omega) (by omega) (by omega)

/-- Two disjoint `wbytes` overlays commute (first block entirely below
the second, both within `2^64`). -/
theorem wbytes_disjoint_comm (bs1 bs2 : List byte) (m : word → Option byte) (a1 a2 : word)
    (Hd : bv_unsigned a1 + (bs1.length : Int) ≤ bv_unsigned a2)
    (Hnw2 : bv_unsigned a2 + (bs2.length : Int) < 2 ^ 64) :
    wbytes (wbytes m a1 bs1) a2 bs2 = wbytes (wbytes m a2 bs2) a1 bs1 := by
  have pointwise (bs : List byte) (p q : word → Option byte) (a x : word)
      (h : p x = q x) : wbytes p a bs x = wbytes q a bs x := by
    induction bs generalizing p q a with
    | nil => exact h
    | cons b rest ih =>
      simp only [wbytes]
      apply ih
      split
      · rfl
      · exact h
  funext x
  by_cases hx : bv_unsigned x < bv_unsigned a2
  · rw [wbytes_below bs2 (wbytes m a1 bs1) a2 x (by omega) hx]
    exact pointwise bs1 m (wbytes m a2 bs2) a1 x
      (wbytes_below bs2 m a2 x (by omega) hx).symm
  · have habove : bv_unsigned a1 + (bs1.length : Int) ≤ bv_unsigned x := by
      omega
    rw [wbytes_above bs1 (wbytes m a2 bs2) a1 x habove]
    exact pointwise bs2 (wbytes m a1 bs1) m a2 x
      (wbytes_above bs1 m a1 x habove)

/-! ## Byte-sum positivity for a nonempty NUL-free string -/

theorem sumb_pos (s : List byte) (Hne : s ≠ []) (Hnz : Z_to_bv 8 0 ∉ s) : 1 ≤ sumb s := by
  have nonneg (t : List byte) : 0 ≤ sumb t := by
    induction t with
    | nil => exact Int.le_refl 0
    | cons b t ih =>
      have hb := (u8_range b).1
      simp only [sumb, List.foldr_cons] at ih ⊢
      omega
  cases s with
  | nil => exact False.elim (Hne rfl)
  | cons b t =>
    have hbne : bv_unsigned b ≠ 0 := by
      intro hb
      have heq : b = Z_to_bv 8 0 :=
        bv_eq_of_unsigned b (Z_to_bv 8 0) (hb.trans u8_zero.symm)
      exact Hnz (List.mem_cons.mpr (Or.inl heq.symm))
    have hb := (u8_range b).1
    have ht := nonneg t
    simp only [sumb, List.foldr_cons] at ht ⊢
    omega

/-- The decimal rendering of a value below 2^64 fits in the 24-byte
stack buffer with at least 4 slots to spare. -/
theorem udec_len_24 (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 64) : (udec v).length ≤ 20 :=
  udec_len_le v h0 h1

/-! ## The machine-level SWAR zero test -/

/-- The two magic constants musl's `strlen` materialises before its
word-at-a-time loop: `-0x0101010101010101` and `0x8080808080808080`. -/
def swar_K : word := Z_to_bv 64 0xFEFEFEFEFEFEFEFF
def swar_M : word := Z_to_bv 64 0x8080808080808080

/-- The value musl's loop tests against zero: `(x + K) & ~x & M`. -/
def swar_res (x : word) : word :=
  v_and (v_and (v_add x swar_K) (v_xori x (-1))) swar_M

/-- `swar_res` IS the `HZ.Tz` test of Common/MuslStrlen: the constants
match `v_haszero`'s literals digit for digit. -/
theorem swar_res_Tz (x : word) : bv_unsigned (swar_res x) = HZ.Tz (bv_unsigned x) := by
  unfold swar_res swar_K swar_M
  exact v_haszero x

/-- First zero byte of a list: its index, and everything below it
nonzero (what `HZ.Tz_haszero`'s borrow side condition wants). -/
theorem in_first_zero (bs : List byte) (Hin : Z_to_bv 8 0 ∈ bs) :
    ∃ i, i < bs.length ∧ bs.getD i (Z_to_bv 8 0) = Z_to_bv 8 0 ∧
      ∀ j, j < i → bs.getD j (Z_to_bv 8 0) ≠ Z_to_bv 8 0 := by
  induction bs with
  | nil => simp only [List.not_mem_nil] at Hin
  | cons b bs ih =>
    by_cases hb : b = Z_to_bv 8 0
    · refine ⟨0, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · simpa only [List.getD_cons_zero] using hb
      · intro j hj
        omega
    · have htail : Z_to_bv 8 0 ∈ bs := by
        rcases List.mem_cons.mp Hin with h | h
        · exact False.elim (hb h.symm)
        · exact h
      obtain ⟨i, hi, hz, hfirst⟩ := ih htail
      refine ⟨i + 1, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · simpa only [List.getD_cons_succ] using hz
      · intro j hj
        cases j with
        | zero => simpa only [List.getD_cons_zero] using hb
        | succ j =>
          simp only [List.getD_cons_succ]
          exact hfirst j (by omega)

/-- The two directions of the test at the machine level, via
`HZ.Tz_nozero` / `HZ.Tz_haszero`. -/
theorem swar_res_zero (bs : List byte) (x : word) (Hlen : bs.length = 8)
    (Hx : bv_unsigned x = bytes_le_to_Z bs) (Hnz : Z_to_bv 8 0 ∉ bs) :
    swar_res x = Z_to_bv 64 0 := by
  apply bv_eq_of_unsigned
  rw [swar_res_Tz, Hx]
  have hnz : ∀ i : Nat, i < 8 → HZ.zb (bytes_le_to_Z bs) i ≠ 0 := by
    intro i hi hz
    have hilt : i < bs.length := by omega
    rw [zb_of_bytes bs i hilt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hilt, Option.getD_some] at hz
    have hb : bs[i] = Z_to_bv 8 0 :=
      bv_eq_of_unsigned _ _ (hz.trans u8_zero.symm)
    exact Hnz (hb ▸ List.getElem_mem hilt)
  rw [HZ.Tz_nozero (bytes_le_to_Z bs) (bytes_le_to_Z_range bs Hlen) hnz]
  rfl

theorem swar_res_nonzero (bs : List byte) (x : word) (Hlen : bs.length = 8)
    (Hx : bv_unsigned x = bytes_le_to_Z bs) (Hin : Z_to_bv 8 0 ∈ bs) :
    swar_res x ≠ Z_to_bv 64 0 := by
  obtain ⟨i, hi, hz, hlow⟩ := in_first_zero bs Hin
  have htest : HZ.Tz (bytes_le_to_Z bs) ≠ 0 := by
    apply HZ.Tz_haszero _ i (bytes_le_to_Z_range bs Hlen) (by omega)
    · rw [zb_of_bytes bs i hi, hz, u8_zero]
    · intro j hj hzero
      rw [zb_of_bytes bs j (by omega)] at hzero
      apply hlow j hj
      apply bv_eq_of_unsigned
      simpa only [u8_zero] using hzero
  intro heq
  apply htest
  rw [← Hx, ← swar_res_Tz, heq]
  decide

/-! ## Local helpers from the Rocq target file

`v_addi_natS_m1` and `sumb_nonneg` are the Rocq target file's own helpers;
`c_ltu_x0` stands in for Rocq's `bveq` on a branch condition the target run
meets (`c_eq_refl` and `c_eq_neq`, which do the same for the equality
branches, come from `Common/PropExec.lean`).

Nothing in this file redeclares a name `Common/` carries: #1526 landed
with copies of library lemmas and was reverted by #1543 when the library
PRs made them ambiguous.  A helper that `Common/` lacks is spelled with
the example's own name so it can never collide. -/

theorem v_addi_natS_m1 (k : Nat) : v_addi (nat_to_word (k + 1)) (-1) = nat_to_word k := by
  unfold nat_to_word v_addi
  apply bv_eq_of_unsigned
  simp only [Z_to_bv_unsigned, bv_wrap64_mod, Int.emod_add_emod]
  congr 1
  omega

theorem sumb_nonneg (s : List byte) : 0 ≤ sumb s := by
  induction s with
  | nil => exact Int.le_refl 0
  | cons b s ih =>
    unfold sumb at *
    simp only [List.foldr_cons]
    have := (u8_range b).1
    omega

theorem c_ltu_x0 (x : word) : c_ltu x (Z_to_bv 64 0) = false := by
  change decide (x.toNat < 0) = false
  simp only [Nat.not_lt_zero, decide_false]

/-! ## Model facts the outcome layer needs

Rocq reaches this through `Common/AllocSim.v`; the Lean `Common` has no
twin yet, so it is stated here over `init_model` itself
(`init_model_fd1chan`, its companion, is `Common/CatSim.lean`'s). -/

theorem m_vmmaps_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_vmmaps (init_model reserved brk0 mbase sp lim inp) =
      VmMaps.mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp := rfl

end LinuxProcessSemantics.Examples.oob_read_bug_ns.oob_read_bug_ns_defs
