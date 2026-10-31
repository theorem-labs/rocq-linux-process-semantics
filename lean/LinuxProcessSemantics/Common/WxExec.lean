import LinuxProcessSemantics.Common.PropExec

/-! The writable-code frame argument from `theories/Common/WxExec.v`
at reference commit `7f386a77d4d3877f162c91f06b7e4fcc1d998e61`.
The static image justifies a fetch only while the overlay misses every
fetched byte. Disjoint stores preserve that premise; overlapping stores do not. -/

namespace LinuxProcessSemantics.Common.WxExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.Common.PropExec

def mem_clear (m : word → Option byte) (lo hi : Int) : Prop :=
  ∀ a, lo ≤ bv_unsigned a ∧ bv_unsigned a < hi → m a = none

theorem mem_clear_wrap (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (lo hi : Int) (uid hwcap : word) (draw : EntryDraw)
    (hhi : hi ≤ bv_unsigned sp - stack_max_size) :
    mem_clear (wrap_mem ph sp argv envp uid hwcap draw) lo hi := by
  intro a ha
  have hbelow : ¬ bv_unsigned sp ≤ bv_unsigned a := by
    unfold stack_max_size at hhi
    omega
  have hbelowZero : ¬ bv_unsigned sp - stack_max_size ≤ bv_unsigned a := by omega
  simp [wrap_mem, stack_to_mem, hbelow, hbelowZero]

theorem mem_clear_wbytes (m : word → Option byte) (addr : word) (bs : List byte)
    (lo hi : Int) (hc : mem_clear m lo hi)
    (hd : hi ≤ bv_unsigned addr ∨ bv_unsigned addr + (bs.length : Int) ≤ lo)
    (hnw : bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64) :
    mem_clear (write_to_mem m addr bs) lo hi := by
  intro a ha
  rw [write_to_mem_away]
  · exact hc a ha
  · intro i hiLen heq
    have hbound : addr.toNat + i < 2 ^ 64 := by
      unfold bv_unsigned at hnw
      omega
    have hu := u_add_offset addr i hbound
    rw [← heq] at hu
    rcases hd with habove | hbelow <;> omega

theorem find_segment_range (segs : List Segment) (a n : Int) (seg : Segment) :
    find_segment segs a n = some seg →
    (seg.seg_base : Int) ≤ a ∧ a + n ≤ (seg.seg_base : Int) + seg.seg_size := by
  induction segs with
  | nil => simp [find_segment]
  | cons s ss ih =>
    simp only [find_segment]
    split
    · rename_i hs
      intro h
      cases Option.some.inj h
      simpa using hs
    · exact ih

theorem find_segment_in (segs : List Segment) (a n : Int) (seg : Segment) :
    find_segment segs a n = some seg → seg ∈ segs := by
  induction segs with
  | nil => simp only [find_segment, reduceCtorEq, false_implies]
  | cons s ss ih =>
      simp only [find_segment]
      split
      · intro h
        cases Option.some.inj h
        exact List.mem_cons_self
      · intro h
        exact List.mem_cons_of_mem s (ih h)

def no_ro_exec (segs : List Segment) : Bool :=
  segs.all (fun s => !(seg_executable s && !(seg_writable s)))

theorem code_read_none_no_ro_exec (segs : List Segment) (a : word) (n : Nat)
    (hro : no_ro_exec segs = true) : code_read segs a n = none := by
  cases hs : find_segment segs (bv_unsigned a) n with
  | none => simp only [code_read, hs]
  | some seg =>
      have hm := find_segment_in segs (bv_unsigned a) n seg hs
      have hp := (List.all_eq_true.mp hro) seg hm
      have hn : ¬ (seg_executable seg && !(seg_writable seg)) = true := by
        intro h
        simp only [h, Bool.not_true, Bool.false_eq_true] at hp
      simp only [code_read, hs, ite_eq_right hn]

theorem fetch_word_none_no_ro_exec (segs : List Segment) (pc : word)
    (hro : no_ro_exec segs = true) : fetch_word segs pc = none := by
  unfold fetch_word
  rw [code_read_none_no_ro_exec segs pc 4 hro]
  split <;> rfl

theorem seg_ov_read_bytes_static (n : Nat) (m : word → Option byte)
    (seg : Segment) (addr : word)
    (hc : ∀ a, bv_unsigned addr ≤ bv_unsigned a ∧
      bv_unsigned a < bv_unsigned addr + (n : Int) → m a = none)
    (hnw : bv_unsigned addr + (n : Int) ≤ 2 ^ 64)
    (hbase : (seg.seg_base : Int) ≤ bv_unsigned addr) :
    seg_ov_read_bytes m seg addr n =
      segment_read_bytes seg.seg_bytes (Int.toNat (bv_unsigned addr - seg.seg_base)) n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    have h0 : m addr = none := hc addr (by omega)
    simp only [seg_ov_read_bytes, segment_read_bytes, h0]
    cases hb : segment_byte_at seg.seg_bytes (Int.toNat (bv_unsigned addr - seg.seg_base)) with
    | none => rfl
    | some b =>
      simp only
      cases n with
      | zero => rfl
      | succ n =>
        have hu : bv_unsigned (addr + 1) = bv_unsigned addr + 1 :=
          u_add1 addr (by omega)
        have hc' : ∀ a, bv_unsigned (addr + 1) ≤ bv_unsigned a ∧
            bv_unsigned a < bv_unsigned (addr + 1) + ((n + 1 : Nat) : Int) → m a = none := by
          intro a ha
          apply hc a
          rw [hu] at ha
          omega
        rw [ih (addr + 1) hc' (by rw [hu]; omega) (by rw [hu]; omega)]
        have hoff : Int.toNat (bv_unsigned (addr + 1) - (seg.seg_base : Int)) =
            Int.toNat (bv_unsigned addr - (seg.seg_base : Int)) + 1 := by
          rw [hu]
          omega
        rw [hoff]
        cases segment_read_bytes seg.seg_bytes
          (Int.toNat (bv_unsigned addr - (seg.seg_base : Int)) + 1) (n + 1) <;> rfl

theorem code_read_ov_eq_wx (segs : List Segment) (m : word → Option byte)
    (addr : word) (n : Nat)
    (hc : ∀ a, bv_unsigned addr ≤ bv_unsigned a ∧
      bv_unsigned a < bv_unsigned addr + (n : Int) → m a = none)
    (hnw : bv_unsigned addr + (n : Int) ≤ 2 ^ 64) :
    code_read_ov segs m addr n = code_read_wx segs addr n := by
  cases hs : find_segment segs (bv_unsigned addr) n with
  | none => simp only [code_read_ov, code_read_wx, hs]
  | some seg =>
      simp only [code_read_ov, code_read_wx, hs]
      by_cases hp : (seg_executable seg && seg_writable seg) = true
      · simp only [ite_eq_left hp]
        exact seg_ov_read_bytes_static n m seg addr hc hnw
          (find_segment_range segs (bv_unsigned addr) n seg hs).1
      · simp only [ite_eq_right hp]

theorem fetch_word_ov_of_wx (segs : List Segment) (m : word → Option byte)
    (pc : word) (w : BitVec 32) (lo hi : Int)
    (hc : mem_clear m lo hi) (hlo : lo ≤ bv_unsigned pc)
    (hhi : bv_unsigned pc + 4 ≤ hi) (hceil : hi ≤ 2 ^ 64)
    (hf : fetch_word_wx segs pc = some w) : fetch_word_ov segs m pc = some w := by
  have hread : code_read_ov segs m pc 4 = code_read_wx segs pc 4 := by
    apply code_read_ov_eq_wx
    · intro a ha
      apply hc a
      omega
    · omega
  simpa only [fetch_word_ov, fetch_word_wx, hread] using hf

def wx_fetch (segs : List Segment) (m : word → Option byte)
    (pc : word) (w : BitVec 32) : Prop :=
  fetch_word segs pc = none ∧ fetch_word_ov segs m pc = some w

theorem wx_fetch_intro (segs : List Segment) (m : word → Option byte)
    (pc : word) (w : BitVec 32) (lo hi : Int)
    (hro : no_ro_exec segs = true) (hc : mem_clear m lo hi)
    (hlo : lo ≤ bv_unsigned pc) (hhi : bv_unsigned pc + 4 ≤ hi) (hceil : hi ≤ 2 ^ 64)
    (hf : fetch_word_wx segs pc = some w) : wx_fetch segs m pc w :=
  ⟨fetch_word_none_no_ro_exec segs pc hro,
   fetch_word_ov_of_wx segs m pc w lo hi hc hlo hhi hceil hf⟩

end LinuxProcessSemantics.Common.WxExec
