import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
import Init.Data.String.Lemmas.Basic

set_option autoImplicit false
/-! Kernel-checked certificates for ASCII hex snapshots.

Lean string literals expand through UTF-8 encoding in the kernel. Repeating
that encoding at every instruction fetch is expensive. These lemmas expose
list indexing for a string whose characters are all one UTF-8 byte, with an
explicit proof of that condition. The original string and segment records
remain the memory image used by the semantics.
-/
namespace LinuxProcessSemantics.Common.ImageBytes
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.Riscv.Prelude

theorem utf8Encode_ascii (cs : List Char)
    (h : cs.all (fun c => c.utf8Size == 1) = true) :
    cs.utf8Encode = (cs.map Char.toUInt8).toByteArray := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, hs⟩ := h
    rw [List.utf8Encode_cons, List.utf8Encode_singleton,
      String.utf8EncodeChar_eq_singleton hc, ih hs]
    simp only [List.map_cons, ← List.toByteArray_append]
    rfl

def hex_chars_byte_at (cs : List Char) (i : Nat) : Option byte :=
  if hlt : 2 * i + 1 < cs.length then
    let h := hex_nybble (cs[2 * i]'(by omega)).toUInt8
    let l := hex_nybble (cs[2 * i + 1]'hlt).toUInt8
    if h < 16 ∧ l < 16 then some (Z_to_bv 8 ((h * 16 + l : Nat) : Int)) else none
  else none

theorem hex_byte_at_ofList_ascii (cs : List Char)
    (h : cs.all (fun c => c.utf8Size == 1) = true) (i : Nat) :
    hex_byte_at (String.ofList cs) i = hex_chars_byte_at cs i := by
  simp only [hex_byte_at, String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    utf8Encode_ascii cs h, List.size_toByteArray, List.length_map,
    List.getElem_toByteArray, List.getElem_map, hex_chars_byte_at]

theorem utf8ByteSize_ofList_ascii (cs : List Char)
    (h : cs.all (fun c => c.utf8Size == 1) = true) :
    (String.ofList cs).utf8ByteSize = cs.length := by
  rw [← String.size_toByteArray, String.toByteArray_ofList, utf8Encode_ascii cs h,
    List.size_toByteArray, List.length_map]

def ascii_segment_byte_at (chunks : List (List Char)) (off : Nat) : Option byte :=
  match chunks with
  | [] => none
  | cs :: rest =>
    if off < cs.length / 2 then hex_chars_byte_at cs off
    else ascii_segment_byte_at rest (off - cs.length / 2)

def ascii_segment_read_bytes (chunks : List (List Char)) (off n : Nat)
    : Option (List byte) :=
  match n with
  | 0 => some []
  | n + 1 =>
    match ascii_segment_byte_at chunks off with
    | none => none
    | some b =>
      match ascii_segment_read_bytes chunks (off + 1) n with
      | none => none
      | some bs => some (b :: bs)

theorem segment_byte_at_ascii (chunks : List (List Char))
    (h : ∀ cs ∈ chunks, cs.all (fun c => c.utf8Size == 1) = true) (off : Nat) :
    segment_byte_at (chunks.map String.ofList) off = ascii_segment_byte_at chunks off := by
  induction chunks generalizing off with
  | nil => rfl
  | cons cs rest ih =>
    have hc := h cs (List.mem_cons_self)
    simp only [List.map_cons, segment_byte_at, utf8ByteSize_ofList_ascii cs hc,
      ascii_segment_byte_at]
    split
    · exact hex_byte_at_ofList_ascii cs hc off
    · exact ih (fun c hm => h c (List.mem_cons_of_mem cs hm)) _

theorem segment_read_bytes_ascii (chunks : List (List Char))
    (h : ∀ cs ∈ chunks, cs.all (fun c => c.utf8Size == 1) = true) (off n : Nat) :
    segment_read_bytes (chunks.map String.ofList) off n =
      ascii_segment_read_bytes chunks off n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    simp only [segment_read_bytes, segment_byte_at_ascii chunks h, ascii_segment_read_bytes]
    rw [ih]
    rfl

theorem fetch_word_wx_of_bytes (segs : List Segment) (seg : Segment) (pc : word)
    (b0 b1 b2 b3 : byte)
    (ha : bv_unsigned pc % 2 = 0)
    (hf : find_segment segs (bv_unsigned pc) (↑(4 : Nat)) = some seg)
    (hx : seg_executable seg = true) (hw : seg_writable seg = true)
    (hb : segment_read_bytes seg.seg_bytes (bv_unsigned pc - seg.seg_base).toNat 4 =
      some [b0, b1, b2, b3]) :
    fetch_word_wx segs pc = some (le4 b3 b2 b1 b0) := by
  simp only [fetch_word_wx, ha, decide_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, code_read_wx, hf, hx, hw, Bool.and_self]
  rw [hb]

theorem fetch_word_of_bytes (segs : List Segment) (seg : Segment) (pc : word)
    (b0 b1 b2 b3 : byte)
    (ha : bv_unsigned pc % 2 = 0)
    (hf : find_segment segs (bv_unsigned pc) (↑(4 : Nat)) = some seg)
    (hx : seg_executable seg = true) (hw : seg_writable seg = false)
    (hb : segment_read_bytes seg.seg_bytes (bv_unsigned pc - seg.seg_base).toNat 4 =
      some [b0, b1, b2, b3]) :
    fetch_word segs pc = some (le4 b3 b2 b1 b0) := by
  simp only [fetch_word, ha, decide_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, code_read, hf, hx, hw, Bool.not_false, Bool.and_self]
  rw [hb]

theorem store_ok_empty_step_of_byte (segs : List Segment) (seg : Segment)
    (a : word) (n : Nat) (b : byte)
    (hf : find_segment segs (bv_unsigned a) 1 = some seg)
    (hw : seg_writable seg = true)
    (hb : segment_byte_at seg.seg_bytes (bv_unsigned a - seg.seg_base).toNat = some b)
    (ht : store_ok segs (fun _ => none) (a + 1) n = true) :
    store_ok segs (fun _ => none) a (n + 1) = true := by
  simp only [store_ok, wview, hf, hw, ↓reduceIte, hb]
  exact ht

theorem hex_chars_byte_at_isSome (cs : List Char) (i : Nat)
    (hv : cs.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true)
    (hi : 2 * i + 1 < cs.length) : (hex_chars_byte_at cs i).isSome = true := by
  have hv' := List.all_eq_true.mp hv
  have hh : hex_nybble (cs[2 * i]'(by omega)).toUInt8 < 16 := by
    simpa using hv' _ (List.getElem_mem (by omega))
  have hl : hex_nybble cs[2 * i + 1].toUInt8 < 16 := by
    simpa using hv' _ (List.getElem_mem hi)
  simp [hex_chars_byte_at, hi, hh, hl]

theorem ascii_segment_read_bytes_single_isSome (cs : List Char)
    (hv : cs.all (fun c => decide (hex_nybble c.toUInt8 < 16)) = true)
    (off n : Nat) (hr : off + n ≤ cs.length / 2) :
    (ascii_segment_read_bytes [cs] off n).isSome = true := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have ho : off < cs.length / 2 := by omega
    have hb : (ascii_segment_byte_at [cs] off).isSome = true := by
      simp only [ascii_segment_byte_at, ite_eq_left ho]
      exact hex_chars_byte_at_isSome cs off hv (by omega)
    have ht := ih (off + 1) (by omega)
    simp only [ascii_segment_read_bytes]
    cases he : ascii_segment_byte_at [cs] off with
    | none => simp [he] at hb
    | some b =>
      cases he' : ascii_segment_read_bytes [cs] (off + 1) n with
      | none => simp [he'] at ht
      | some bs => rfl

theorem memory_read_isSome_of_segment (segs : List Segment) (seg : Segment)
    (a : word) (n : Nat)
    (hf : find_segment segs (bv_unsigned a) (n : Int) = some seg)
    (hr : seg_readable seg = true)
    (hb : (segment_read_bytes seg.seg_bytes (bv_unsigned a - seg.seg_base).toNat n).isSome = true) :
    (memory_read segs a n).isSome = true := by
  simp only [memory_read, hf, hr, ↓reduceIte]
  exact hb

end LinuxProcessSemantics.Common.ImageBytes
