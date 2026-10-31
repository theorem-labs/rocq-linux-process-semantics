import LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_defs
import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/
/-! Mirrors `theories/Examples/grep_args_ns/grep_args_ns_source.v` at the baseline above;
this proof-side file symbolically executes the musl-gcc source image from entry
to the exit ecall, for the argc ≥ 2 and argc < 2 branches glued by Proof.v.
Rocq Z is Int, nat is Nat, firstn/skipn are List.take/List.drop, and Section
variables become explicit arguments or `variable`s. Shared stack scaffolding
is reused from Common.ArgvEnv; instruction blocks use Common.StepTac.
-/

namespace LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.MuslStrlen
open LinuxProcessSemantics.Common.ImageBytes
open LinuxProcessSemantics.Common.ArgvEnv
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_code
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_defs
open LinuxProcessSemantics.Examples.grep_args_ns.SourceMemImage

section SourceProof
variable (av ev : List (List byte)) (uid hw : word)
variable (Hva : valid_argv av) (Hve : valid_envp ev)
/- The initial stack pointer is quantified (ASLR), anywhere in the valid window.
The entry draw is likewise unconstrained: neither its AT_RANDOM bytes nor the
last-page bytes above that block may be assumed, and each binary has its own draw. -/
variable (rsp : word) (rrnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
variable (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)

/- Rocq rsp_lo_num/rsp_hi_num are ArgvEnv.sp_lo_num/sp_hi_num. -/
theorem source_init_pc_val : SourceMemImage_init_pc = 0x11174 := by decide

/- argcN, wmem, u_argcN, envp_ptr and envp_ptr_eq are reused from ArgvEnv.
Its bsb_nw supplies Rocq source_bsb_nw, the initial image's no-overflow bound. -/
def rrom : word → Option byte := seg_rom source_segs

local notation "wm" => wmem source_phdrs rsp av ev uid hw rrnd

/-- Memory after _start's environ store and main's six callee-save stores,
in execution order. The two lowest frame slots remain spill scratch for write. -/
def fmem : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes wm
    0x13000 (word_to_le_bytes 8 (envp_ptr rsp av)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x30)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x111a0 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x28)) (word_to_le_bytes 8 (Z_to_bv 64 0))

local notation "fm" => fmem av ev uid hw rsp rrnd

local macro "ga_u" : tactic =>
  `(tactic| simp (disch := omega) only [length_N_to_le_bytes, u_Z2bv])

include Hsp_lo Hsp_hi in
/-- Reads at or above the initial sp see through the frame stores;
the no-overflow premise matches rdn_wbytes_disjoint. -/
theorem rdn_fmem_above (a : word) (n : Nat)
    (Ha : bv_unsigned rsp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs fm a n = rdn source_segs wm a n := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  unfold fmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by ga_u <;> imm_norm <;> omega) Hn]

/- Reads over wmem at/above sp use ArgvEnv.rdn_wmem_stack. -/
include Hva Hve Hsp_lo Hsp_hi in
/-- argc at rsp. -/
theorem read_argc_f : rdn source_segs fm rsp 8 = some (word_le8 (argcN av)) := by
  have hhi := sp_hi_num rsp Hsp_hi
  rw [rdn_fmem_above av ev uid hw rsp rrnd Hsp_lo Hsp_hi rsp 8 (by omega) (by omega)]
  exact read_argc_w source_segs source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi

include Hva Hve Hsp_lo Hsp_hi in
/-- argv pointer k at rsp + 8 + 8k. -/
theorem read_ptr_f (k : Nat) (Hk : k < av.length) :
    rdn source_segs fm (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (k : Int))) 8 =
      some (word_le8 (cat_argv_ptr rsp av ev k)) := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  have hl := valid_argv_len av Hva
  have he : Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (k : Int)) =
      rsp + nat_to_word (8 + 8 * k) := by
    rw [word_add_nat]
    congr 1
    omega
  rw [he, rdn_fmem_above av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; ga_u; omega) (by rw [word_add_nat]; ga_u; omega)]
  exact read_argv_ptr_w source_segs source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_lo Hsp_hi k Hk

/- Rocq source_ptr_bounds is ArgvEnv.argv_ptr_bounds_at. -/
include Hva Hve Hsp_lo Hsp_hi in
/-- String byte j, including the NUL sentinel at j = len. -/
theorem read_str_byte_f (k j : Nat) (Hk : k < av.length)
    (Hj : j ≤ (av.getD k []).length) :
    rdn source_segs fm (cat_argv_ptr rsp av ev k + nat_to_word j) 1 =
      some [byte_at (av.getD k []) j] := by
  obtain ⟨Hge, Hup⟩ := argv_ptr_bounds_at rsp av ev Hva Hve Hsp_hi k Hk
  have Hslen := valid_argv_str_len av k Hva Hk
  have hr := u64_range rsp
  have hp := u64_range (cat_argv_ptr rsp av ev k)
  rw [rdn_fmem_above av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; ga_u; omega) (by rw [word_add_nat]; ga_u; omega)]
  rw [rdn_wmem_stack source_segs source_phdrs rsp av ev uid hw rrnd _ _
    (by rw [word_add_nat]; ga_u; omega) (by rw [word_add_nat]; ga_u; omega)]
  exact read_argv_byte_k source_phdrs source_segs rsp av ev k j uid hw rrnd Hk Hj
    (bsb_nw source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi in
/-- Whole string k. -/
theorem read_str_f (k : Nat) (Hk : k < av.length) :
    rdn source_segs fm (cat_argv_ptr rsp av ev k) (av.getD k []).length =
      some (av.getD k []) := by
  obtain ⟨Hge, Hup⟩ := argv_ptr_bounds_at rsp av ev Hva Hve Hsp_hi k Hk
  rw [rdn_fmem_above av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ _ Hge (by omega)]
  rw [rdn_wmem_stack source_segs source_phdrs rsp av ev uid hw rrnd _ _ Hge (by omega)]
  exact read_argv_str_k source_phdrs source_segs rsp av ev k uid hw rrnd Hk
    (bsb_nw source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi)

/- Rocq source_ptr_room is MuslStrlen.argv_ptr_room: the pad and AT_RANDOM
provide room for a whole word beyond any offset inside an argv string. -/
-- The generated append tree needs more than the default conversion recursion depth.
set_option maxRecDepth 4096 in
private theorem ga_newline_prefix : SourceMemImage_seg_bytes_002_chars =
    '0' :: 'a' :: SourceMemImage_seg_bytes_002_chars.drop 2 := by rfl
private theorem ga_newline_ascii (tail : List Char) :
    ascii_segment_read_bytes ['0' :: 'a' :: tail] 0 1 = some [Z_to_bv 8 10] := by
  have hlen : 0 < (('0' :: 'a' :: tail).length / 2) := by
    simp only [List.length_cons]; omega
  have hi : 2 * 0 + 1 < ('0' :: 'a' :: tail).length := by
    simp only [List.length_cons]; omega
  simp only [ascii_segment_read_bytes, ascii_segment_byte_at, ite_eq_left hlen,
    hex_chars_byte_at, dite_eq_left hi]
  rfl

private theorem ga_newline_read :
    segment_read_bytes SourceMemImage_segment_002.seg_bytes 0 1 = some [Z_to_bv 8 10] :=
  (SourceMemImage_segment_002_read_ascii 0 1).trans
    ((congrArg (fun cs => ascii_segment_read_bytes [cs] 0 1) ga_newline_prefix).trans
      (ga_newline_ascii _))

private theorem ga_rom_byte (segs : List Segment) (seg : Segment) (a : word) (b : byte)
    (hf : find_segment segs (bv_unsigned a) (↑(1 : Nat)) = some seg)
    (hs : seg_readable seg = true)
    (hb : segment_read_bytes seg.seg_bytes (bv_unsigned a - (seg.seg_base : Int)).toNat 1 =
      some [b]) : seg_rom segs a = some b := by
  simp only [seg_rom, LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read,
    hf, hs, ↓reduceIte, hb]

/-- The newline byte in the source image. -/
theorem seg_rom_newline : seg_rom source_segs 0x12000 = some (Z_to_bv 8 10) :=
  ga_rom_byte source_segs SourceMemImage_segment_002 0x12000 (Z_to_bv 8 10)
    rfl rfl ga_newline_read

include Hsp_lo Hsp_hi in
theorem read_newline_f : rdn source_segs fm 0x12000 1 = some [Z_to_bv 8 10] := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  unfold fmem
  repeat rw [rdn_wbytes_below _ _ _ _ _ _ (by ga_u <;> imm_norm <;> omega)
    (by ga_u <;> imm_norm <;> omega)]
  rw [rdn_wbytes_below _ _ _ _ _ _ (by decide)
    (by rw [length_N_to_le_bytes]; decide)]
  simp only [rdn]
  unfold wmem
  rw [wrap_mem_below source_phdrs rsp av ev 0x12000 uid hw rrnd (by
    rw [stack_max_size_val]; imm_norm; omega)]
  rw [seg_rom_newline]

include Hsp_lo Hsp_hi in
/-- Frame-slot read-back for the epilogue. -/
theorem read_slot_ra :
    rdn source_segs fm (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111a0 : word)) := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  unfold fmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by ga_u; omega) (by ga_u; omega)]
  exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega)

include Hsp_lo Hsp_hi in
theorem read_slot_0 (a : word)
    (Ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x30), Z_to_bv 64 (bv_unsigned rsp - 0x28),
      Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18),
      Z_to_bv 64 (bv_unsigned rsp - 0x10)]) :
    rdn source_segs fm a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
  rcases Ha with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold fmem
    repeat first
      | rw [rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega)]
      | rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by ga_u; omega) (by ga_u; omega)]
      | rw [rdn_wbytes_below _ _ _ _ _ _ (by ga_u; omega) (by ga_u; omega)]

/- Memories agree with fmem outside [rsp-0x50,rsp-0x30): the wrapper's
16-byte frame and main's two spill slots. Writability of the initial overlay
must survive the scratch stores, so the second clause carries mem_grows.
Both clauses remain under one forall; explicit constructors below preserve
this abstraction without Rocq's Opaque command. -/
def mem_ok (mem : word → Option byte) : Prop :=
  ∀ (a : word) (n : Nat),
    (bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
      (bv_unsigned rsp - 0x30 ≤ bv_unsigned a ∨
        bv_unsigned a + (n : Int) ≤ bv_unsigned rsp - 0x50) →
      rdn source_segs mem a n = rdn source_segs fm a n) ∧
    (wm a ≠ none → mem a ≠ none)

/-- These projections are the interface used below the invariant. -/
theorem mem_ok_agree (mem : word → Option byte) (H : mem_ok av ev uid hw rsp rrnd mem)
    (a : word) (n : Nat) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (Hd : bv_unsigned rsp - 0x30 ≤ bv_unsigned a ∨
      bv_unsigned a + (n : Int) ≤ bv_unsigned rsp - 0x50) :
    rdn source_segs mem a n = rdn source_segs fm a n := (H a n).1 Hn Hd

theorem mem_ok_grows (mem : word → Option byte) (H : mem_ok av ev uid hw rsp rrnd mem) :
    mem_grows wm mem := fun x => (H x 0).2

local macro_rules
  | `(tactic| store_ok_grows) => `(tactic| (apply mem_ok_grows; assumption))

theorem fmem_ok : mem_ok av ev uid hw rsp rrnd fm := by
  have Hg : mem_grows wm fm := by unfold fmem; solve_mem_grows
  intro a n
  exact ⟨fun _ _ => rfl, Hg a⟩

include Hsp_hi in
/-- An eight-byte store inside the scratch window preserves mem_ok. -/
theorem mem_ok_scratch8 (mem : word → Option byte) (a v : word)
    (Hm : mem_ok av ev uid hw rsp rrnd mem)
    (Hlo : bv_unsigned rsp - 0x50 ≤ bv_unsigned a)
    (Hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp - 0x30) :
    mem_ok av ev uid hw rsp rrnd (wbytes mem a (word_to_le_bytes 8 v)) := by
  have Hg := mem_ok_grows av ev uid hw rsp rrnd mem Hm
  have Hg' : mem_grows wm (wbytes mem a (word_to_le_bytes 8 v)) := by solve_mem_grows
  intro a' n
  refine ⟨?_, Hg' a'⟩
  intro Hnw Hd
  rcases Hd with Hd | Hd
  · rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; omega) Hnw]
    exact mem_ok_agree av ev uid hw rsp rrnd mem Hm a' n Hnw (Or.inl Hd)
  · have hhi := sp_hi_num rsp Hsp_hi
    rw [rdn_wbytes_below _ _ _ _ _ _ (by omega) (by rw [length_N_to_le_bytes]; omega)]
    exact mem_ok_agree av ev uid hw rsp rrnd mem Hm a' n Hnw (Or.inr Hd)

/- mem_ok-relative read lemmas. -/
include Hva Hve Hsp_lo Hsp_hi in
theorem read_ptr_m (mem : word → Option byte) (Hm : mem_ok av ev uid hw rsp rrnd mem)
    (k : Nat) (Hk : k < av.length) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (k : Int))) 8 =
      some (word_le8 (cat_argv_ptr rsp av ev k)) := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  have hl := valid_argv_len av Hva
  rw [mem_ok_agree av ev uid hw rsp rrnd mem Hm _ _
    (by ga_u; omega) (Or.inl (by ga_u; omega))]
  exact read_ptr_f av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi k Hk

include Hva Hve Hsp_lo Hsp_hi in
theorem read_str_byte_m (mem : word → Option byte) (Hm : mem_ok av ev uid hw rsp rrnd mem)
    (k j : Nat) (Hk : k < av.length) (Hj : j ≤ (av.getD k []).length) :
    rdn source_segs mem (cat_argv_ptr rsp av ev k + nat_to_word j) 1 =
      some [byte_at (av.getD k []) j] := by
  obtain ⟨Hge, Hup⟩ := argv_ptr_bounds_at rsp av ev Hva Hve Hsp_hi k Hk
  have Hslen := valid_argv_str_len av k Hva Hk
  have hlo := sp_lo_num rsp Hsp_lo
  rw [mem_ok_agree av ev uid hw rsp rrnd mem Hm _ _
    (by rw [word_add_nat]; ga_u; omega) (Or.inl (by rw [word_add_nat]; ga_u; omega))]
  exact read_str_byte_f av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi k j Hk Hj

include Hva Hve Hsp_lo Hsp_hi in
theorem read_str_m (mem : word → Option byte) (Hm : mem_ok av ev uid hw rsp rrnd mem)
    (k : Nat) (Hk : k < av.length) :
    rdn source_segs mem (cat_argv_ptr rsp av ev k) (av.getD k []).length =
      some (av.getD k []) := by
  obtain ⟨Hge, Hup⟩ := argv_ptr_bounds_at rsp av ev Hva Hve Hsp_hi k Hk
  rw [mem_ok_agree av ev uid hw rsp rrnd mem Hm _ _ (by omega) (Or.inl (by omega))]
  exact read_str_f av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi k Hk

include Hsp_lo Hsp_hi in
theorem read_newline_m (mem : word → Option byte) (Hm : mem_ok av ev uid hw rsp rrnd mem) :
    rdn source_segs mem 0x12000 1 = some [Z_to_bv 8 10] := by
  have hlo := sp_lo_num rsp Hsp_lo
  rw [mem_ok_agree av ev uid hw rsp rrnd mem Hm _ _ (by decide)
    (Or.inr (by imm_norm; omega))]
  exact read_newline_f av ev uid hw rsp rrnd Hsp_lo Hsp_hi

include Hsp_lo Hsp_hi in
theorem read_slot_ra_m (mem : word → Option byte) (Hm : mem_ok av ev uid hw rsp rrnd mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111a0 : word)) := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  rw [mem_ok_agree av ev uid hw rsp rrnd mem Hm _ _
    (by ga_u; omega) (Or.inl (by ga_u; omega))]
  exact read_slot_ra av ev uid hw rsp rrnd Hsp_lo Hsp_hi

include Hsp_lo Hsp_hi in
theorem read_slot_0_m (mem : word → Option byte) (Hm : mem_ok av ev uid hw rsp rrnd mem)
    (a : word) (Ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x30),
      Z_to_bv 64 (bv_unsigned rsp - 0x28), Z_to_bv 64 (bv_unsigned rsp - 0x20),
      Z_to_bv 64 (bv_unsigned rsp - 0x18), Z_to_bv 64 (bv_unsigned rsp - 0x10)]) :
    rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  have hb : bv_unsigned a + 8 ≤ 2 ^ 64 ∧ bv_unsigned rsp - 0x30 ≤ bv_unsigned a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
    rcases Ha with rfl | rfl | rfl | rfl | rfl <;> ga_u <;> constructor <;> omega
  rw [mem_ok_agree av ev uid hw rsp rrnd mem Hm _ _ hb.1 (Or.inl hb.2)]
  exact read_slot_0 av ev uid hw rsp rrnd Hsp_lo Hsp_hi a Ha

include Hva Hve Hsp_lo Hsp_hi in
/-- Peel the frame overlay and use MuslStrlen's pad/AT_RANDOM argument:
an eight-byte load inside an argv string never faults. -/
theorem read_word_m (mem : word → Option byte) (Hmk : mem_ok av ev uid hw rsp rrnd mem)
    (k m : Nat) (Hk : k < av.length) (Hm : m ≤ (av.getD k []).length) :
    ∃ bs, bs.length = 8 ∧
      rdn source_segs mem (cat_argv_ptr rsp av ev k + nat_to_word m) 8 = some bs := by
  have hlo := sp_lo_num rsp Hsp_lo
  have hhi := sp_hi_num rsp Hsp_hi
  obtain ⟨Hge, Hup⟩ := argv_ptr_bounds_at rsp av ev Hva Hve Hsp_hi k Hk
  have Hroom := argv_ptr_room source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_lo Hsp_hi k Hk
  have Hnw := bsb_nw source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi
  have hp := u64_range (cat_argv_ptr rsp av ev k)
  have Hu : bv_unsigned (cat_argv_ptr rsp av ev k + nat_to_word m) =
      bv_unsigned (cat_argv_ptr rsp av ev k) + (m : Int) := by
    rw [word_add_nat]; exact u_Z2bv _ (by omega) (by omega)
  obtain ⟨bs, Hl, Hr⟩ := argv_word_readable source_segs source_phdrs rsp av ev uid hw rrnd
    Hva Hve Hsp_lo Hsp_hi k m Hk Hm
  refine ⟨bs, Hl, ?_⟩
  rw [mem_ok_agree av ev uid hw rsp rrnd mem Hmk _ _ (by rw [Hu]; omega)
    (Or.inl (by rw [Hu]; omega))]
  rw [rdn_fmem_above av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [Hu]; omega) (by rw [Hu]; omega)]
  exact Hr

include Hva Hve Hsp_lo Hsp_hi in
/-- The loaded word's bytes agree with the string as far as its NUL. -/
theorem read_word_nth (mem : word → Option byte) (Hmk : mem_ok av ev uid hw rsp rrnd mem)
    (k m : Nat) (bs : List byte) (j : Nat) (Hk : k < av.length)
    (Hr : rdn source_segs mem (cat_argv_ptr rsp av ev k + nat_to_word m) 8 = some bs)
    (Hj : j < 8) (Hmj : m + j ≤ (av.getD k []).length) :
    bs.getD j (Z_to_bv 8 0) = byte_at (av.getD k []) (m + j) := by
  apply word_bytes_nth source_segs mem (cat_argv_ptr rsp av ev k) (av.getD k []) m bs j Hr
  · intro i Hi
    exact read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmk k i Hk Hi
  · exact Hj
  · exact Hmj

/- Epilogue, reloads through ret to the exit ecall. Rocq's s_slot_rd
batch dispatcher is replaced by explicit read_slot_*_m applications at each ld. -/
include Hsp_lo Hsp_hi in
theorem source_epilogue (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (H10 : reg_get regs 10 = code) (Hc : bv_unsigned code < 256) :
    to_wallexit source_segs (Z_to_bv 64 1) [] code (mkst regs 0x11140 mem rrom) := by
  have Hlo := sp_lo_num rsp Hsp_lo
  have Hhi := sp_hi_num rsp Hsp_hi
  stepld SF_11140 SD_11140 (Z_to_bv 64 (bv_unsigned rsp - 8)) (0x111a0 : word)
    (exact read_slot_ra_m av ev uid hw rsp rrnd Hsp_lo Hsp_hi mem Hmem)
  stepld SF_11144 SD_11144 (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (Z_to_bv 64 0)
    (apply read_slot_0_m av ev uid hw rsp rrnd Hsp_lo Hsp_hi mem Hmem
     simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
  stepld SF_11148 SD_11148 (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (Z_to_bv 64 0)
    (apply read_slot_0_m av ev uid hw rsp rrnd Hsp_lo Hsp_hi mem Hmem
     simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or])
  stepld SF_1114c SD_1114c (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (Z_to_bv 64 0)
    (apply read_slot_0_m av ev uid hw rsp rrnd Hsp_lo Hsp_hi mem Hmem
     simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or])
  stepld SF_11150 SD_11150 (Z_to_bv 64 (bv_unsigned rsp - 0x28)) (Z_to_bv 64 0)
    (apply read_slot_0_m av ev uid hw rsp rrnd Hsp_lo Hsp_hi mem Hmem
     simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or])
  stepld SF_11154 SD_11154 (Z_to_bv 64 (bv_unsigned rsp - 0x30)) (Z_to_bv 64 0)
    (apply read_slot_0_m av ev uid hw rsp rrnd Hsp_lo Hsp_hi mem Hmem
     exact List.mem_cons_self)
  stepiv SF_11158 SD_11158 rsp (getr_resolve; rw [H2]; sp_norm; rw [show bv_unsigned rsp - 64 + 64 = bv_unsigned rsp by omega]; apply bv_eq_of_unsigned; rw [u_Z2bv _ (by omega) (by omega)])
  stepjr SF_1115c SD_1115c (0x111a0 : word) (getr_resolve; bveq)
  stepi SF_111a0 SD_111a0
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ SF_111a4 rfl
  · apply tw_exit_coden
    · getr_resolve; rfl
    · regupd_resolve; exact H10
    · exact Hc

/- musl write, through the syscall shuffle, ecall, and __syscall_ret.
The environment chooses a nonempty delivered prefix. The continuation gets
that length in a0 and the undelivered tail; positivity keeps the errno branch
dead. The scratch store preserves mem_ok and every register except a0/a3..a7. -/
include Hsp_lo Hsp_hi in
theorem source_write_fn (K : machine_state → Prop) (regs : bvmap 5 word)
    (mem : word → Option byte) (buf : List byte) (RA : word)
    (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (H10 : reg_get regs 10 = Z_to_bv 64 1) (H1 : reg_get regs 1 = RA)
    (Hvj : v_jalr RA 0 = RA)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (H12lo : 1 ≤ bv_unsigned (reg_get regs 12))
    (H12 : bv_unsigned (reg_get regs 12) ≤ 131072)
    (Hnov : bv_unsigned (reg_get regs 11) + bv_unsigned (reg_get regs 12) ≤ 2 ^ 64)
    (Hdisj : bv_unsigned rsp - 0x30 ≤ bv_unsigned (reg_get regs 11) ∨
      bv_unsigned (reg_get regs 11) + bv_unsigned (reg_get regs 12) ≤ bv_unsigned rsp - 0x50)
    (Hbuf : rdn source_segs fm (reg_get regs 11) (word_to_nat (reg_get regs 12)) = some buf)
    (Hcont : ∀ regs' mem' k, 1 ≤ k → k ≤ buf.length →
      mem_ok av ev uid hw rsp rrnd mem' →
      (∀ (a : word) (n : Nat), bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
        (bv_unsigned rsp - 0x40 ≤ bv_unsigned a ∨
          bv_unsigned a + (n : Int) ≤ bv_unsigned rsp - 0x50) →
        rdn source_segs mem' a n = rdn source_segs mem a n) →
      (∀ r : reg, r ≠ 10 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regs' r = reg_get regs r) →
      reg_get regs' 10 = len_word (buf.take k) →
      to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs' RA mem' rrom) (buf.drop k) K) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x111cc mem rrom) buf K := by
  have Hlo := sp_lo_num rsp Hsp_lo
  have Hhi := sp_hi_num rsp Hsp_hi
  have Hbl := rdn_length _ _ _ _ _ Hbuf
  have H12r := u64_range (reg_get regs 12)
  have HbufL : (buf.length : Int) = bv_unsigned (reg_get regs 12) := by
    rw [Hbl, of_nat_word_to_nat]
  have Hm1 : mem_ok av ev uid hw rsp rrnd
      (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x48)) (word_to_le_bytes 8 RA)) :=
    mem_ok_scratch8 av ev uid hw rsp rrnd Hsp_hi mem _ RA Hmem (by ga_u; omega) (by ga_u; omega)
  stepiv SF_111cc SD_111cc (Z_to_bv 64 (bv_unsigned rsp - 0x50))
    (getr_resolve; rw [H2]; sp_norm; congr 1; omega)
  stepiv SF_111d0 SD_111d0 (reg_get regs 12) (getr_resolve; apply v_addi_0)
  stepiv SF_111d4 SD_111d4 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  stepiv SF_111d8 SD_111d8 (reg_get regs 11) (getr_resolve; apply v_addi_0)
  stepiv SF_111dc SD_111dc (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  stepiv SF_111e0 SD_111e0 (Z_to_bv 64 1) (getr_resolve; rw [H10]; apply v_addi_0)
  stepiv SF_111e4 SD_111e4 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  stepiv SF_111e8 SD_111e8 (Z_to_bv 64 64) (getr_resolve; bveq)
  stepsd SF_111ec SD_111ec (Z_to_bv 64 (bv_unsigned rsp - 0x48)) RA
    (getr_resolve; exact H1) (solve_store_ok_inv)
  stepj SF_111f0 SD_111f0
  stepj SF_1125c SD_1125c
  stepiv SF_11238 SD_11238 (Z_to_bv 64 64) (getr_resolve; apply v_addi_0)
  stepiv SF_1123c SD_1123c (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
  stepiv SF_11240 SD_11240 (reg_get regs 11) (getr_resolve; apply v_addi_0)
  stepiv SF_11244 SD_11244 (reg_get regs 12) (getr_resolve; apply v_addi_0)
  stepiv SF_11248 SD_11248 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  stepiv SF_1124c SD_1124c (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  stepiv SF_11250 SD_11250 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ SF_11254 rfl
  · apply to_wall_tail.twt_more
    · omega
    · apply twl_write_rec source_segs (Z_to_bv 64 1)
      · getr_resolve; rfl
      · regupd_resolve; rfl
      · rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        dsimp only [machine_state.ms_mem, machine_state.ms_regs]
        regupd_resolve
        rw [mem_ok_agree av ev uid hw rsp rrnd _ Hm1 _ _
          (by rw [of_nat_word_to_nat]; exact Hnov) (by rw [of_nat_word_to_nat]; exact Hdisj)]
        exact Hbuf
      · omega
      · intro k Hk1 Hk2
        norm_pc
        stepjr SF_11258 SD_11258 (0x111f4 : word) (getr_resolve; regupd_resolve; bveq)
        stepld SF_111f4 SD_111f4 (Z_to_bv 64 (bv_unsigned rsp - 0x48)) RA
          (exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega))
        stepiv SF_111f8 SD_111f8 (Z_to_bv 64 (bv_unsigned rsp - 0x40))
          (getr_resolve; regupd_resolve; sp_norm; congr 1; omega)
        stepj SF_111fc SD_111fc
        /- __syscall_ret has a frameless success path in gcc 15: the errno
        fixup lives in a cold tail. -/
        stepi SF_11200 SD_11200
        chain_step
        · rfl
        · apply step_bltu_ft
          · exact SF_11204
          · rfl
          · exact SD_11204
          · getr_resolve; regupd_resolve
            rw [c_ltu_ltb]
            apply decide_eq_false
            have Hlui : bv_unsigned (v_lui (Z_shiftl (bv_signed (1048575 : BitVec 20)) 12)) = 18446744073709547520 := by decide
            rw [Hlui, u_len_word_firstn k buf Hk2 (by omega)]
            omega
        · norm_pc
          chain_step
          · rfl
          · apply step_jalr_x0 (tgt := RA)
            · exact SF_11208
            · rfl
            · exact SD_11208
            · getr_resolve; rfl
          · imm_norm
            rw [Hvj]
            apply Hcont _ _ k Hk1 Hk2 Hm1
            · intro a n Hn Hd
              rcases Hd with Hd | Hd
              · rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by ga_u; omega) Hn]
              · rw [rdn_wbytes_below _ _ _ _ _ _ (by ga_u; omega) (by ga_u; omega)]
            · intro r Hx10 Hx13 Hx14 Hx15 Hx16 Hx17
              by_cases Hx1 : r = 1
              · subst r; regupd_resolve; exact H1.symm
              by_cases Hx2 : r = 2
              · subst r; regupd_resolve; exact H2.symm
              by_cases Hx11 : r = 11
              · subst r; regupd_resolve; rfl
              by_cases Hx12 : r = 12
              · subst r; regupd_resolve; rfl
              simp (disch := assumption) only [regupd_other]
            · regupd_resolve; rfl
/- With -fno-builtin, gcc keeps three inline byte scans instead of musl
strlen: hay length, pattern length, and the output length recomputation. -/
include Hva Hve Hsp_lo Hsp_hi in
/-- Hay scan from offset j. -/
theorem source_slen_hay (k : Nat) (Hk : k < av.length)
    (mem : word → Option byte) (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (d j : Nat) (regs : bvmap 5 word) (Hjd : j + d = (av.getD k []).length)
    (Hr11 : reg_get regs 11 = cat_argv_ptr rsp av ev k)
    (Hr14 : reg_get regs 14 = nat_to_word j) :
    ∃ regs', (∀ r : reg, r ≠ 14 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 14 = nat_to_word (av.getD k []).length ∧
      msteps source_segs (mkst regs 0x11058 mem rrom) (mkst regs' 0x11064 mem rrom) := by
  have Hslen := valid_argv_str_len av k Hva Hk
  have Hsnz := valid_argv_str_nz av k Hva Hk
  induction d generalizing j regs with
  | zero =>
    have Hj : j = (av.getD k []).length := by omega
    let regs1 := regupd regs 15 (cat_argv_ptr rsp av ev k + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 0)
    refine ⟨regs2, ?_, ?_, ?_⟩
    · intro r Hx14 Hx15
      dsimp only [regs2, regs1]
      simp (disch := assumption) only [regupd_other]
    · dsimp only [regs2, regs1]; regupd_resolve; rw [Hr14, Hj]
    · stepiv SF_11058 SD_11058 (cat_argv_ptr rsp av ev k + nat_to_word j)
        (getr_resolve; rw [Hr11, Hr14, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
      chain_step
      · rfl
      · apply step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) SF_1105c rfl SD_1105c
        getr_resolve
        imm_norm; rw [v_addi_0]
        have hrd := read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
        rw [Hj, byte_at_len] at hrd
        simpa only [Hj] using hrd
      · step_simpl
        chain_step
        · rfl
        · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_11060 rfl SD_11060
          getr_resolve; exact c_eq_0_true
        · norm_pc; exact msteps.mst_refl _
  | succ d IH =>
    have Hjlt : j < (av.getD k []).length := by omega
    let b := byte_at (av.getD k []) j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hsnz Hjlt
    let regs1 := regupd regs 15 (cat_argv_ptr rsp av ev k + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 14 (nat_to_word (j + 1))
    have Hr11' : reg_get regs3 11 = cat_argv_ptr rsp av ev k := by
      dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr11
    have Hr14' : reg_get regs3 14 = nat_to_word (j + 1) := regupd_same _ _ _
    obtain ⟨regs', Hag, H14, Hms⟩ := IH (j + 1) regs3 (by omega) Hr11' Hr14'
    refine ⟨regs', ?_, H14, ?_⟩
    · intro r Hx14 Hx15
      rw [Hag r Hx14 Hx15]
      dsimp only [regs3, regs2, regs1]
      simp (disch := assumption) only [regupd_other]
    · stepiv SF_11058 SD_11058 (cat_argv_ptr rsp av ev k + nat_to_word j)
        (getr_resolve; rw [Hr11, Hr14, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
      chain_step
      · rfl
      · apply step_lbu _ _ _ _ _ _ _ _ _ b SF_1105c rfl SD_1105c
        getr_resolve; imm_norm; rw [v_addi_0]
        exact read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
      · step_simpl
        chain_step
        · rfl
        · apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_11060 rfl SD_11060
          getr_resolve
          apply c_eq_0_false
          rw [u_zext8]
          exact byte_nz_u b Hbnz
        · norm_pc
          stepiv SF_11088 SD_11088 (nat_to_word (j + 1))
            (getr_resolve; rw [Hr14]; exact v_addi_Sj j (by omega))
          stepj SF_1108c SD_1108c
          exact Hms

include Hva Hve Hsp_lo Hsp_hi in
/-- Pattern scan from offset j. -/
theorem source_slen_pat (H2le : 2 ≤ av.length)
    (mem : word → Option byte) (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (d j : Nat) (regs : bvmap 5 word) (Hjd : j + d = (av.getD 1 []).length)
    (Hr19 : reg_get regs 19 = cat_argv_ptr rsp av ev 1)
    (Hr12 : reg_get regs 12 = nat_to_word j) :
    ∃ regs', (∀ r : reg, r ≠ 12 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 12 = nat_to_word (av.getD 1 []).length ∧
      msteps source_segs (mkst regs 0x11068 mem rrom) (mkst regs' 0x11074 mem rrom) := by
  have Hk : 1 < av.length := by omega
  have Hslen := valid_argv_str_len av 1 Hva Hk
  have Hsnz := valid_argv_str_nz av 1 Hva Hk
  induction d generalizing j regs with
  | zero =>
    have Hj : j = (av.getD 1 []).length := by omega
    let regs1 := regupd regs 15 (cat_argv_ptr rsp av ev 1 + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 0)
    refine ⟨regs2, ?_, ?_, ?_⟩
    · intro r Hx12 Hx15
      dsimp only [regs2, regs1]
      simp (disch := assumption) only [regupd_other]
    · dsimp only [regs2, regs1]; regupd_resolve; rw [Hr12, Hj]
    · stepiv SF_11068 SD_11068 (cat_argv_ptr rsp av ev 1 + nat_to_word j)
        (getr_resolve; rw [Hr19, Hr12, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
      chain_step
      · rfl
      · apply step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) SF_1106c rfl SD_1106c
        getr_resolve
        imm_norm; rw [v_addi_0]
        have hrd := read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem 1 j Hk (by omega)
        rw [Hj, byte_at_len] at hrd
        simpa only [Hj] using hrd
      · step_simpl
        chain_step
        · rfl
        · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_11070 rfl SD_11070
          getr_resolve; exact c_eq_0_true
        · norm_pc; exact msteps.mst_refl _
  | succ d IH =>
    have Hjlt : j < (av.getD 1 []).length := by omega
    let b := byte_at (av.getD 1 []) j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hsnz Hjlt
    let regs1 := regupd regs 15 (cat_argv_ptr rsp av ev 1 + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 12 (nat_to_word (j + 1))
    have Hr19' : reg_get regs3 19 = cat_argv_ptr rsp av ev 1 := by
      dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr19
    have Hr12' : reg_get regs3 12 = nat_to_word (j + 1) := regupd_same _ _ _
    obtain ⟨regs', Hag, H12, Hms⟩ := IH (j + 1) regs3 (by omega) Hr19' Hr12'
    refine ⟨regs', ?_, H12, ?_⟩
    · intro r Hx12 Hx15
      rw [Hag r Hx12 Hx15]
      dsimp only [regs3, regs2, regs1]
      simp (disch := assumption) only [regupd_other]
    · stepiv SF_11068 SD_11068 (cat_argv_ptr rsp av ev 1 + nat_to_word j)
        (getr_resolve; rw [Hr19, Hr12, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
      chain_step
      · rfl
      · apply step_lbu _ _ _ _ _ _ _ _ _ b SF_1106c rfl SD_1106c
        getr_resolve; imm_norm; rw [v_addi_0]
        exact read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem 1 j Hk (by omega)
      · step_simpl
        chain_step
        · rfl
        · apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_11070 rfl SD_11070
          getr_resolve
          apply c_eq_0_false
          rw [u_zext8]
          exact byte_nz_u b Hbnz
        · norm_pc
          stepiv SF_11090 SD_11090 (nat_to_word (j + 1))
            (getr_resolve; rw [Hr12]; exact v_addi_Sj j (by omega))
          stepj SF_11094 SD_11094
          exact Hms

include Hva Hve Hsp_lo Hsp_hi in
/-- Recompute the matched argument length for write. This loop is laid out
backwards: its increment precedes the loop head, so it needs no final jump. -/
theorem source_slen_out (k : Nat) (Hk : k < av.length)
    (mem : word → Option byte) (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (d j : Nat) (regs : bvmap 5 word) (Hjd : j + d = (av.getD k []).length)
    (Hr11 : reg_get regs 11 = cat_argv_ptr rsp av ev k)
    (Hr12 : reg_get regs 12 = nat_to_word j) :
    ∃ regs', (∀ r : reg, r ≠ 12 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 12 = nat_to_word (av.getD k []).length ∧
      msteps source_segs (mkst regs 0x110dc mem rrom) (mkst regs' 0x110e8 mem rrom) := by
  have Hslen := valid_argv_str_len av k Hva Hk
  have Hsnz := valid_argv_str_nz av k Hva Hk
  induction d generalizing j regs with
  | zero =>
    have Hj : j = (av.getD k []).length := by omega
    let regs1 := regupd regs 15 (cat_argv_ptr rsp av ev k + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 0)
    refine ⟨regs2, ?_, ?_, ?_⟩
    · intro r Hx12 Hx15
      dsimp only [regs2, regs1]
      simp (disch := assumption) only [regupd_other]
    · dsimp only [regs2, regs1]; regupd_resolve; rw [Hr12, Hj]
    · stepiv SF_110dc SD_110dc (cat_argv_ptr rsp av ev k + nat_to_word j)
        (getr_resolve; rw [Hr11, Hr12, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
      chain_step
      · rfl
      · apply step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) SF_110e0 rfl SD_110e0
        getr_resolve
        imm_norm; rw [v_addi_0]
        have hrd := read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
        rw [Hj, byte_at_len] at hrd
        simpa only [Hj] using hrd
      · step_simpl
        chain_step
        · rfl
        · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_110e4 rfl SD_110e4
          getr_resolve; exact c_eq_0_true
        · norm_pc; exact msteps.mst_refl _
  | succ d IH =>
    have Hjlt : j < (av.getD k []).length := by omega
    let b := byte_at (av.getD k []) j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hsnz Hjlt
    let regs1 := regupd regs 15 (cat_argv_ptr rsp av ev k + nat_to_word j)
    let regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 12 (nat_to_word (j + 1))
    have Hr11' : reg_get regs3 11 = cat_argv_ptr rsp av ev k := by
      dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr11
    have Hr12' : reg_get regs3 12 = nat_to_word (j + 1) := regupd_same _ _ _
    obtain ⟨regs', Hag, H12, Hms⟩ := IH (j + 1) regs3 (by omega) Hr11' Hr12'
    refine ⟨regs', ?_, H12, ?_⟩
    · intro r Hx12 Hx15
      rw [Hag r Hx12 Hx15]
      dsimp only [regs3, regs2, regs1]
      simp (disch := assumption) only [regupd_other]
    · stepiv SF_110dc SD_110dc (cat_argv_ptr rsp av ev k + nat_to_word j)
        (getr_resolve; rw [Hr11, Hr12, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
      chain_step
      · rfl
      · apply step_lbu _ _ _ _ _ _ _ _ _ b SF_110e0 rfl SD_110e0
        getr_resolve; imm_norm; rw [v_addi_0]
        exact read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
      · step_simpl
        chain_step
        · rfl
        · apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_110e4 rfl SD_110e4
          getr_resolve
          apply c_eq_0_false
          rw [u_zext8]
          exact byte_nz_u b Hbnz
        · norm_pc
          stepiv SF_110d8 SD_110d8 (nat_to_word (j + 1))
            (getr_resolve; rw [Hr12]; exact v_addi_Sj j (by omega))
          exact Hms


/- Compare pat[j..) against hay[i+j..). A full match reaches 0x110dc
with a2 cleared; a mismatch reaches 0x110c8 with the pattern length intact.
The clobbers are a0, a2, a5 and a6. -/
include Hva Hve Hsp_lo Hsp_hi in
theorem source_cmp (k : Nat) (Hk : k < av.length) (H2le : 2 ≤ av.length)
    (mem : word → Option byte) (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (i d j : Nat) (regs : bvmap 5 word)
    (Hjd : j + d = (av.getD 1 []).length) (Hd : 1 ≤ d)
    (Hin : i + (av.getD 1 []).length ≤ (av.getD k []).length)
    (Hr15 : reg_get regs 15 = nat_to_word j)
    (Hr17 : reg_get regs 17 = cat_argv_ptr rsp av ev k + nat_to_word i)
    (Hr19 : reg_get regs 19 = cat_argv_ptr rsp av ev 1)
    (Hr12 : reg_get regs 12 = nat_to_word (av.getD 1 []).length) :
    ∃ regs',
      (∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 15 → r ≠ 16 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 12 = (if prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i + j)
        then nat_to_word 0 else nat_to_word (av.getD 1 []).length) ∧
      msteps source_segs (mkst regs 0x110b0 mem rrom)
        (mkst regs' (if prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i + j)
          then 0x110dc else 0x110c8) mem rrom) := by
  have Hhlen := valid_argv_str_len av k Hva Hk
  have Hplen := valid_argv_str_len av 1 Hva (by omega)
  induction d generalizing i j regs with
  | zero => omega
  | succ d IH =>
    have Hjlt : j < (av.getD 1 []).length := by omega
    have HijN : i + j < (av.getD k []).length := by omega
    let bh := byte_at (av.getD k []) (i + j)
    let bp := byte_at (av.getD 1 []) j
    let regs1 := regupd regs 16 (cat_argv_ptr rsp av ev k + nat_to_word (i + j))
    let regs2 := regupd regs1 10 (cat_argv_ptr rsp av ev 1 + nat_to_word j)
    let regs3 := regupd regs2 16 (Z_to_bv 64 (bv_unsigned bh))
    let regs4 := regupd regs3 10 (Z_to_bv 64 (bv_unsigned bp))
    have Hpre : msteps source_segs (mkst regs 0x110b0 mem rrom) (mkst regs4 0x110c0 mem rrom) := by
      stepiv SF_110b0 SD_110b0 (cat_argv_ptr rsp av ev k + nat_to_word (i + j))
        (getr_resolve; rw [Hr17, Hr15, v_add_ntw_merge])
      stepiv SF_110b4 SD_110b4 (cat_argv_ptr rsp av ev 1 + nat_to_word j)
        (getr_resolve; rw [Hr19, Hr15, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
      chain_step
      · rfl
      · apply step_lbu _ _ _ _ _ _ _ _ _ bh SF_110b8 rfl SD_110b8
        getr_resolve; imm_norm; rw [v_addi_0]
        exact read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k (i+j) Hk (by omega)
      · step_simpl
        chain_step
        · rfl
        · apply step_lbu _ _ _ _ _ _ _ _ _ bp SF_110bc rfl SD_110bc
          getr_resolve; imm_norm; rw [v_addi_0]
          exact read_str_byte_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem 1 j (by omega) (by omega)
        · step_simpl; exact msteps.mst_refl _
    have Hspec : prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i+j) =
        (bv_eqb bh bp && prefix_eqb ((av.getD 1 []).drop (j+1)) (av.getD k []) (i+j+1)) := by
      rw [skipn_nth (av.getD 1 []) j (Z_to_bv 8 0) Hjlt]
      dsimp only [prefix_eqb]
      rw [← nth_lt_byte_at (av.getD 1 []) j Hjlt]
    cases Heqb : bv_eqb bh bp with
    | false =>
      have Hp : prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i+j) = false := by
        rw [Hspec, Heqb]; rfl
      refine ⟨regs4, ?_, ?_, ?_⟩
      · intro r h10 h12 h15 h16
        dsimp only [regs4, regs3, regs2, regs1]
        simp (disch := assumption) only [regupd_other]
      · rw [Hp]; dsimp only [Bool.false_eq_true, ↓reduceIte, regs4, regs3, regs2, regs1]
        regupd_resolve; exact Hr12
      · rw [Hp]
        apply msteps_trans _ _ _ _ Hpre
        dsimp only [regs4, regs3, regs2, regs1]
        chain_step
        · rfl
        · apply step_beq_ft _ _ _ _ _ _ _ _ _ SF_110c0 rfl SD_110c0
          getr_resolve; rw [c_eq_small, bv_eqb_zext]; exact Heqb
        · norm_pc
          chain_step
          · rfl
          · apply step_beq_ft _ _ _ _ _ _ _ _ _ SF_110c4 rfl SD_110c4
            getr_resolve; rw [Hr15, Hr12]
            apply c_eq_neq
            rw [u_ntw _ (by omega), u_ntw _ (by omega)]; omega
          · norm_pc; exact msteps.mst_refl _
    | true =>
      let regs5 := regupd regs4 15 (nat_to_word (j+1))
      have Hnext : msteps source_segs (mkst regs4 0x110c0 mem rrom) (mkst regs5 0x1109c mem rrom) := by
        dsimp only [regs4, regs3, regs2, regs1]
        chain_step
        · rfl
        · apply step_beq_tk _ _ _ _ _ _ _ _ _ SF_110c0 rfl SD_110c0
          getr_resolve; rw [c_eq_small, bv_eqb_zext]; exact Heqb
        · norm_pc
          stepiv SF_11098 SD_11098 (nat_to_word (j+1))
            (getr_resolve; rw [Hr15]; exact v_addi_Sj j (by omega))
          exact msteps.mst_refl _
      by_cases HSj : j+1 = (av.getD 1 []).length
      · let regs6 := regupd regs5 12 (nat_to_word 0)
        have Hp : prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i+j) = true := by
          rw [Hspec, Heqb, List.drop_eq_nil_iff.mpr (by omega)]
          rfl
        refine ⟨regs6, ?_, ?_, ?_⟩
        · intro r h10 h12 h15 h16
          dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
          simp (disch := assumption) only [regupd_other]
        · rw [Hp]; exact regupd_same _ _ _
        · rw [Hp]
          apply msteps_trans _ _ _ _ Hpre
          apply msteps_trans _ _ _ _ Hnext
          dsimp only [regs5, regs4, regs3, regs2, regs1]
          chain_step
          · rfl
          · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_1109c rfl SD_1109c
            getr_resolve; rw [Hr12, HSj, c_eq_small]; exact LinuxProcessSemantics.Common.PropExec.bv_eqb_refl _
          · norm_pc
            stepiv SF_110a0 SD_110a0 (nat_to_word 0) (getr_resolve; bveq)
            stepj SF_110a4 SD_110a4
            exact msteps.mst_refl _
      · have Hr15' : reg_get regs5 15 = nat_to_word (j+1) := regupd_same _ _ _
        have Hr17' : reg_get regs5 17 = cat_argv_ptr rsp av ev k + nat_to_word i := by
          dsimp only [regs5, regs4, regs3, regs2, regs1]; regupd_resolve; exact Hr17
        have Hr19' : reg_get regs5 19 = cat_argv_ptr rsp av ev 1 := by
          dsimp only [regs5, regs4, regs3, regs2, regs1]; regupd_resolve; exact Hr19
        have Hr12' : reg_get regs5 12 = nat_to_word (av.getD 1 []).length := by
          dsimp only [regs5, regs4, regs3, regs2, regs1]; regupd_resolve; exact Hr12
        obtain ⟨regs', Hag, H12, Hms⟩ := IH i (j+1) regs5 (by omega) (by omega) Hin Hr15' Hr17' Hr19' Hr12'
        have Hp : prefix_eqb ((av.getD 1 []).drop j) (av.getD k []) (i+j) =
            prefix_eqb ((av.getD 1 []).drop (j+1)) (av.getD k []) (i+(j+1)) := by
          rw [Hspec, Heqb, Bool.true_and, Nat.add_assoc]
        refine ⟨regs', ?_, ?_, ?_⟩
        · intro r h10 h12 h15 h16
          rw [Hag r h10 h12 h15 h16]
          dsimp only [regs5, regs4, regs3, regs2, regs1]
          simp (disch := assumption) only [regupd_other]
        · rw [Hp]; exact H12
        · rw [Hp]
          apply msteps_trans _ _ _ _ Hpre
          apply msteps_trans _ _ _ _ Hnext
          chain_step
          · rfl
          · apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_1109c rfl SD_1109c
            dsimp only [regs5, regs4, regs3, regs2, regs1]
            getr_resolve; rw [Hr12]
            apply c_eq_neq
            rw [u_ntw _ (by omega), u_ntw _ (by omega)]; omega
          · norm_pc; exact Hms

/- Scan guard: with a nonempty pattern no longer than the haystack, try
positions starting at i. A match clears a2 and reaches the output path;
exhausting the admissible positions reaches the next argument. -/
include Hva Hve Hsp_lo Hsp_hi in
theorem source_scan (k : Nat) (Hk : k < av.length) (H2le : 2 ≤ av.length)
    (mem : word → Option byte) (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (f i : Nat) (regs : bvmap 5 word)
    (Hnn1 : 1 ≤ (av.getD 1 []).length)
    (Hnnhn : (av.getD 1 []).length ≤ (av.getD k []).length)
    (Hif : i + f = ((av.getD k []).length - (av.getD 1 []).length) + 1)
    (Hr13 : reg_get regs 13 = nat_to_word i)
    (Hr14 : reg_get regs 14 = nat_to_word (av.getD k []).length)
    (Hr12 : reg_get regs 12 = nat_to_word (av.getD 1 []).length)
    (Hr11 : reg_get regs 11 = cat_argv_ptr rsp av ev k)
    (Hr19 : reg_get regs 19 = cat_argv_ptr rsp av ev 1) :
    ∃ regs',
      (∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regs' r = reg_get regs r) ∧
      (if scan_from (av.getD k []) (av.getD 1 []) i f
        then reg_get regs' 12 = nat_to_word 0 else True) ∧
      msteps source_segs (mkst regs 0x110cc mem rrom)
        (mkst regs' (if scan_from (av.getD k []) (av.getD 1 []) i f
          then 0x110dc else 0x11080) mem rrom) := by
  have Hhlen := valid_argv_str_len av k Hva Hk
  have Hplen := valid_argv_str_len av 1 Hva (by omega)
  induction f generalizing i regs with
  | zero =>
    let regs1 := regupd regs 15 (nat_to_word (i + (av.getD 1 []).length))
    refine ⟨regs1, ?_, True.intro, ?_⟩
    · intro r h10 h12 h13 h15 h16 h17
      exact regupd_other _ _ _ _ h15
    · simp only [scan_from, Bool.false_eq_true, ↓reduceIte]
      stepiv SF_110cc SD_110cc (nat_to_word (i + (av.getD 1 []).length))
        (getr_resolve; rw [Hr13, Hr12, v_add_ntw])
      chain_step
      · rfl
      · apply step_bgeu_ft _ _ _ _ _ _ _ _ _ SF_110d0 rfl SD_110d0
        getr_resolve; rw [Hr14, c_ltu_ltb]
        apply decide_eq_true
        rw [u_ntw _ (by omega), u_ntw _ (by omega)]; omega
      · norm_pc; stepj SF_110d4 SD_110d4; exact msteps.mst_refl _
  | succ f IH =>
    have Hin : i + (av.getD 1 []).length ≤ (av.getD k []).length := by omega
    let regs1 := regupd regs 15 (nat_to_word (i + (av.getD 1 []).length))
    let regs2 := regupd regs1 15 (nat_to_word 0)
    let regs3 := regupd regs2 17 (cat_argv_ptr rsp av ev k + nat_to_word i)
    have Hpre : msteps source_segs (mkst regs 0x110cc mem rrom) (mkst regs3 0x110b0 mem rrom) := by
      stepiv SF_110cc SD_110cc (nat_to_word (i + (av.getD 1 []).length))
        (getr_resolve; rw [Hr13, Hr12, v_add_ntw])
      chain_step
      · rfl
      · apply step_bgeu_tk _ _ _ _ _ _ _ _ _ SF_110d0 rfl SD_110d0
        getr_resolve; rw [Hr14, c_ltu_ltb]
        apply decide_eq_false
        rw [u_ntw _ (by omega), u_ntw _ (by omega)]; omega
      · norm_pc
        stepiv SF_110a8 SD_110a8 (nat_to_word 0) (getr_resolve; bveq)
        stepiv SF_110ac SD_110ac (cat_argv_ptr rsp av ev k + nat_to_word i)
          (getr_resolve; rw [Hr11, Hr13, LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm])
        exact msteps.mst_refl _
    have Hr15C : reg_get regs3 15 = nat_to_word 0 := by
      dsimp only [regs3, regs2]; regupd_resolve; rfl
    have Hr17C : reg_get regs3 17 = cat_argv_ptr rsp av ev k + nat_to_word i := regupd_same _ _ _
    have Hr19C : reg_get regs3 19 = cat_argv_ptr rsp av ev 1 := by
      dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr19
    have Hr12C : reg_get regs3 12 = nat_to_word (av.getD 1 []).length := by
      dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr12
    obtain ⟨regsC, HagC, H12C, HmsC⟩ := source_cmp av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi
      k Hk H2le mem Hmem i (av.getD 1 []).length 0 regs3 (by omega) Hnn1 Hin Hr15C Hr17C Hr19C Hr12C
    simp only [List.drop_zero, Nat.add_zero] at H12C HmsC
    have HagE : ∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regsC r = reg_get regs r := by
      intro r h10 h12 h13 h15 h16 h17
      rw [HagC r h10 h12 h15 h16]
      dsimp only [regs3, regs2, regs1]
      simp (disch := assumption) only [regupd_other]
    simp only [scan_from]
    by_cases Epre : prefix_eqb (av.getD 1 []) (av.getD k []) i = true
    ·
      simp only [Epre, ↓reduceIte] at H12C HmsC
      simp only [Epre, Bool.true_or, ↓reduceIte]
      exact ⟨regsC, HagE, H12C, msteps_trans _ _ _ _ Hpre HmsC⟩
    · have Efalse := Bool.eq_false_iff.mpr Epre
      simp only [Efalse, Bool.false_eq_true, ↓reduceIte] at H12C HmsC
      simp only [Efalse, Bool.false_or]
      let regsD := regupd regsC 13 (nat_to_word (i+1))
      have Hr13D : reg_get regsD 13 = nat_to_word (i+1) := regupd_same _ _ _
      have Hr14D : reg_get regsD 14 = nat_to_word (av.getD k []).length := by
        dsimp only [regsD]; regupd_resolve
        rw [HagE 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact Hr14
      have Hr12D : reg_get regsD 12 = nat_to_word (av.getD 1 []).length := by
        dsimp only [regsD]; regupd_resolve; exact H12C
      have Hr11D : reg_get regsD 11 = cat_argv_ptr rsp av ev k := by
        dsimp only [regsD]; regupd_resolve
        rw [HagE 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact Hr11
      have Hr19D : reg_get regsD 19 = cat_argv_ptr rsp av ev 1 := by
        dsimp only [regsD]; regupd_resolve
        rw [HagE 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact Hr19
      obtain ⟨regs', Hag', H12', Hms'⟩ := IH (i+1) regsD (by omega) Hr13D Hr14D Hr12D Hr11D Hr19D
      refine ⟨regs', ?_, H12', ?_⟩
      · intro r h10 h12 h13 h15 h16 h17
        rw [Hag' r h10 h12 h13 h15 h16 h17, regupd_other _ _ _ _ h13]
        exact HagE r h10 h12 h13 h15 h16 h17
      · apply msteps_trans _ _ _ _ Hpre
        apply msteps_trans _ _ _ _ HmsC
        stepiv SF_110c8 SD_110c8 (nat_to_word (i+1))
          (getr_resolve
           rw [HagC 13 (by decide) (by decide) (by decide) (by decide)]
           dsimp only [regs3, regs2, regs1]; regupd_resolve
           rw [Hr13]; exact v_addi_Sj i (by omega))
        exact Hms'

/- The newline write spills its length/pointer, calls write, and reloads.
The nonempty prefix of a one-byte buffer is that whole byte, so the loop
rejoins the next-argument path after one call, preserving callee saves. -/
include Hsp_lo Hsp_hi in
theorem source_nl_write (regs : bvmap 5 word) (mem : word → Option byte)
    (bufs : List (List byte)) (code : word)
    (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (Hr20 : reg_get regs 20 = Z_to_bv 64 73728)
    (Hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (Hcont : ∀ regs' mem', mem_ok av ev uid hw rsp rrnd mem' →
      (∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
        r ≠ 15 → r ≠ 16 → r ≠ 17 → reg_get regs' r = reg_get regs r) →
      to_wallexit source_segs (Z_to_bv 64 1) bufs code (mkst regs' 0x11080 mem' rrom)) :
    to_wallexit source_segs (Z_to_bv 64 1) ([Z_to_bv 8 10] :: bufs) code
      (mkst regs 0x110ec mem rrom) := by
  have Hlo := sp_lo_num rsp Hsp_lo
  have Hhi := sp_hi_num rsp Hsp_hi
  constructor
  · decide
  · stepiv SF_110ec SD_110ec (Z_to_bv 64 1) (getr_resolve; bveq)
    stepiv SF_110f0 SD_110f0 (0x12000 : word) (getr_resolve; rw [Hr20]; bveq)
    stepiv SF_110f4 SD_110f4 (Z_to_bv 64 1) (getr_resolve; bveq)
    stepsd SF_110f8 SD_110f8 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (Z_to_bv 64 1)
      (getr_resolve; rfl) (solve_store_ok_inv)
    stepsd SF_110fc SD_110fc (Z_to_bv 64 (bv_unsigned rsp - 0x40)) (0x12000 : word)
      (getr_resolve; rfl) (solve_store_ok_inv)
    stepj SF_11100 SD_11100
    apply source_write_fn av ev uid hw rsp rrnd Hsp_lo Hsp_hi
      (to_wallexit source_segs (Z_to_bv 64 1) bufs code) _ _ [Z_to_bv 8 10] (0x11104 : word)
    · apply mem_ok_scratch8 av ev uid hw rsp rrnd Hsp_hi
      · apply mem_ok_scratch8 av ev uid hw rsp rrnd Hsp_hi
        · exact Hmem
        · ga_u; omega
        · ga_u; omega
      · ga_u; omega
      · ga_u; omega
    · regupd_resolve; rfl
    · regupd_resolve; bveq
    · bveq
    · regupd_resolve; exact Hr2
    · regupd_resolve; decide
    · regupd_resolve; decide
    · regupd_resolve; decide
    · regupd_resolve; right; imm_norm; u_norm; omega
    · regupd_resolve; exact read_newline_f av ev uid hw rsp rrnd Hsp_lo Hsp_hi
    · intro regsB memB kB HkB1 HkB2 HmB HagrB HagB H10B
      have HkB : kB = 1 := by simp only [List.length_cons, List.length_nil] at HkB2; omega
      subst kB
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at H10B ⊢
      change reg_get regsB 10 = Z_to_bv 64 1 at H10B
      have Hr2B : reg_get regsB 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) := by
        rw [HagB 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        regupd_resolve; exact Hr2
      chain_step
      · rfl
      · apply step_bge_ft _ _ _ _ _ _ _ _ _ SF_11104 rfl SD_11104
        getr_resolve; rw [H10B]; decide
      · norm_pc
        stepld SF_11108 SD_11108 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (Z_to_bv 64 1)
          (rw [HagrB _ _ (by ga_u; omega) (Or.inl (by ga_u; omega))]
           rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by ga_u; omega) (by ga_u; omega)]
           exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega))
        stepld SF_1110c SD_1110c (Z_to_bv 64 (bv_unsigned rsp - 0x40)) (0x12000 : word)
          (rw [HagrB _ _ (by ga_u; omega) (Or.inl (by ga_u; omega))]
           exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega))
        stepi SF_11110 SD_11110
        stepi SF_11114 SD_11114
        chain_step
        · rfl
        · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_11118 rfl SD_11118
          getr_resolve; regupd_resolve; rw [H10B]; decide
        · norm_pc
          stepj SF_1111c SD_1111c
          apply to_wall_tail.twt_done
          apply Hcont _ _ HmB
          intro r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17
          simp (disch := assumption) only [regupd_other]
          rw [HagB r Hx10 Hx13 Hx14 Hx15 Hx16 Hx17]
          simp (disch := assumption) only [regupd_other]

/- Retry after a write delivery: reload the spilled pair, advance by n,
and reissue the remainder or continue to newline. The nonempty delivery
makes the error branch unreachable. Spill reads travel separately because
the mem_ok scratch window excludes them. -/
include Hsp_lo Hsp_hi in
theorem source_out_wall (K : machine_state → Prop) (fuel : Nat) (rest : List byte)
    (p : word) (n : Nat) (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 131071)
    (Hplo : bv_unsigned rsp - 0x30 ≤ bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) < 2 ^ 64)
    (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (H10 : reg_get regs 10 = len_word (rest.take n))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (Hs0 : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x40)) 8 = some (word_to_le_bytes 8 p))
    (Hs8 : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = some (word_to_le_bytes 8 (len_word rest)))
    (Hbuf : rdn source_segs fm p rest.length = some rest)
    (Hcont : ∀ regs' mem', mem_ok av ev uid hw rsp rrnd mem' →
      (∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
        r ≠ 15 → r ≠ 16 → r ≠ 17 → reg_get regs' r = reg_get regs r) →
      K (mkst regs' 0x110ec mem' rrom)) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x11130 mem rrom) (rest.drop n) K := by
  induction fuel generalizing rest p n regs mem with
  | zero => omega
  | succ fuel IH =>
    have Hlo := sp_lo_num rsp Hsp_lo
    have Hhi := sp_hi_num rsp Hsp_hi
    have Hup := u64_range p
    have Hsk : rdn source_segs fm (p + nat_to_word n) (rest.drop n).length = some (rest.drop n) := by
      rw [List.length_drop]
      exact LinuxProcessSemantics.Common.SeqExec.rdn_skipn source_segs fm rest.length p rest n Hbuf Hn2
    stepld SF_11130 SD_11130 (Z_to_bv 64 (bv_unsigned rsp - 0x40)) p (exact Hs0)
    stepld SF_11134 SD_11134 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (len_word rest) (exact Hs8)
    chain_step
    · rfl
    · apply step_blt_tk _ _ _ _ _ _ _ _ _ SF_11138 rfl SD_11138
      getr_resolve; rw [H10]
      apply c_lts_0_pos
      · rw [u_len_word_firstn n rest Hn2 (by omega)]; omega
      · rw [u_len_word_firstn n rest Hn2 (by omega)]; omega
    · norm_pc
      stepiv SF_11160 SD_11160 (p + nat_to_word n)
        (getr_resolve; rw [H10]; exact v_add_len_firstn p n rest Hn2)
      stepiv SF_11164 SD_11164 (len_word (rest.drop n))
        (getr_resolve; rw [H10]; exact v_sub_len_firstn n rest Hn2 (by omega))
      stepj SF_11168 SD_11168
      by_cases Hne : n = rest.length
      · subst n
        rw [List.drop_length]
        chain_step
        · rfl
        · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_110e8 rfl SD_110e8
          getr_resolve; apply c_eq_0_of_u; rfl
        · norm_pc
          apply to_wall_tail.twt_done
          apply Hcont _ _ Hmem
          intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
          simp (disch := assumption) only [regupd_other]
      · have Hupn : bv_unsigned (p + nat_to_word n) = bv_unsigned p + (n : Int) := by
          rw [word_add_nat]; exact u_Z2bv _ (by omega) (by omega)
        have Hremain : bv_unsigned (len_word (rest.drop n)) = ((rest.drop n).length : Int) :=
          u_len_word _ (by rw [List.length_drop]; omega)
        chain_step
        · rfl
        · apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_110e8 rfl SD_110e8
          getr_resolve; apply c_eq_0_false
          rw [Hremain, List.length_drop]; omega
        · norm_pc
          stepiv SF_11120 SD_11120 (Z_to_bv 64 1) (getr_resolve; bveq)
          stepsd SF_11124 SD_11124 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (len_word (rest.drop n))
            (getr_resolve; rfl) (solve_store_ok_inv)
          stepsd SF_11128 SD_11128 (Z_to_bv 64 (bv_unsigned rsp - 0x40)) (p + nat_to_word n)
            (getr_resolve; rfl) (solve_store_ok_inv)
          stepj SF_1112c SD_1112c
          apply source_write_fn av ev uid hw rsp rrnd Hsp_lo Hsp_hi K _ _ (rest.drop n) (0x11130 : word)
          · apply mem_ok_scratch8 av ev uid hw rsp rrnd Hsp_hi
            · apply mem_ok_scratch8 av ev uid hw rsp rrnd Hsp_hi
              · exact Hmem
              · ga_u; omega
              · ga_u; omega
            · ga_u; omega
            · ga_u; omega
          · regupd_resolve; rfl
          · regupd_resolve; bveq
          · bveq
          · regupd_resolve; exact H2
          · regupd_resolve; rw [Hremain, List.length_drop]; omega
          · regupd_resolve; rw [Hremain, List.length_drop]; omega
          · regupd_resolve; rw [Hremain, Hupn, List.length_drop]; omega
          · regupd_resolve; left; rw [Hupn]; omega
          · regupd_resolve
            rw [len_word_nat, word_to_nat_ntw _ (by rw [List.length_drop]; omega)]
            exact Hsk
          · intro regsB memB m Hm1 Hm2 HmB HagrB HagB H10B
            apply IH (rest.drop n) (p + nat_to_word n) m regsB memB
            · rw [List.length_drop]; omega
            · exact Hm1
            · exact Hm2
            · rw [List.length_drop]; omega
            · rw [Hupn]; omega
            · rw [Hupn, List.length_drop]; omega
            · exact HmB
            · exact H10B
            · rw [HagB 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
              regupd_resolve; exact H2
            · rw [HagrB _ _ (by ga_u; omega) (Or.inl (by ga_u; omega))]
              exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega)
            · rw [HagrB _ _ (by ga_u; omega) (Or.inl (by ga_u; omega))]
              rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by ga_u; omega) (by ga_u; omega)]
              exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega)
            · exact Hsk
            · intro regsC memC HmC HagC
              apply Hcont _ _ HmC
              intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
              rw [HagC r h1 h10 h11 h12 h13 h14 h15 h16 h17,
                HagB r h10 h13 h14 h15 h16 h17]
              simp (disch := assumption) only [regupd_other]

/- A matched argument: recompute its length, write it unless empty, write
the newline, and rejoin the next-argument path. The callee saves and sp survive. -/
include Hva Hve Hsp_lo Hsp_hi in
theorem source_output (i : Nat) (regs : bvmap 5 word) (mem : word → Option byte)
    (bufs : List (List byte)) (code : word)
    (Hmem : mem_ok av ev uid hw rsp rrnd mem) (Hi : i < av.length)
    (Hr11 : reg_get regs 11 = cat_argv_ptr rsp av ev i)
    (Hr12 : reg_get regs 12 = nat_to_word 0)
    (Hr20 : reg_get regs 20 = Z_to_bv 64 73728)
    (Hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (Hcont : ∀ regs' mem', mem_ok av ev uid hw rsp rrnd mem' →
      (∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
        r ≠ 15 → r ≠ 16 → r ≠ 17 → reg_get regs' r = reg_get regs r) →
      to_wallexit source_segs (Z_to_bv 64 1) bufs code (mkst regs' 0x11080 mem' rrom)) :
    to_wallexit source_segs (Z_to_bv 64 1)
      ((match av.getD i [] with
        | [] => [[Z_to_bv 8 10]]
        | _ => [av.getD i [], [Z_to_bv 8 10]]) ++ bufs) code
      (mkst regs 0x110dc mem rrom) := by
  have Hlo := sp_lo_num rsp Hsp_lo
  have Hhi := sp_hi_num rsp Hsp_hi
  obtain ⟨Hge, Hlt⟩ := argv_ptr_bounds_at rsp av ev Hva Hve Hsp_hi i Hi
  have Hslen := valid_argv_str_len av i Hva Hi
  obtain ⟨regsL, HagL, Hr12L, HmsL⟩ := source_slen_out av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi
    i Hi mem Hmem (av.getD i []).length 0 regs (by omega) Hr11 Hr12
  apply msteps_to_wallexit _ _ _ _ _ _ HmsL
  have Hr2L : reg_get regsL 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) := by
    rw [HagL 2 (by decide) (by decide)]; exact Hr2
  have Hr11L : reg_get regsL 11 = cat_argv_ptr rsp av ev i := by
    rw [HagL 11 (by decide) (by decide)]; exact Hr11
  have Hr20L : reg_get regsL 20 = Z_to_bv 64 73728 := by
    rw [HagL 20 (by decide) (by decide)]; exact Hr20
  by_cases Ea : av.getD i [] = []
  · simp only [Ea, List.nil_append, List.cons_append]
    rw [Ea] at Hr12L
    chain_step
    · rfl
    · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_110e8 rfl SD_110e8
      getr_resolve; rw [Hr12L]; apply c_eq_0_of_u; rfl
    · norm_pc
      apply source_nl_write av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ _ _ _ Hmem Hr20L Hr2L
      intro regsF memF HmF HagF
      apply Hcont _ _ HmF
      intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
      rw [HagF r h1 h10 h11 h12 h13 h14 h15 h16 h17]
      exact HagL r h12 h15
  · have Hnn : 1 ≤ (av.getD i []).length := List.length_pos_iff.mpr Ea
    have Hshape : (match av.getD i [] with
        | [] => [[Z_to_bv 8 10]]
        | _ => [av.getD i [], [Z_to_bv 8 10]]) = [av.getD i [], [Z_to_bv 8 10]] := by
      cases h : av.getD i [] with
      | nil => exact False.elim (Ea h)
      | cons b bs => rfl
    rw [Hshape]
    simp only [List.cons_append, List.nil_append]
    chain_step
    · rfl
    · apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_110e8 rfl SD_110e8
      getr_resolve; rw [Hr12L]; apply c_eq_0_false
      rw [u_ntw _ (by omega)]; omega
    · norm_pc
      stepiv SF_11120 SD_11120 (Z_to_bv 64 1) (getr_resolve; bveq)
      stepsd SF_11124 SD_11124 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (nat_to_word (av.getD i []).length)
        (getr_resolve; exact Hr12L) (solve_store_ok_inv)
      stepsd SF_11128 SD_11128 (Z_to_bv 64 (bv_unsigned rsp - 0x40)) (cat_argv_ptr rsp av ev i)
        (getr_resolve; exact Hr11L) (solve_store_ok_inv)
      stepj SF_1112c SD_1112c
      constructor
      · exact Hnn
      · apply source_write_fn av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ _ _ (av.getD i []) (0x11130 : word)
        · apply mem_ok_scratch8 av ev uid hw rsp rrnd Hsp_hi
          · apply mem_ok_scratch8 av ev uid hw rsp rrnd Hsp_hi
            · exact Hmem
            · ga_u; omega
            · ga_u; omega
          · ga_u; omega
          · ga_u; omega
        · regupd_resolve; rfl
        · regupd_resolve; bveq
        · bveq
        · regupd_resolve; exact Hr2L
        · regupd_resolve; rw [Hr12L, u_ntw _ (by omega)]; omega
        · regupd_resolve; rw [Hr12L, u_ntw _ (by omega)]; omega
        · regupd_resolve; rw [Hr11L, Hr12L, u_ntw _ (by omega)]; omega
        · regupd_resolve; left; rw [Hr11L]; omega
        · regupd_resolve; rw [Hr11L, Hr12L, word_to_nat_ntw _ (by omega)]
          exact read_str_f av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi i Hi
        · intro regsA memA kA HkA1 HkA2 HmA HagrA HagA H10A
          apply source_out_wall av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ (av.getD i []).length
            (av.getD i []) (cat_argv_ptr rsp av ev i) kA regsA memA
          · omega
          · exact HkA1
          · exact HkA2
          · exact Hslen
          · omega
          · omega
          · exact HmA
          · exact H10A
          · rw [HagA 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            regupd_resolve; exact Hr2L
          · rw [HagrA _ _ (by ga_u; omega) (Or.inl (by ga_u; omega))]
            exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega)
          · rw [HagrA _ _ (by ga_u; omega) (Or.inl (by ga_u; omega))]
            rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by ga_u; omega) (by ga_u; omega)]
            exact rdn_wbytes_hit8 _ _ _ _ (by ga_u; omega)
          · exact read_str_f av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi i Hi
          · intro regsF memF HmF HagF
            apply source_nl_write av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ _ _ _ HmF
            · simp (disch := decide) only [HagF, HagA, regupd_other]
              exact Hr20L
            · simp (disch := decide) only [HagF, HagA, regupd_other]
              exact Hr2L
            · intro regsG memG HmG HagG
              apply Hcont _ _ HmG
              intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
              simp (disch := assumption) only [HagG, HagF, HagA, regupd_other]
              exact HagL r h12 h15

/- One argument, from the outer loop head through its optional output and
back to the loop head with the next index. -/
include Hva Hve Hsp_lo Hsp_hi in
theorem source_arg (i : Nat) (regs : bvmap 5 word) (mem : word → Option byte)
    (bufs : List (List byte)) (code : word)
    (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (H2le : 2 ≤ av.length) (H2i : 2 ≤ i) (Hi : i < av.length)
    (Hr8 : reg_get regs 8 = argcN av) (Hr9 : reg_get regs 9 = nat_to_word i)
    (Hr18 : reg_get regs 18 = Z_to_bv 64 (bv_unsigned rsp + 8))
    (Hr19 : reg_get regs 19 = cat_argv_ptr rsp av ev 1)
    (Hr20 : reg_get regs 20 = Z_to_bv 64 73728)
    (Hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (Hcont : ∀ regs' mem', mem_ok av ev uid hw rsp rrnd mem' →
      reg_get regs' 8 = argcN av → reg_get regs' 9 = nat_to_word (i+1) →
      reg_get regs' 18 = Z_to_bv 64 (bv_unsigned rsp + 8) →
      reg_get regs' 19 = cat_argv_ptr rsp av ev 1 →
      reg_get regs' 20 = Z_to_bv 64 73728 →
      reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) →
      to_wallexit source_segs (Z_to_bv 64 1) bufs code (mkst regs' 0x11038 mem' rrom)) :
    to_wallexit source_segs (Z_to_bv 64 1) (arg_bufs (av.getD 1 []) (av.getD i []) ++ bufs) code
      (mkst regs 0x11038 mem rrom) := by
  have Hargc := valid_argv_len av Hva
  have Hhlen := valid_argv_str_len av i Hva Hi
  have Hplen := valid_argv_str_len av 1 Hva (by omega)
  have Hlo := sp_lo_num rsp Hsp_lo
  have Hhi := sp_hi_num rsp Hsp_hi
  have HuA := u_argcN av Hva
  have HiN : (i : Int) ≤ 1024 := by omega
  have Htail : ∀ regsT memT, reg_get regsT 9 = nat_to_word i →
      msteps source_segs (mkst regsT 0x11080 memT rrom)
        (mkst (regupd regsT 9 (nat_to_word (i+1))) 0x11038 memT rrom) := by
    intro regsT memT HrT
    stepiv SF_11080 SD_11080 (nat_to_word (i+1))
      (getr_resolve; rw [HrT]; exact v_addi_Sj i (by omega))
    stepj SF_11084 SD_11084
    exact msteps.mst_refl _
  let regs1 := regupd regs 15 (nat_to_word i)
  let regs2 := regupd regs1 15 (Z_to_bv 64 (8 * (i : Int)))
  let regs3 := regupd regs2 15 (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (i : Int)))
  let regs4 := regupd regs3 11 (cat_argv_ptr rsp av ev i)
  let regs5 := regupd regs4 14 (nat_to_word 0)
  have Hr11_5 : reg_get regs5 11 = cat_argv_ptr rsp av ev i := by
    dsimp only [regs5, regs4]; regupd_resolve; rfl
  have Hr14_5 : reg_get regs5 14 = nat_to_word 0 := regupd_same _ _ _
  obtain ⟨regsH, HagH, Hr14H, HmsH⟩ := source_slen_hay av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi
    i Hi mem Hmem (av.getD i []).length 0 regs5 (by omega) Hr11_5 Hr14_5
  have HrH : ∀ r : reg, r ≠ 11 → r ≠ 14 → r ≠ 15 → reg_get regsH r = reg_get regs r := by
    intro r h11 h14 h15
    rw [HagH r h14 h15]
    dsimp only [regs5, regs4, regs3, regs2, regs1]
    simp (disch := assumption) only [regupd_other]
  have Hr11H : reg_get regsH 11 = cat_argv_ptr rsp av ev i := by
    rw [HagH 11 (by decide) (by decide)]; exact Hr11_5
  let regs6 := regupd regsH 12 (nat_to_word 0)
  have Hr19_6 : reg_get regs6 19 = cat_argv_ptr rsp av ev 1 := by
    dsimp only [regs6]; regupd_resolve
    rw [HrH 19 (by decide) (by decide) (by decide)]; exact Hr19
  have Hr12_6 : reg_get regs6 12 = nat_to_word 0 := regupd_same _ _ _
  obtain ⟨regsP, HagP, Hr12P, HmsP⟩ := source_slen_pat av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi
    H2le mem Hmem (av.getD 1 []).length 0 regs6 (by omega) Hr19_6 Hr12_6
  have HrP : ∀ r : reg, r ≠ 11 → r ≠ 12 → r ≠ 14 → r ≠ 15 →
      reg_get regsP r = reg_get regs r := by
    intro r h11 h12 h14 h15
    rw [HagP r h12 h15, regupd_other _ _ _ _ h12]
    exact HrH r h11 h14 h15
  have Hr11P : reg_get regsP 11 = cat_argv_ptr rsp av ev i := by
    rw [HagP 11 (by decide) (by decide)]
    dsimp only [regs6]; regupd_resolve; exact Hr11H
  have Hr14P : reg_get regsP 14 = nat_to_word (av.getD i []).length := by
    rw [HagP 14 (by decide) (by decide)]
    dsimp only [regs6]; regupd_resolve; exact Hr14H
  have Hr19P : reg_get regsP 19 = cat_argv_ptr rsp av ev 1 := by
    rw [HrP 19 (by decide) (by decide) (by decide) (by decide)]; exact Hr19
  have Hr20P : reg_get regsP 20 = Z_to_bv 64 73728 := by
    rw [HrP 20 (by decide) (by decide) (by decide) (by decide)]; exact Hr20
  have Hr2P : reg_get regsP 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) := by
    rw [HrP 2 (by decide) (by decide) (by decide) (by decide)]; exact Hr2
  have HmsPre : msteps source_segs (mkst regs 0x11038 mem rrom) (mkst regsP 0x11074 mem rrom) := by
    stepiwv SF_11038 SD_11038 (nat_to_word i)
      (getr_resolve; rw [Hr9]; exact v_addiw_id _ (by rw [u_ntw _ (by omega)]; omega))
    chain_step
    · rfl
    · apply step_blt_tk _ _ _ _ _ _ _ _ _ SF_1103c rfl SD_1103c
      getr_resolve; rw [Hr8]
      rw [c_lts_small _ _ (by rw [u_ntw _ (by omega)]; omega) (by omega)]
      rw [LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
      apply decide_eq_true; rw [u_ntw _ (by omega), HuA]; omega
    · norm_pc
      stepiv SF_11048 SD_11048 (Z_to_bv 64 (8 * (i : Int)))
        (getr_resolve; rw [Hr9]; exact v_slli3_nat i HiN)
      stepiv SF_1104c SD_1104c (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (i : Int)))
        (getr_resolve; rw [Hr18]; apply bv_eq_of_unsigned
         rw [v_add_small _ _ (by ga_u; omega)]; ga_u)
      stepld SF_11050 SD_11050 (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (i : Int)))
        (cat_argv_ptr rsp av ev i)
        (exact read_ptr_m av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem i Hi)
      stepiv SF_11054 SD_11054 (nat_to_word 0) (getr_resolve; bveq)
      apply msteps_trans _ _ _ _ HmsH
      stepiv SF_11064 SD_11064 (nat_to_word 0) (getr_resolve; bveq)
      exact HmsP
  have Hout : ∀ regsO memO, mem_ok av ev uid hw rsp rrnd memO →
      (∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
        r ≠ 15 → r ≠ 16 → r ≠ 17 → reg_get regsO r = reg_get regs r) →
      to_wallexit source_segs (Z_to_bv 64 1) bufs code (mkst regsO 0x11080 memO rrom) := by
    intro regsO memO HmO HagO
    apply msteps_to_wallexit _ _ _ _ _ _ (Htail regsO memO (by
      simp (disch := decide) only [HagO]; exact Hr9))
    apply Hcont _ _ HmO
    · regupd_resolve; simp (disch := decide) only [HagO]; exact Hr8
    · exact regupd_same _ _ _
    · regupd_resolve; simp (disch := decide) only [HagO]; exact Hr18
    · regupd_resolve; simp (disch := decide) only [HagO]; exact Hr19
    · regupd_resolve; simp (disch := decide) only [HagO]; exact Hr20
    · regupd_resolve; simp (disch := decide) only [HagO]; exact Hr2
  apply msteps_to_wallexit _ _ _ _ _ _ HmsPre
  by_cases Hnn0 : (av.getD 1 []).length = 0
  · have Hcont_b : contains_b (av.getD i []) (av.getD 1 []) = true := by
      simp only [contains_b, Hnn0, ↓reduceIte]
    simp only [arg_bufs, Hcont_b, ↓reduceIte]
    chain_step
    · rfl
    · apply step_beq_tk _ _ _ _ _ _ _ _ _ SF_11074 rfl SD_11074
      getr_resolve; rw [Hr12P, Hnn0]; apply c_eq_0_of_u; rfl
    · norm_pc
      apply source_output av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi i regsP mem bufs code
        Hmem Hi Hr11P (by rw [Hr12P, Hnn0]) Hr20P Hr2P
      intro regsF memF HmF HagF
      apply Hout _ _ HmF
      intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
      rw [HagF r h1 h10 h11 h12 h13 h14 h15 h16 h17]
      exact HrP r h11 h12 h14 h15
  · have Hnn1 : 1 ≤ (av.getD 1 []).length := by omega
    chain_step
    · rfl
    · apply step_beq_ft _ _ _ _ _ _ _ _ _ SF_11074 rfl SD_11074
      getr_resolve; rw [Hr12P]; apply c_eq_0_false
      rw [u_ntw _ (by omega)]; omega
    · norm_pc
      stepiv SF_11078 SD_11078 (nat_to_word 0) (getr_resolve; bveq)
      let regsA := regupd regsP 13 (nat_to_word 0)
      by_cases Hle : (av.getD 1 []).length ≤ (av.getD i []).length
      · have Hcont_b : contains_b (av.getD i []) (av.getD 1 []) =
            scan_from (av.getD i []) (av.getD 1 []) 0 ((av.getD i []).length - (av.getD 1 []).length + 1) := by
          simp only [contains_b, ite_eq_right Hnn0, ite_eq_right (by omega : ¬ (av.getD i []).length < (av.getD 1 []).length)]
        chain_step
        · rfl
        · apply step_bgeu_tk _ _ _ _ _ _ _ _ _ SF_1107c rfl SD_1107c
          getr_resolve; rw [Hr14P, Hr12P, c_ltu_ltb]
          apply decide_eq_false
          rw [u_ntw _ (by omega), u_ntw _ (by omega)]; omega
        · norm_pc
          obtain ⟨regsS, HagS, H12S, HmsS⟩ := source_scan av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi
            i Hi H2le mem Hmem ((av.getD i []).length - (av.getD 1 []).length + 1) 0 regsA Hnn1 Hle (by omega)
            (regupd_same _ _ _)
            (by dsimp only [regsA]; regupd_resolve; exact Hr14P)
            (by dsimp only [regsA]; regupd_resolve; exact Hr12P)
            (by dsimp only [regsA]; regupd_resolve; exact Hr11P)
            (by dsimp only [regsA]; regupd_resolve; exact Hr19P)
          have HrS : ∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
              r ≠ 15 → r ≠ 16 → r ≠ 17 → reg_get regsS r = reg_get regs r := by
            intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
            rw [HagS r h10 h12 h13 h15 h16 h17, regupd_other _ _ _ _ h13]
            exact HrP r h11 h12 h14 h15
          simp only [arg_bufs, Hcont_b]
          by_cases Esc : scan_from (av.getD i []) (av.getD 1 []) 0
              ((av.getD i []).length - (av.getD 1 []).length + 1) = true
          · simp only [Esc, ↓reduceIte] at H12S HmsS ⊢
            apply msteps_to_wallexit _ _ _ _ _ _ HmsS
            apply source_output av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi i regsS mem bufs code Hmem Hi
            · simp (disch := decide) only [HagS]; dsimp only [regsA]; regupd_resolve; exact Hr11P
            · exact H12S
            · simp (disch := decide) only [HrS]; exact Hr20
            · simp (disch := decide) only [HrS]; exact Hr2
            · intro regsF memF HmF HagF
              apply Hout _ _ HmF
              intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
              rw [HagF r h1 h10 h11 h12 h13 h14 h15 h16 h17]
              exact HrS r h1 h10 h11 h12 h13 h14 h15 h16 h17
          · simp only [ite_eq_right Esc, List.nil_append] at HmsS ⊢
            apply msteps_to_wallexit _ _ _ _ _ _ HmsS
            exact Hout regsS mem Hmem HrS
      · have Hcont_b : contains_b (av.getD i []) (av.getD 1 []) = false := by
          simp only [contains_b, ite_eq_right Hnn0, ite_eq_left (by omega : (av.getD i []).length < (av.getD 1 []).length)]
        simp only [arg_bufs, Hcont_b, Bool.false_eq_true, ↓reduceIte, List.nil_append]
        chain_step
        · rfl
        · apply step_bgeu_ft _ _ _ _ _ _ _ _ _ SF_1107c rfl SD_1107c
          getr_resolve; rw [Hr14P, Hr12P, c_ltu_ltb]
          apply decide_eq_true
          rw [u_ntw _ (by omega), u_ntw _ (by omega)]; omega
        · norm_pc
          apply Hout _ _ Hmem
          intro r h1 h10 h11 h12 h13 h14 h15 h16 h17
          rw [regupd_other _ _ _ _ h13]
          exact HrP r h11 h12 h14 h15

/-- A small nonnegative index survives sext.w. Rocq needed the v_lw
spelling left by the reflective block; Lean reuses v_addiw_id after unfolding. -/
theorem v_lw_ntw (n : Nat) (Hn : (n : Int) < 2 ^ 31) :
    v_lw (nat_to_word n) = nat_to_word n := by
  have h := v_addiw_id (nat_to_word n) (by rw [u_ntw _ (by omega)]; exact Hn)
  simpa only [v_lw, v_addiw, Int.add_zero] using h

include Hva Hve Hsp_lo Hsp_hi in
theorem source_loop (m i : Nat) (regs : bvmap 5 word) (mem : word → Option byte)
    (Hmem : mem_ok av ev uid hw rsp rrnd mem)
    (H2le : 2 ≤ av.length) (H2i : 2 ≤ i) (Him : i + m = av.length)
    (Hr8 : reg_get regs 8 = argcN av) (Hr9 : reg_get regs 9 = nat_to_word i)
    (Hr18 : reg_get regs 18 = Z_to_bv 64 (bv_unsigned rsp + 8))
    (Hr19 : reg_get regs 19 = cat_argv_ptr rsp av ev 1)
    (Hr20 : reg_get regs 20 = Z_to_bv 64 73728)
    (Hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40)) :
    to_wallexit source_segs (Z_to_bv 64 1) (grep_bufs (av.getD 1 []) (av.drop i))
      (Z_to_bv 64 0) (mkst regs 0x11038 mem rrom) := by
  induction m generalizing i regs mem with
  | zero =>
    have Hi : i = av.length := by omega
    rw [List.drop_eq_nil_iff.mpr (by omega)]
    simp only [grep_bufs, List.flatMap_nil]
    have Hargc := valid_argv_len av Hva
    have HuA := u_argcN av Hva
    stepiwv SF_11038 SD_11038 (nat_to_word i)
      (getr_resolve; rw [Hr9]; exact v_addiw_id _ (by rw [u_ntw _ (by omega)]; omega))
    chain_step
    · rfl
    · apply step_blt_ft _ _ _ _ _ _ _ _ _ SF_1103c rfl SD_1103c
      getr_resolve; rw [Hr8]
      rw [c_lts_small _ _ (by rw [u_ntw _ (by omega)]; omega) (by omega),
        LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
      apply decide_eq_false; rw [u_ntw _ (by omega), HuA]; omega
    · norm_pc
      stepiv SF_11040 SD_11040 (Z_to_bv 64 0) (getr_resolve; bveq)
      stepj SF_11044 SD_11044
      apply source_epilogue av ev uid hw rsp rrnd Hsp_lo Hsp_hi _ mem (Z_to_bv 64 0) Hmem
      · regupd_resolve; exact Hr2
      · regupd_resolve; rfl
      · decide
  | succ m IH =>
    have Hi : i < av.length := by omega
    rw [skipn_nth av i [] Hi]
    simp only [grep_bufs, List.flatMap_cons]
    apply source_arg av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi i regs mem _ (Z_to_bv 64 0)
      Hmem H2le H2i Hi Hr8 Hr9 Hr18 Hr19 Hr20 Hr2
    intro regs' mem' Hm' H8' H9' H18' H19' H20' H2'
    exact IH (i+1) regs' mem' Hm' (by omega) (by omega) H8' H9' H18' H19' H20' H2'

/- Rocq s_read_argc is replaced by ArgvEnv.read_argc_w at the entry ld. -/
include Hva Hsp_lo Hsp_hi in
/-- The reflective executor's alu64/v_sll spelling of the environ pointer;
alu_add turns it back into the ArgvEnv spelling. -/
theorem envp_ptr_alu :
    Z_to_bv 64 (bv_unsigned (alu64 .ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (argcN av) (Z_to_bv 64 3))) + 8) = envp_ptr rsp av := by
  rw [alu_add]
  exact envp_ptr_eq rsp av Hva Hsp_lo Hsp_hi

include Hva Hve Hsp_lo Hsp_hi in
/-- Program entry, argc ≥ 2. _start reads argc, publishes environ and calls
main. The six frame stores and the argv[1] load leave precisely fmem at the
outer loop head. The five saved callee registers start at zero. Rocq's
25-instruction sym_block is stepped explicitly with StepTac. -/
theorem source_wexit_ge2 (H2le : 2 ≤ av.length) :
    to_wallexit source_segs (Z_to_bv 64 1)
      (grep_bufs (av.getD 1 []) (av.drop 2)) (Z_to_bv 64 0)
      (init_machine_state source_segs 0x11174 source_phdrs rsp rrnd av ev uid hw) := by
  have Hargc := valid_argv_len av Hva
  have HuA := u_argcN av Hva
  have Hlo := sp_lo_num rsp Hsp_lo
  have Hhi := sp_hi_num rsp Hsp_hi
  rw [init_mkst]
  norm_pc
  stepi SF_11174 SD_11174
  stepiv SF_11178 SD_11178 (0x13800 : word) (getr_resolve; bveq)
  stepld SF_1117c SD_1117c rsp (argcN av)
    (exact read_argc_w source_segs source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi)
  stepiv SF_11180 SD_11180 (Z_to_bv 64 (bv_unsigned rsp + 8)) (getr_resolve; rfl)
  stepiv SF_11184 SD_11184 (v_slli (argcN av) 3) (getr_resolve; rfl)
  stepiv SF_11188 SD_11188 (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3))
    (getr_resolve; rfl)
  stepiv SF_1118c SD_1118c (envp_ptr rsp av)
    (getr_resolve; exact envp_ptr_eq rsp av Hva Hsp_lo Hsp_hi)
  stepi SF_11190 SD_11190
  stepiv SF_11194 SD_11194 (0x13000 : word) (getr_resolve; bveq)
  stepsd SF_11198 SD_11198 (0x13000 : word) (envp_ptr rsp av)
    (getr_resolve; rfl) (apply source_store_ok <;> decide)
  stepj SF_1119c SD_1119c
  stepiv SF_11000 SD_11000 (Z_to_bv 64 1) (getr_resolve; bveq)
  chain_step
  · rfl
  · apply step_bge_ft _ _ _ _ _ _ _ _ _ SF_11004 rfl SD_11004
    getr_resolve
    rw [c_lts_small _ _ (by decide) (by omega), LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
    apply decide_eq_true
    rw [HuA]; change (1 : Int) < (av.length : Int); omega
  · norm_pc
    stepiv SF_11008 SD_11008 (Z_to_bv 64 (bv_unsigned rsp - 0x40)) (getr_resolve; rfl)
    stepsd SF_1100c SD_1100c (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (Z_to_bv 64 0)
      (getr_resolve; rfl) (solve_store_ok)
    stepsd SF_11010 SD_11010 (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (Z_to_bv 64 0)
      (getr_resolve; rfl) (solve_store_ok)
    stepsd SF_11014 SD_11014 (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (Z_to_bv 64 0)
      (getr_resolve; rfl) (solve_store_ok)
    stepsd SF_11018 SD_11018 (Z_to_bv 64 (bv_unsigned rsp - 0x30)) (Z_to_bv 64 0)
      (getr_resolve; rfl) (solve_store_ok)
    stepsd SF_1101c SD_1101c (Z_to_bv 64 (bv_unsigned rsp - 8)) (0x111a0 : word)
      (getr_resolve; rfl) (solve_store_ok)
    stepsd SF_11020 SD_11020 (Z_to_bv 64 (bv_unsigned rsp - 0x28)) (Z_to_bv 64 0)
      (getr_resolve; rfl) (solve_store_ok)
    stepld SF_11024 SD_11024 (Z_to_bv 64 (bv_unsigned rsp + 16)) (cat_argv_ptr rsp av ev 1)
      (exact read_ptr_f av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi 1 (by omega))
    stepiv SF_11028 SD_11028 (Z_to_bv 64 (bv_unsigned rsp + 8)) (getr_resolve; apply v_addi_0)
    stepiv SF_1102c SD_1102c (argcN av) (getr_resolve; apply v_addi_0)
    stepiv SF_11030 SD_11030 (nat_to_word 2) (getr_resolve; bveq)
    stepiv SF_11034 SD_11034 (0x12000 : word) (getr_resolve; bveq)
    apply source_loop av ev uid hw Hva Hve rsp rrnd Hsp_lo Hsp_hi (av.length - 2) 2
    · exact fmem_ok av ev uid hw rsp rrnd
    · exact H2le
    · omega
    · omega
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl
    · regupd_resolve; rfl

/- Keep the return-and-exit suffix abstract over the startup state: elaborating
it inside source_wexit_lt2 exceeded the default 200000 heartbeats. -/
private theorem ga_return_lt2 (regs : bvmap 5 word) (mem : word → Option byte)
    (H1 : reg_get regs 1 = (0x111a0 : word)) :
    to_wallexit source_segs (Z_to_bv 64 1) [] (Z_to_bv 64 2)
      (mkst regs 0x1116c mem rrom) := by
  stepiv SF_1116c SD_1116c (Z_to_bv 64 2) (getr_resolve; bveq)
  stepjr SF_11170 SD_11170 (0x111a0 : word) (getr_resolve; regupd_resolve; exact H1)
  stepi SF_111a0 SD_111a0
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ SF_111a4 rfl
  · apply tw_exit_coden
    · getr_resolve; regupd_resolve; rfl
    · getr_resolve; regupd_resolve; rfl
    · decide

include Hva Hve Hsp_lo Hsp_hi in
/-- Program entry, argc < 2: exit 2 without output. _start reads argc,
publishes environ and calls main; main takes bge because argc ≤ 1, returns
2 immediately, then exits. Rocq's 18-instruction sym_block is stepped
explicitly to the exit ecall. -/
theorem source_wexit_lt2 (Hlt2 : av.length < 2) :
    to_wallexit source_segs (Z_to_bv 64 1) [] (Z_to_bv 64 2)
      (init_machine_state source_segs 0x11174 source_phdrs rsp rrnd av ev uid hw) := by
  have Hargc := valid_argv_len av Hva
  have HuA := u_argcN av Hva
  have Hlo := sp_lo_num rsp Hsp_lo
  have Hhi := sp_hi_num rsp Hsp_hi
  rw [init_mkst]
  norm_pc
  stepi SF_11174 SD_11174
  stepiv SF_11178 SD_11178 (0x13800 : word) (getr_resolve; bveq)
  stepld SF_1117c SD_1117c rsp (argcN av)
    (exact read_argc_w source_segs source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi)
  stepiv SF_11180 SD_11180 (Z_to_bv 64 (bv_unsigned rsp + 8)) (getr_resolve; rfl)
  stepiv SF_11184 SD_11184 (v_slli (argcN av) 3) (getr_resolve; rfl)
  stepiv SF_11188 SD_11188 (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3))
    (getr_resolve; rfl)
  stepiv SF_1118c SD_1118c (envp_ptr rsp av)
    (getr_resolve; exact envp_ptr_eq rsp av Hva Hsp_lo Hsp_hi)
  stepi SF_11190 SD_11190
  stepiv SF_11194 SD_11194 (0x13000 : word) (getr_resolve; bveq)
  stepsd SF_11198 SD_11198 (0x13000 : word) (envp_ptr rsp av)
    (getr_resolve; rfl) (apply source_store_ok <;> decide)
  stepj SF_1119c SD_1119c
  stepiv SF_11000 SD_11000 (Z_to_bv 64 1) (getr_resolve; bveq)
  chain_step
  · rfl
  · apply step_bge_tk _ _ _ _ _ _ _ _ _ SF_11004 rfl SD_11004
    getr_resolve
    rw [c_lts_small _ _ (by decide) (by omega), LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
    apply decide_eq_false
    rw [HuA]; change ¬ (1 : Int) < (av.length : Int); omega
  · norm_pc
    apply ga_return_lt2
    regupd_resolve; bveq

end SourceProof
end LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_source
