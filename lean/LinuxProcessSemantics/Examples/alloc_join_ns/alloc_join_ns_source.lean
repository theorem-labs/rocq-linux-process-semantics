import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.AllocSim
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.AllocSim2
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.ListFacts
import LinuxProcessSemantics.Common.MuslStrlen
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.SymExec
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_code
import LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_defs
import LinuxProcessSemantics.Examples.alloc_join_ns.SourceMemImage
import LinuxProcessSemantics.Examples.alloc_join_ns.TargetMemImage

/-! rocq-baseline: b89fd3aefa642f07b01c02ead422e3cebfce5549 -/

/-! # alloc-join-ns source binary: per-binary derivations

PROOF-SIDE FILE (not part of the trusted specification).

Deliverables (Rocq's `SourceProof`, generic over av/ev and the ASLR window sp):
- `source_wexit_lt2`: argc < 2 → to_wexit [] 2
- `source_wexit_cap`: argc ≥ 2, tot > 65536 → to_wexit [] 3
- `source_outcomes`: argc ≥ 2, tot ≤ 65536 →
  to_outcomes (init) (init_model) (two_outcomes [] 4 [jout av] 0).

gcc 15 / musl 1.2.6 binary: argument lengths are measured by an out-of-line
call to musl's word-at-a-time `strlen` (the gcc 9 build inlined the C `slen`
byte loop). The `Int`-level exactness of musl's has-zero test and readability
of the NUL-straddling word load live in Common.MuslStrlen; the per-instruction
walk over the routine (0x111e8..0x11260) is below, pinned to this binary's addresses.

Conventions: sp-relative values use the canonical
`Z_to_bv 64 (bv_unsigned rsp - k)` form, loop indices use `nat_to_word`,
and the total byte count `tot` is the word `nat_to_word totn`; all range
bookkeeping is `Int` over `bv_unsigned`.
-/

namespace LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.Common.ImageBytes
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.AllocSim2
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.ListFacts
open LinuxProcessSemantics.Common.MuslStrlen
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.Footprint
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymSide
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Examples.alloc_join_ns.SourceMemImage
open LinuxProcessSemantics.Examples.alloc_join_ns.TargetMemImage
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_code
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_defs

def rrom : word → Option byte := seg_rom source_segs

theorem source_init_pc_val : SourceMemImage_init_pc = 0x11190 := by rfl

theorem source_reserved_val :
    segments_reserved source_segs =
      [(0x10000, 0x1000), (0x11000, 0x1000), (0x12000, 0x1000), (0x13000, 0x1000)] := by
  decide +kernel

/-- Stores at/above the first writable address are legal. The read-only part
of the image spans THREE page-rounded segments: [0x10000, 0x11000) headers,
[0x11000, 0x12000) text (`-z separate-code`), and [0x12000, 0x13000)
rodata/.eh_frame. Stores are legal from 0x13000 up, where writable data begins. -/
theorem source_avoids_ro (a : word) (n : Int) (Ha : 0x13000 ≤ bv_unsigned a) :
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true := by
  exact range_avoids_ro_above source_segs 0x13000 _ n (by decide +kernel) Ha

/-- The source image's WRITABLE window: the rw- segment covers
[0x13000, 0x14000), and the snapshot carries a byte for every address in it
(.bss is zero-filled in the .hex). Thus `wview` is defined there whatever the
overlay holds: a store into .data/.bss needs no prior write. This is the
`store_ok` side condition machine stores carry; stack targets instead use
the RLIMIT_STACK window (`solve_store_ok`). -/
theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  have hchars := SourceMemImage_seg_bytes_003_hex
  have hlen : SourceMemImage_seg_bytes_003_chars.length = 8192 := by
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  have window (n : Nat) (a : word) (hlo : 0x13000 ≤ bv_unsigned a)
      (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
      wseg_ok source_segs a n = true := by
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      have hf : find_segment source_segs (bv_unsigned a) 1 = some SourceMemImage_segment_003 := by
        simp only [source_segs, Source.loaded_segments, SourceMemImage_loaded_segments,
          find_segment, SourceMemImage_segment_000, SourceMemImage_segment_001,
          SourceMemImage_segment_002, SourceMemImage_segment_003]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        repeat first | split | omega | rfl
      have hb : (segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - 0x13000).toNat).isSome = true := by
        rw [SourceMemImage_segment_003_byte_ascii]
        simp only [ascii_segment_byte_at, hlen]
        rw [ite_eq_left (by omega)]
        exact hex_chars_byte_at_isSome _ _ hchars (by omega)
      have hu : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
      have ht := ih (a + 1) (by omega) (by omega)
      have hw : seg_writable SourceMemImage_segment_003 = true := by decide +kernel
      rw [wseg_ok]
      simp only [hf, hw, ht, Bool.true_and, Bool.and_true]
      have hb' : (segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat).isSome = true := hb
      cases he : segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb'
      | some b => rfl
  exact window 4096 0x13000 (by decide +kernel) (by decide +kernel)

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (Hlo : 0x13000 ≤ bv_unsigned a) (Hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true := by
  exact store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    (by decide +kernel) (by decide +kernel) (by decide +kernel) source_data_wseg Hlo Hhi

/-- A region [b, b+l) free against the page-rounded reservations avoids the
read-only segment everywhere inside it. With four reservations, the free
region lies entirely below 0x10000 or at/above 0x14000. -/
theorem source_free_avoids (b l : word)
    (Hfree : region_free (segments_reserved source_segs) b l = true)
    (Hl : 0 < bv_unsigned l) (a k : Int) (Hlo : bv_unsigned b ≤ a)
    (Hhi : a + k ≤ bv_unsigned b + bv_unsigned l) :
    range_avoids_ro_segs source_segs a k = true := by
  rw [source_reserved_val] at Hfree
  simp only [region_free, Bool.and_eq_true, Bool.not_eq_true', iv_overlap,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_lt] at Hfree
  change ((0x10000 + 0x1000 ≤ bv_unsigned b ∨ bv_unsigned b + bv_unsigned l ≤ 0x10000) ∧
    (0x11000 + 0x1000 ≤ bv_unsigned b ∨ bv_unsigned b + bv_unsigned l ≤ 0x11000) ∧
    (0x12000 + 0x1000 ≤ bv_unsigned b ∨ bv_unsigned b + bv_unsigned l ≤ 0x12000) ∧
    (0x13000 + 0x1000 ≤ bv_unsigned b ∨ bv_unsigned b + bv_unsigned l ≤ 0x13000) ∧ True) at Hfree
  have Hcase : bv_unsigned b + bv_unsigned l ≤ 0x10000 ∨ 0x14000 ≤ bv_unsigned b := by
    omega
  rcases Hcase with Hc | Hc
  · change ((false || !(decide (0x10000 < a + k) && _)) &&
      ((false || !(decide (0x11000 < a + k) && _)) &&
      ((false || !(decide (0x12000 < a + k) && _)) && ((true || _) && true)))) = true
    have H0 : ¬ 0x10000 < a + k := by omega
    have H1 : ¬ 0x11000 < a + k := by omega
    have H2 : ¬ 0x12000 < a + k := by omega
    simp only [H0, H1, H2, decide_false, Bool.false_and, Bool.not_false,
      Bool.false_or, Bool.true_or, Bool.and_true]
  · exact range_avoids_ro_above source_segs 0x13000 a k (by decide +kernel) (by omega)

theorem rsp_lo_num (rsp : word) (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) :
    0x7fff80000000 ≤ bv_unsigned rsp := Hsp_lo

theorem rsp_hi_num (rsp : word) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    bv_unsigned rsp ≤ 0x800000000000 := Hsp_hi

theorem rtop_src_val : reserved_top (segments_reserved source_segs) = 0x14000 := by
  rw [source_reserved_val]
  rfl

theorem rbrk_lo_num (rbrk : word)
    (Hbrk_lo : reserved_top (segments_reserved source_segs) ≤ bv_unsigned rbrk) :
    0x14000 ≤ bv_unsigned rbrk := by
  rw [← rtop_src_val]
  exact Hbrk_lo

theorem rbrk_hi_num (rbrk : word)
    (Hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max) :
    bv_unsigned rbrk ≤ 0x14000 + 1073741824 := by
  rw [← rtop_src_val, ← brk_aslr_max_val]
  exact Hbrk_hi

theorem rbrk_lt64 (rbrk : word)
    (Hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max) :
    bv_unsigned rbrk < 2 ^ 64 := by
  have H := rbrk_hi_num rbrk Hbrk_hi
  omega

def argcN (inp : ProcInput) : word := len_word inp.in_argv

def wmem (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) : word → Option byte :=
  wrap_mem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd

theorem u_argcN (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (argcN inp) = (inp.in_argv.length : Int) := by
  have H := valid_argv_len inp.in_argv Hva
  unfold argcN len_word
  exact u_Z2bv _ (by omega) (by omega)

theorem argcN_le (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (argcN inp) ≤ 1024 := by
  rw [u_argcN inp Hva]
  exact valid_argv_len inp.in_argv Hva

/-- No-overflow bound for the initial stack image (feeds the stack-read
lemmas' new side conditions). -/
theorem source_bsb_nw (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap rrnd).length : Int) < 2 ^ 64 := by
  have H := bsb_bound source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd Hva Hve
  have Hhi := rsp_hi_num rsp Hsp_hi
  omega

/-- environ pointer _start stores at 0x13000. -/
def envp_val (inp : ProcInput) (rsp : word) : word :=
  Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * (inp.in_argv.length : Int))

/-- The a2 chain _start computes (`a1 = sp+8`, `t0 = argc << 3`,
`a2 = a1 + t0 + 8`) equals `envp_val`. -/
theorem envp_val_eq (inp : ProcInput) (Hva : valid_argv inp.in_argv) (rsp : word)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp) 3)) 8 =
      envp_val inp rsp := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hlen := valid_argv_len inp.in_argv Hva
  have Hs : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp + 8)) = bv_unsigned rsp + 8 :=
    u_Z2bv _ (by omega) (by omega)
  have Ht : bv_unsigned (v_slli (argcN inp) 3) = 8 * (inp.in_argv.length : Int) := by
    rw [v_slli_3 _ (by rw [u_argcN inp Hva]; omega), u_argcN inp Hva]
  apply bv_eq_of_unsigned
  unfold envp_val v_addi
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned,
    v_add_small _ _ (by rw [Hs, Ht]; omega), Hs, Ht]
  congr 1 <;> omega

/-- The register shift the crt's `slli t0,a0,3` compiles to, in the
immediate-shift spelling used elsewhere in this file. The shift amount is
a closed literal; only the shifted value is symbolic. -/
theorem v_sll_3 (x : word) : v_sll x (Z_to_bv 64 3) = v_slli x 3 := by
  rfl

/-- `envp_val_eq` in the spelling a REFLECTIVE block leaves behind: the
executor denotes the crt's four-instruction envp computation as an
`alu64`/`v_sll` tree, which becomes `envp_val` here. Without this lemma the
exit memory is only CONVERTIBLE to `fmem`, and finding that conversion
costs the unifier minutes. -/
theorem envp_val_sym (inp : ProcInput) (Hva : valid_argv inp.in_argv) (rsp : word)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    Z_to_bv 64 (bv_unsigned (alu64 .ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (argcN inp) (Z_to_bv 64 3))) + 8) = envp_val inp rsp := by
  rw [alu_add, v_sll_3]
  exact envp_val_eq inp Hva rsp Hsp_lo Hsp_hi

/-- Memory after _start's environ store. -/
def emem (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) : word → Option byte :=
  wbytes (wmem inp rsp rrnd) 0x13000 (word_to_le_bytes 8 (envp_val inp rsp))

/-- main()'s 48-byte frame (stores in execution order; sp = rsp - 48):
s1@+24 (rsp-24), ra@+40 (rsp-8, = 0x111bc), s0@+32 (rsp-16),
s2@+16 (rsp-32), s3@+8 (rsp-40), s4@+0 (rsp-48). -/
def fmem (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (emem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x111bc : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))

theorem rdn_emem_above (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (n : Nat) (Ha : bv_unsigned rsp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (emem inp rsp rrnd) a n = rdn source_segs (wmem inp rsp rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold emem
  rw [rdn_wbytes_disjoint]
  · rw [length_N_to_le_bytes]; imm_norm; omega
  · exact Hn

theorem rdn_fmem_above (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (n : Nat) (Ha : bv_unsigned rsp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (fmem inp rsp rrnd) a n = rdn source_segs (wmem inp rsp rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hn]
  exact rdn_emem_above inp rsp rrnd Hsp_lo Hsp_hi a n Ha Hn

theorem rdn_wmem_stack (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (a : word) (n : Nat) (Ha : bv_unsigned rsp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (wmem inp rsp rrnd) a n =
      rdn source_segs (stack_to_mem rsp (entry_stack_image source_phdrs rsp
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd)) a n := by
  apply rdn_wrap_stack_above <;> assumption

/-- argc at rsp. -/
theorem read_argc_w (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    rdn source_segs (wmem inp rsp rrnd) rsp 8 = some (word_le8 (argcN inp)) := by
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_wmem_stack inp rsp rrnd rsp 8 (by omega) (by omega)]
  apply read_argc
  exact source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi

theorem read_slot_ra (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111bc : word)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _
        (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

theorem read_slot_0 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (a : word) (Ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)]) :
    rdn source_segs (fmem inp rsp rrnd) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
  rcases Ha with rfl | rfl | rfl | rfl | rfl
  all_goals repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _
        (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 65536 in
/-- From main's epilogue with ANY memory whose frame slots read back the
initial values: exit with code = a0, no output. sp = rsp - 48. -/
theorem source_epilogue (rsp : word)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H10 : reg_get regs 10 = code) (Hc : bv_unsigned code < 256)
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111bc : word)))
    (Hsl : ∀ a : word, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    to_wexit source_segs (mkst regs 0x11098 mem rrom) [] code := by
  -- The same six reloads, stack pop, return and li a7,93 as the Rocq block,
  -- expanded into steps using the generated fetch and decode proofs.
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  stepld SF_11098 SD_11098 (Z_to_bv 64 (bv_unsigned rsp - 8))
    (0x111bc : word) (exact Hra)
  stepld SF_1109c SD_1109c (Z_to_bv 64 (bv_unsigned rsp - 16))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inl True.intro))
  stepld SF_110a0 SD_110a0 (Z_to_bv 64 (bv_unsigned rsp - 24))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inl True.intro)))
  stepld SF_110a4 SD_110a4 (Z_to_bv 64 (bv_unsigned rsp - 32))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inr (Or.inl True.intro))))
  stepld SF_110a8 SD_110a8 (Z_to_bv 64 (bv_unsigned rsp - 40))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))
  stepld SF_110ac SD_110ac (Z_to_bv 64 (bv_unsigned rsp - 48))
    (Z_to_bv 64 0) (apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (Or.inr (Or.inr (Or.inr (Or.inr True.intro)))))
  stepiv SF_110b0 SD_110b0 rsp
    (getr_resolve; regupd_resolve; rw [H2]; sp_norm; apply bv_eq_of_unsigned; u_norm; omega)
  stepjr SF_110b4 SD_110b4 (0x111bc : word) (getr_resolve; regupd_resolve; rfl)
  stepiv SF_111bc SD_111bc (Z_to_bv 64 93) (getr_resolve; bveq)
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ SF_111c0 rfl
  apply tw_exit_coden
  · getr_resolve; regupd_resolve; decide +kernel
  · regupd_resolve; exact H10
  · exact Hc

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- argc < 2: no output, exit 2. Unlike the gcc 9 build (bare ret with no
frame), the frame is built BEFORE the argc test, so this path goes through
the prologue and shared epilogue. -/
theorem source_wexit_lt2 (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hlt2 : inp.in_argv.length < 2) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11190 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 2) := by
  -- The Rocq block's 22 instructions: crt entry, seven stores, argc load,
  -- frame push, argc test and jump to the shared epilogue. The initial
  -- callee-saved registers are zero, so the resulting memory is fmem.
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hsms := stack_max_size_val
  have HargcLe := valid_argv_len inp.in_argv Hva
  have Hu := u_argcN inp Hva
  rw [init_mkst]
  norm_pc
  stepi SF_11190 SD_11190
  stepi SF_11194 SD_11194
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_ld (bs := word_le8 (argcN inp)) (v := argcN inp)
      (hfetch := SF_11198) (hecall := rfl) (hdecode := SD_11198)
    · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
      exact read_argc_w inp Hva Hve rsp rrnd Hsp_hi
    · exact bytes_le_n_to_le_8 _
  step_simpl
  stepiv SF_1119c SD_1119c (Z_to_bv 64 (bv_unsigned rsp + 8))
    (getr_resolve; regupd_resolve; sp_norm; rfl)
  stepiv SF_111a0 SD_111a0 (v_slli (argcN inp) 3)
    (getr_resolve; regupd_resolve; rfl)
  stepiv SF_111a4 SD_111a4
    (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp) 3))
    (getr_resolve; regupd_resolve; rfl)
  stepiv SF_111a8 SD_111a8 (envp_val inp rsp)
    (getr_resolve; regupd_resolve; exact envp_val_eq inp Hva rsp Hsp_lo Hsp_hi)
  stepi SF_111ac SD_111ac
  stepiv SF_111b0 SD_111b0 (0x13000 : word) (getr_resolve; regupd_resolve; bveq)
  stepsd SF_111b4 SD_111b4 (0x13000 : word) (envp_val inp rsp)
    (getr_resolve; regupd_resolve; rfl) (apply source_store_ok <;> decide +kernel)
  stepj SF_111b8 SD_111b8
  stepiv SF_11000 SD_11000 (Z_to_bv 64 (bv_unsigned rsp - 48))
    (getr_resolve; regupd_resolve; sp_norm; rfl)
  stepsd SF_11004 SD_11004 (Z_to_bv 64 (bv_unsigned rsp - 24)) (Z_to_bv 64 0)
    (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
  stepsd SF_11008 SD_11008 (Z_to_bv 64 (bv_unsigned rsp - 8)) ((0x111bc : word))
    (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
  stepsd SF_1100c SD_1100c (Z_to_bv 64 (bv_unsigned rsp - 16)) (Z_to_bv 64 0)
    (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
  stepsd SF_11010 SD_11010 (Z_to_bv 64 (bv_unsigned rsp - 32)) (Z_to_bv 64 0)
    (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
  stepsd SF_11014 SD_11014 (Z_to_bv 64 (bv_unsigned rsp - 40)) (Z_to_bv 64 0)
    (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
  stepsd SF_11018 SD_11018 (Z_to_bv 64 (bv_unsigned rsp - 48)) (Z_to_bv 64 0)
    (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
  stepiv SF_1101c SD_1101c (Z_to_bv 64 1) (getr_resolve; bveq)
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_bge_tk (Hf := SF_11020) (He := rfl) (Hd := SD_11020)
    getr_resolve; regupd_resolve
    rw [c_lts_small _ _ (by decide +kernel) (by omega), bv_ltu_Z]
    simp only [show ¬ bv_unsigned (Z_to_bv 64 1) < bv_unsigned (argcN inp) by
      change ¬ 1 < bv_unsigned (argcN inp); omega, decide_false]
  norm_pc
  stepiv SF_11180 SD_11180 (Z_to_bv 64 2) (getr_resolve; bveq)
  stepj SF_11184 SD_11184
  apply source_epilogue rsp Hsp_lo Hsp_hi
  · regupd_resolve; rfl
  · regupd_resolve; rfl
  · decide +kernel
  · exact read_slot_ra inp rsp rrnd Hsp_lo Hsp_hi
  · exact read_slot_0 inp rsp rrnd Hsp_lo Hsp_hi

def sptr (inp : ProcInput) (rsp : word) (k : Nat) : word :=
  cat_argv_ptr rsp inp.in_argv inp.in_envp k

theorem sptr_bounds (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    bv_unsigned rsp ≤ bv_unsigned (sptr inp rsp k) ∧
      bv_unsigned (sptr inp rsp k) + ((inp.in_argv.getD k []).length : Int) + 1 < 2 ^ 64 := by
  unfold sptr
  apply argv_ptr_bounds rsp inp.in_argv inp.in_envp k Hva Hve Hk
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold argv_layout_slack
  omega

/-- `sptr_bounds` restated over `cat_argv_ptr` (the strlen walk below spells
the pointer out). -/
theorem source_ptr_bounds (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    bv_unsigned rsp ≤ bv_unsigned (cat_argv_ptr rsp inp.in_argv inp.in_envp k) ∧
      bv_unsigned (cat_argv_ptr rsp inp.in_argv inp.in_envp k) +
        ((inp.in_argv.getD k []).length : Int) + 1 < 2 ^ 64 :=
  sptr_bounds inp Hva Hve rsp Hsp_hi k Hk

theorem read_arg_ptr_f (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (k : Int))) 8 =
      some (word_le8 (sptr inp rsp k)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hlen := valid_argv_len inp.in_argv Hva
  have HkZ : (k : Int) ≤ 1024 := by omega
  have He : Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (k : Int)) =
      rsp + nat_to_word (8 + 8 * k) := by
    rw [word_add_nat]
    congr 1 <;> omega
  rw [He, rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_wmem_stack inp rsp rrnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k source_phdrs source_segs rsp inp.in_argv inp.in_envp k
    inp.in_uid inp.in_hwcap rrnd Hk (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

theorem read_arg_byte_f (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k j : Nat) (Hk : k < inp.in_argv.length) (Hj : j ≤ (inp.in_argv.getD k []).length) :
    rdn source_segs (fmem inp rsp rrnd) (sptr inp rsp k + nat_to_word j) 1 =
      some [byte_at (inp.in_argv.getD k []) j] := by
  obtain ⟨Hge, Hup⟩ := sptr_bounds inp Hva Hve rsp Hsp_hi k Hk
  have Hslen := valid_argv_str_len inp.in_argv k Hva Hk
  have Hsr := u64_range rsp
  have Hpr := u64_range (sptr inp rsp k)
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_wmem_stack inp rsp rrnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  unfold sptr byte_at
  exact read_argv_byte_k source_phdrs source_segs rsp inp.in_argv inp.in_envp k j
    inp.in_uid inp.in_hwcap rrnd Hk Hj (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

theorem arg_nz_k (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    Z_to_bv 8 0 ∉ inp.in_argv.getD k [] :=
  valid_argv_str_nz inp.in_argv k Hva Hk

/-- Room for a whole word past ANY offset inside argv string k
(instance of MuslStrlen's `argv_ptr_room`). -/
theorem source_ptr_room (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    bv_unsigned (cat_argv_ptr rsp inp.in_argv inp.in_envp k) +
      ((inp.in_argv.getD k []).length : Int) + 17 ≤ bv_unsigned rsp +
      ((build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap rrnd).length : Int) := by
  exact argv_ptr_room source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
    rrnd Hva Hve Hsp_lo Hsp_hi k Hk

-- In grep_args_ns the strlen walk uses memories agreeing with fmem outside
-- a scratch window written by the write wrapper. In THIS binary strlen is
-- only called by the length loop, before any store, so memory is exactly fmem.
-- The mem_ok abstraction degenerates to equality; the walk ports unchanged.
def mem_ok (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (mem : word → Option byte) : Prop := mem = fmem inp rsp rrnd

theorem fmem_ok (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) :
    mem_ok inp rsp rrnd (fmem inp rsp rrnd) := rfl

theorem read_str_byte_m (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (mem : word → Option byte) (Hm : mem_ok inp rsp rrnd mem) (k j : Nat)
    (Hk : k < inp.in_argv.length) (Hj : j ≤ (inp.in_argv.getD k []).length) :
    rdn source_segs mem (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j) 1 =
      some [byte_at (inp.in_argv.getD k []) j] := by
  unfold mem_ok at Hm
  subst mem
  exact read_arg_byte_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi k j Hk Hj

/-- An 8-byte load at offset m inside argv string k never faults: peel this
binary's frame overlay down to `wmem = wrap_mem ...`, then use MuslStrlen's
`argv_word_readable`, where the pad+AT_RANDOM tail argument lives. -/
theorem read_word_m (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (mem : word → Option byte) (Hmk : mem_ok inp rsp rrnd mem) (k m : Nat)
    (Hk : k < inp.in_argv.length) (Hm : m ≤ (inp.in_argv.getD k []).length) :
    ∃ bs, bs.length = 8 ∧
      rdn source_segs mem (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word m) 8 = some bs := by
  unfold mem_ok at Hmk
  subst mem
  obtain ⟨Hge, Hup⟩ := source_ptr_bounds inp Hva Hve rsp Hsp_hi k Hk
  have Hroom := source_ptr_room inp Hva Hve rsp rrnd Hsp_lo Hsp_hi k Hk
  have Hnw := source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi
  have Hur := u64_range (cat_argv_ptr rsp inp.in_argv inp.in_envp k)
  have Hu : bv_unsigned (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word m) =
      bv_unsigned (cat_argv_ptr rsp inp.in_argv inp.in_envp k) + (m : Int) := by
    rw [word_add_nat]
    exact u_Z2bv _ (by omega) (by omega)
  obtain ⟨bs, Hl, Hr⟩ := argv_word_readable source_segs source_phdrs rsp
    inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd Hva Hve Hsp_lo Hsp_hi k m Hk Hm
  refine ⟨bs, Hl, ?_⟩
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _ (by rw [Hu]; omega) (by rw [Hu]; omega)]
  exact Hr

/-- Its bytes as far as the NUL (MuslStrlen's `word_bytes_nth` fed with
this binary's overlay-relative byte-read lemma). -/
theorem read_word_nth (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (mem : word → Option byte) (Hmk : mem_ok inp rsp rrnd mem) (k m : Nat)
    (bs : List byte) (j : Nat) (Hk : k < inp.in_argv.length)
    (Hr : rdn source_segs mem (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word m) 8 = some bs)
    (Hj : j < 8) (Hmj : m + j ≤ (inp.in_argv.getD k []).length) :
    bs.getD j (Z_to_bv 8 0) = byte_at (inp.in_argv.getD k []) (m + j) := by
  apply word_bytes_nth source_segs mem (cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (inp.in_argv.getD k []) m bs j Hr
  · intro i Hi
    exact read_str_byte_m inp Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmk k i Hk Hi
  · exact Hj
  · exact Hmj

/-- `addi rd, rs, 8` over a symbolic base. -/
theorem v_addi_8 (a : word) (m : Nat) :
    v_addi (a + nat_to_word m) 8 = a + nat_to_word (m + 8) := by
  rw [word_add_nat, word_add_nat]
  unfold v_addi
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod,
    bv_wrap64_mod, Int.emod_add_emod]
  congr 1 <;> omega

/-- The exit tail 0x1125c: a0 := a5 - a0 = length, then ret. -/
theorem source_strlen_tail (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (regs : bvmap 5 word) (RA : word) (Hvj : v_jalr RA 0 = RA)
    (Hr10 : reg_get regs 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (Hr15 : reg_get regs 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k +
      nat_to_word (inp.in_argv.getD k []).length) (Hr1 : reg_get regs 1 = RA) :
    ∃ regs', (∀ r : reg, r ≠ 10 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (inp.in_argv.getD k []).length ∧
      msteps source_segs (mkst regs 0x1125c mem rrom) (mkst regs' RA mem rrom) := by
  obtain ⟨Hge, Hup⟩ := source_ptr_bounds inp Hva Hve rsp Hsp_hi k Hk
  have Hslen := valid_argv_str_len inp.in_argv k Hva Hk
  let ptr := cat_argv_ptr rsp inp.in_argv inp.in_envp k
  let regs1 := regupd regs 10 (nat_to_word (inp.in_argv.getD k []).length)
  have E1 : RiscvSemantics.step source_segs (mkst regs 0x1125c mem rrom) =
      MachineOk (mkst regs1 0x11260 mem rrom) := by
    apply step_sub_at (hf := SF_1125c) (he := rfl) (hd := SD_1125c) (hrd := rfl)
    getr_resolve
    rw [Hr10, Hr15]
    unfold v_sub
    rw [word_add_nat, u_Z2bv _ (by have H := u64_range ptr; dsimp only [ptr] at H; omega) (by omega)]
    unfold nat_to_word
    congr 1 <;> omega
  have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11260 mem rrom) =
      MachineOk (mkst regs1 RA mem rrom) := by
    rw [step_jalr_x0 _ _ _ _ _ _ _ _ RA SF_11260 rfl SD_11260]
    · imm_norm; rw [Hvj]
    · dsimp only [regs1]; getr_resolve; exact Hr1
  refine ⟨regs1, ?_, ?_, ?_⟩
  · intro r Hr
    exact regupd_other regs 10 _ r Hr
  · exact regupd_same _ _ _
  · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2 (msteps.mst_refl _))

/-- The final byte scan 0x11254, from offset j. -/
theorem source_strlen_scan (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (Hmem : mem_ok inp rsp rrnd mem) (RA : word) (Hvj : v_jalr RA 0 = RA)
    (d j : Nat) (regs : bvmap 5 word) (Hjd : j + d = (inp.in_argv.getD k []).length)
    (Hr10 : reg_get regs 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (Hr15 : reg_get regs 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j)
    (Hr1 : reg_get regs 1 = RA) :
    ∃ regs', (∀ r : reg, r ≠ 10 → r ≠ 14 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (inp.in_argv.getD k []).length ∧
      msteps source_segs (mkst regs 0x11254 mem rrom) (mkst regs' RA mem rrom) := by
  have Hsnz := valid_argv_str_nz inp.in_argv k Hva Hk
  induction d generalizing j regs with
  | zero =>
    have Hj : j = (inp.in_argv.getD k []).length := by omega
    let regs1 := regupd regs 14 (Z_to_bv 64 0)
    have E1 : RiscvSemantics.step source_segs (mkst regs 0x11254 mem rrom) =
        MachineOk (mkst regs1 0x11258 mem rrom) := by
      rw [step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) SF_11254 rfl SD_11254]
      · rfl
      · getr_resolve; imm_norm; rw [Hr15, v_addi_0]
        have Hrd := read_str_byte_m inp Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
        rw [Hj, byte_at_len] at Hrd
        rw [Hj]; exact Hrd
    have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11258 mem rrom) =
        MachineOk (mkst regs1 0x1125c mem rrom) := by
      apply step_bne_ft (hf := SF_11258) (he := rfl) (hd := SD_11258)
      dsimp only [regs1]; getr_resolve; exact c_eq_0_true
    obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_tail inp Hva Hve rsp Hsp_hi k Hk mem regs1 RA Hvj
      (by dsimp only [regs1]; regupd_resolve; exact Hr10)
      (by dsimp only [regs1]; regupd_resolve; rw [Hr15, Hj])
      (by dsimp only [regs1]; regupd_resolve; exact Hr1)
    refine ⟨regs', ?_, H10, ?_⟩
    · intro r Hx10 Hx14 _
      rw [Hag r Hx10]
      exact regupd_other regs 14 _ r Hx14
    · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2 Hms)
  | succ d IH =>
    have Hjlt : j < (inp.in_argv.getD k []).length := by omega
    let b := byte_at (inp.in_argv.getD k []) j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hsnz Hjlt
    let regs1 := regupd regs 14 (Z_to_bv 64 (bv_unsigned b))
    have E1 : RiscvSemantics.step source_segs (mkst regs 0x11254 mem rrom) =
        MachineOk (mkst regs1 0x11258 mem rrom) := by
      rw [step_lbu _ _ _ _ _ _ _ _ _ b SF_11254 rfl SD_11254]
      · rfl
      · getr_resolve; imm_norm; rw [Hr15, v_addi_0]
        exact read_str_byte_m inp Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
    have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11258 mem rrom) =
        MachineOk (mkst regs1 0x11250 mem rrom) := by
      apply step_bne_tk (hf := SF_11258) (he := rfl) (hd := SD_11258)
      dsimp only [regs1]; getr_resolve
      apply c_eq_0_false
      rw [u_zext8]
      exact byte_nz_u b Hbnz
    let regs2 := regupd regs1 15 (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word (j + 1))
    have E3 : RiscvSemantics.step source_segs (mkst regs1 0x11250 mem rrom) =
        MachineOk (mkst regs2 0x11254 mem rrom) := by
      apply step_addi_at (hf := SF_11250) (he := rfl) (hd := SD_11250) (hrd := rfl)
      dsimp only [regs1]; getr_resolve; rw [Hr15]
      exact word_add_nat_1 _ _
    obtain ⟨regs', Hag, H10, Hms⟩ := IH (j + 1) regs2 (by omega)
      (by dsimp only [regs2, regs1]; regupd_resolve; exact Hr10)
      (by dsimp only [regs2]; exact regupd_same _ _ _)
      (by dsimp only [regs2, regs1]; regupd_resolve; exact Hr1)
    refine ⟨regs', ?_, H10, ?_⟩
    · intro r Hx10 Hx14 Hx15
      rw [Hag r Hx10 Hx14 Hx15]
      dsimp only [regs2, regs1]
      rw [regupd_other _ _ _ _ Hx15, regupd_other _ _ _ _ Hx14]
    · exact msteps.mst_step _ _ _ rfl E1
        (msteps.mst_step _ _ _ rfl E2 (msteps.mst_step _ _ _ rfl E3 Hms))

/-- The word-loop body 0x11234..0x11248: load the word at ptr+m and
compute musl's has-zero test into a4. -/
theorem source_strlen_word_body (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (Hmem : mem_ok inp rsp rrnd mem) (m : Nat) (regs : bvmap 5 word)
    (Hm : m ≤ (inp.in_argv.getD k []).length)
    (Hr15 : reg_get regs 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word m)
    (Hr11 : reg_get regs 11 = Z_to_bv 64 18374403900871474943)
    (Hr12 : reg_get regs 12 = Z_to_bv 64 9259542123273814144) :
    ∃ regs1 bs, msteps source_segs (mkst regs 0x11234 mem rrom) (mkst regs1 0x11248 mem rrom) ∧
      bs.length = 8 ∧
      (∀ j, j < 8 → m + j ≤ (inp.in_argv.getD k []).length →
        bs.getD j (Z_to_bv 8 0) = byte_at (inp.in_argv.getD k []) (m + j)) ∧
      (∀ r : reg, r ≠ 13 → r ≠ 14 → reg_get regs1 r = reg_get regs r) ∧
      bv_unsigned (reg_get regs1 14) = HZ.Tz (bytes_le_to_Z bs) := by
  obtain ⟨bs, Hlenb, Hread⟩ := read_word_m inp Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k m Hk Hm
  have Hrange := bytes_le_to_Z_range bs Hlenb
  refine ⟨?_, bs, ?_, Hlenb, ?_, ?_, ?_⟩
  rotate_left
  · apply msteps.mst_step _ _ _ rfl
    · apply step_ld (bs := bs) (v := Z_to_bv 64 (bytes_le_to_Z bs))
        (hfetch := SF_11234) (hecall := rfl) (hdecode := SD_11234)
      · getr_resolve; imm_norm; rw [Hr15, v_addi_0]; exact Hread
      · exact (u_Z2bv _ Hrange.1 Hrange.2).symm
    step_simpl
    stepi SF_11238 SD_11238
    stepi SF_1123c SD_1123c
    stepi SF_11240 SD_11240
    stepi SF_11244 SD_11244
    exact msteps.mst_refl _
  · intro j Hj Hmj
    exact read_word_nth inp Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k m bs j Hk Hread Hj Hmj
  · intro r H13 H14
    repeat rw [regupd_other _ _ _ _ (by assumption)]
  · regupd_resolve; getr_resolve
    rw [Hr11, Hr12]
    imm_norm
    rw [v_haszero, u_Z2bv _ Hrange.1 Hrange.2]

/-- Leaving the word loop at 0x11248 (a4 ≠ 0: the word holds a NUL). -/
theorem source_strlen_word_exit (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (Hmem : mem_ok inp rsp rrnd mem) (RA : word) (Hvj : v_jalr RA 0 = RA)
    (m : Nat) (regs : bvmap 5 word) (Hm : m ≤ (inp.in_argv.getD k []).length)
    (Ha4 : bv_unsigned (reg_get regs 14) ≠ 0)
    (Hr10 : reg_get regs 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (Hr15 : reg_get regs 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word m)
    (Hr1 : reg_get regs 1 = RA) :
    ∃ regs', (∀ r : reg, r ≠ 10 → r ≠ 14 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (inp.in_argv.getD k []).length ∧
      msteps source_segs (mkst regs 0x11248 mem rrom) (mkst regs' RA mem rrom) := by
  have E1 : RiscvSemantics.step source_segs (mkst regs 0x11248 mem rrom) =
      MachineOk (mkst regs 0x1124c mem rrom) := by
    apply step_beq_ft (hf := SF_11248) (he := rfl) (hd := SD_11248)
    getr_resolve; exact c_eq_0_false _ Ha4
  have E2 : RiscvSemantics.step source_segs (mkst regs 0x1124c mem rrom) =
      MachineOk (mkst regs 0x11254 mem rrom) := by
    exact step_jal_x0 _ _ _ _ _ _ _ SF_1124c rfl SD_1124c
  obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_scan inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
    k Hk mem Hmem RA Hvj ((inp.in_argv.getD k []).length - m) m regs (by omega) Hr10 Hr15 Hr1
  exact ⟨regs', Hag, H10, msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2 Hms)⟩

/-- The word-at-a-time loop 0x11234, from offset m. -/
theorem source_strlen_word (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (Hmem : mem_ok inp rsp rrnd mem) (RA : word) (Hvj : v_jalr RA 0 = RA)
    (f m : Nat) (regs : bvmap 5 word) (Hf : (inp.in_argv.getD k []).length - m ≤ f)
    (Hm : m ≤ (inp.in_argv.getD k []).length)
    (Hr10 : reg_get regs 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (Hr15 : reg_get regs 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word m)
    (Hr11 : reg_get regs 11 = Z_to_bv 64 18374403900871474943)
    (Hr12 : reg_get regs 12 = Z_to_bv 64 9259542123273814144)
    (Hr1 : reg_get regs 1 = RA) :
    ∃ regs', (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (inp.in_argv.getD k []).length ∧
      msteps source_segs (mkst regs 0x11234 mem rrom) (mkst regs' RA mem rrom) := by
  have Hsnz := valid_argv_str_nz inp.in_argv k Hva Hk
  induction f generalizing m regs with
  | zero =>
    obtain ⟨regs1, bs, Hms1, Hlenb, Hnthb, Hag1, Ha4⟩ :=
      source_strlen_word_body inp Hva Hve rsp rrnd Hsp_lo Hsp_hi k Hk mem Hmem m regs Hm Hr15 Hr11 Hr12
    have Hrange := bytes_le_to_Z_range bs Hlenb
    have Hm0 : m = (inp.in_argv.getD k []).length := by omega
    have Hnz : bv_unsigned (reg_get regs1 14) ≠ 0 := by
      rw [Ha4]
      apply HZ.Tz_haszero _ ((inp.in_argv.getD k []).length - m) Hrange (by omega)
      · rw [zb_of_bytes _ _ (by omega), Hnthb _ (by omega) (by omega)]
        rw [show m + ((inp.in_argv.getD k []).length - m) = (inp.in_argv.getD k []).length by omega,
          byte_at_len]
        exact u8_zero
      · intro j Hj
        rw [zb_of_bytes _ _ (by omega), Hnthb _ (by omega) (by omega)]
        exact byte_nz_u _ (byte_at_nz _ _ Hsnz (by omega))
    obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_word_exit inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
      k Hk mem Hmem RA Hvj m regs1 Hm Hnz
      (by rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr10)
      (by rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr15)
      (by rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr1)
    refine ⟨regs', ?_, H10, msteps_trans _ _ _ _ Hms1 Hms⟩
    intro r Hx10 _ _ Hx13 Hx14 Hx15
    rw [Hag r Hx10 Hx14 Hx15]
    exact Hag1 r Hx13 Hx14
  | succ f IH =>
    obtain ⟨regs1, bs, Hms1, Hlenb, Hnthb, Hag1, Ha4⟩ :=
      source_strlen_word_body inp Hva Hve rsp rrnd Hsp_lo Hsp_hi k Hk mem Hmem m regs Hm Hr15 Hr11 Hr12
    have Hrange := bytes_le_to_Z_range bs Hlenb
    by_cases Hle : m + 8 ≤ (inp.in_argv.getD k []).length
    · -- The whole word lies inside the string; keep going.
      have Hz : bv_unsigned (reg_get regs1 14) = 0 := by
        rw [Ha4]
        apply HZ.Tz_nozero _ Hrange
        intro i Hi
        rw [zb_of_bytes _ _ (by omega), Hnthb _ Hi (by omega)]
        exact byte_nz_u _ (byte_at_nz _ _ Hsnz (by omega))
      have E1 : RiscvSemantics.step source_segs (mkst regs1 0x11248 mem rrom) =
          MachineOk (mkst regs1 0x11230 mem rrom) := by
        apply step_beq_tk (hf := SF_11248) (he := rfl) (hd := SD_11248)
        getr_resolve; exact c_eq_0_of_u _ Hz
      let regs2 := regupd regs1 15 (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word (m + 8))
      have Hr15' : reg_get regs1 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word m := by
        rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr15
      have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11230 mem rrom) =
          MachineOk (mkst regs2 0x11234 mem rrom) := by
        apply step_addi_at (hf := SF_11230) (he := rfl) (hd := SD_11230) (hrd := rfl)
        getr_resolve; imm_norm; rw [Hr15', v_addi_8]
      obtain ⟨regs', Hag, H10, Hms⟩ := IH (m + 8) regs2 (by omega) Hle
        (by dsimp only [regs2]; regupd_resolve
            rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr10)
        (by dsimp only [regs2]; exact regupd_same _ _ _)
        (by dsimp only [regs2]; regupd_resolve
            rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr11)
        (by dsimp only [regs2]; regupd_resolve
            rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr12)
        (by dsimp only [regs2]; regupd_resolve
            rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr1)
      refine ⟨regs', ?_, H10, ?_⟩
      · intro r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15
        rw [Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15]
        dsimp only [regs2]
        rw [regupd_other _ _ _ _ Hx15]
        exact Hag1 r Hx13 Hx14
      · exact msteps_trans _ _ _ _ Hms1
          (msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2 Hms))
    · -- The NUL lies inside this word; leave the word loop.
      have Hnz : bv_unsigned (reg_get regs1 14) ≠ 0 := by
        rw [Ha4]
        apply HZ.Tz_haszero _ ((inp.in_argv.getD k []).length - m) Hrange (by omega)
        · rw [zb_of_bytes _ _ (by omega), Hnthb _ (by omega) (by omega)]
          rw [show m + ((inp.in_argv.getD k []).length - m) = (inp.in_argv.getD k []).length by omega,
            byte_at_len]
          exact u8_zero
        · intro j Hj
          rw [zb_of_bytes _ _ (by omega), Hnthb _ (by omega) (by omega)]
          exact byte_nz_u _ (byte_at_nz _ _ Hsnz (by omega))
      obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_word_exit inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
        k Hk mem Hmem RA Hvj m regs1 Hm Hnz
        (by rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr10)
        (by rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr15)
        (by rw [Hag1 _ (by reg_neq_tac) (by reg_neq_tac)]; exact Hr1)
      refine ⟨regs', ?_, H10, msteps_trans _ _ _ _ Hms1 Hms⟩
      intro r Hx10 _ _ Hx13 Hx14 Hx15
      rw [Hag r Hx10 Hx14 Hx15]
      exact Hag1 r Hx13 Hx14

/-- The constant setup 0x11208..0x1122c, entering the word loop. -/
theorem source_strlen_setup (mem : word → Option byte) (regs : bvmap 5 word) :
    ∃ regs', msteps source_segs (mkst regs 0x11208 mem rrom) (mkst regs' 0x11234 mem rrom) ∧
      (∀ r : reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 11 = Z_to_bv 64 18374403900871474943 ∧
      reg_get regs' 12 = Z_to_bv 64 9259542123273814144 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · stepi SF_11208 SD_11208
    stepi SF_1120c SD_1120c
    stepi SF_11210 SD_11210
    stepi SF_11214 SD_11214
    stepi SF_11218 SD_11218
    stepi SF_1121c SD_1121c
    stepi SF_11220 SD_11220
    stepi SF_11224 SD_11224
    stepi SF_11228 SD_11228
    stepj SF_1122c SD_1122c
    exact msteps.mst_refl _
  · intro r H11 H12 H13 H14
    repeat rw [regupd_other _ _ _ _ (by assumption)]
  · regupd_resolve; getr_resolve; bveq
  · regupd_resolve; getr_resolve; bveq

/-- Setup + word loop, entered at 0x11208 with a5 = ptr + j. -/
theorem source_strlen_from_aligned (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (Hmem : mem_ok inp rsp rrnd mem) (RA : word) (Hvj : v_jalr RA 0 = RA)
    (j : Nat) (regs : bvmap 5 word) (Hj : j ≤ (inp.in_argv.getD k []).length)
    (Hr10 : reg_get regs 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (Hr15 : reg_get regs 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j)
    (Hr1 : reg_get regs 1 = RA) :
    ∃ regs', (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (inp.in_argv.getD k []).length ∧
      msteps source_segs (mkst regs 0x11208 mem rrom) (mkst regs' RA mem rrom) := by
  obtain ⟨regsC, HmsC, HagC, H11, H12⟩ := source_strlen_setup mem regs
  obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_word inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
    k Hk mem Hmem RA Hvj ((inp.in_argv.getD k []).length - j) j regsC (by omega) Hj
    (by rw [HagC _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact Hr10)
    (by rw [HagC _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact Hr15)
    H11 H12
    (by rw [HagC _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact Hr1)
  refine ⟨regs', ?_, H10, msteps_trans _ _ _ _ HmsC Hms⟩
  intro r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15
  rw [Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15]
  exact HagC r Hx11 Hx12 Hx13 Hx14

/-- The alignment byte scan 0x111f4, from offset j. -/
theorem source_strlen_align (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (Hmem : mem_ok inp rsp rrnd mem) (RA : word) (Hvj : v_jalr RA 0 = RA)
    (d j : Nat) (regs : bvmap 5 word) (Hjd : j + d = (inp.in_argv.getD k []).length)
    (Hr10 : reg_get regs 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (Hr15 : reg_get regs 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j)
    (Hr1 : reg_get regs 1 = RA) :
    ∃ regs', (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (inp.in_argv.getD k []).length ∧
      msteps source_segs (mkst regs 0x111f4 mem rrom) (mkst regs' RA mem rrom) := by
  have Hsnz := valid_argv_str_nz inp.in_argv k Hva Hk
  induction d generalizing j regs with
  | zero =>
    have Hj : j = (inp.in_argv.getD k []).length := by omega
    let regs1 := regupd regs 14 (v_andi (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j) 7)
    have E1 : RiscvSemantics.step source_segs (mkst regs 0x111f4 mem rrom) =
        MachineOk (mkst regs1 0x111f8 mem rrom) := by
      apply step_andi_at (hf := SF_111f4) (he := rfl) (hd := SD_111f4) (hrd := rfl)
      getr_resolve; imm_norm; rw [Hr15]
    have Hr10' : reg_get regs1 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k := by
      dsimp only [regs1]; regupd_resolve; exact Hr10
    have Hr15' : reg_get regs1 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j := by
      dsimp only [regs1]; regupd_resolve; exact Hr15
    have Hr1' : reg_get regs1 1 = RA := by
      dsimp only [regs1]; regupd_resolve; exact Hr1
    by_cases Halg : bv_unsigned (v_andi (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j) 7) = 0
    · -- Aligned: enter the word loop.
      have E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom) =
          MachineOk (mkst regs1 0x11208 mem rrom) := by
        apply step_beq_tk (hf := SF_111f8) (he := rfl) (hd := SD_111f8)
        dsimp only [regs1]; getr_resolve; exact c_eq_0_of_u _ Halg
      obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_from_aligned inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
        k Hk mem Hmem RA Hvj j regs1 (by omega) Hr10' Hr15' Hr1'
      refine ⟨regs', ?_, H10, msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2 Hms)⟩
      intro r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15
      rw [Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15]
      exact regupd_other regs 14 _ r Hx14
    · -- Unaligned: inspect the byte.
      have E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom) =
          MachineOk (mkst regs1 0x111fc mem rrom) := by
        apply step_beq_ft (hf := SF_111f8) (he := rfl) (hd := SD_111f8)
        dsimp only [regs1]; getr_resolve; exact c_eq_0_false _ Halg
      let regs2 := regupd regs1 14 (Z_to_bv 64 0)
      have E3 : RiscvSemantics.step source_segs (mkst regs1 0x111fc mem rrom) =
          MachineOk (mkst regs2 0x11200 mem rrom) := by
        rw [step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) SF_111fc rfl SD_111fc]
        · rfl
        · getr_resolve; imm_norm; rw [Hr15, v_addi_0]
          have Hrd := read_str_byte_m inp Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
          rw [Hj, byte_at_len] at Hrd
          rw [Hj]; exact Hrd
      have E4 : RiscvSemantics.step source_segs (mkst regs2 0x11200 mem rrom) =
          MachineOk (mkst regs2 0x11204 mem rrom) := by
        apply step_bne_ft (hf := SF_11200) (he := rfl) (hd := SD_11200)
        dsimp only [regs2]; getr_resolve; exact c_eq_0_true
      have E5 : RiscvSemantics.step source_segs (mkst regs2 0x11204 mem rrom) =
          MachineOk (mkst regs2 0x1125c mem rrom) := by
        exact step_jal_x0 _ _ _ _ _ _ _ SF_11204 rfl SD_11204
      obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_tail inp Hva Hve rsp Hsp_hi k Hk mem regs2 RA Hvj
        (by dsimp only [regs2]; regupd_resolve; exact Hr10)
        (by dsimp only [regs2]; regupd_resolve; rw [Hr15, Hj])
        (by dsimp only [regs2]; regupd_resolve; exact Hr1)
      refine ⟨regs', ?_, H10, ?_⟩
      · intro r Hx10 _ _ _ Hx14 _
        rw [Hag r Hx10]
        dsimp only [regs2, regs1]
        repeat rw [regupd_other _ _ _ _ Hx14]
      · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2
          (msteps.mst_step _ _ _ rfl E3 (msteps.mst_step _ _ _ rfl E4 (msteps.mst_step _ _ _ rfl E5 Hms))))
  | succ d IH =>
    have Hjlt : j < (inp.in_argv.getD k []).length := by omega
    let regs1 := regupd regs 14 (v_andi (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j) 7)
    have E1 : RiscvSemantics.step source_segs (mkst regs 0x111f4 mem rrom) =
        MachineOk (mkst regs1 0x111f8 mem rrom) := by
      apply step_andi_at (hf := SF_111f4) (he := rfl) (hd := SD_111f4) (hrd := rfl)
      getr_resolve; imm_norm; rw [Hr15]
    have Hr10' : reg_get regs1 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k := by
      dsimp only [regs1]; regupd_resolve; exact Hr10
    have Hr15' : reg_get regs1 15 = cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j := by
      dsimp only [regs1]; regupd_resolve; exact Hr15
    have Hr1' : reg_get regs1 1 = RA := by
      dsimp only [regs1]; regupd_resolve; exact Hr1
    by_cases Halg : bv_unsigned (v_andi (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word j) 7) = 0
    · -- Aligned: enter the word loop.
      have E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom) =
          MachineOk (mkst regs1 0x11208 mem rrom) := by
        apply step_beq_tk (hf := SF_111f8) (he := rfl) (hd := SD_111f8)
        dsimp only [regs1]; getr_resolve; exact c_eq_0_of_u _ Halg
      obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_from_aligned inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
        k Hk mem Hmem RA Hvj j regs1 (by omega) Hr10' Hr15' Hr1'
      refine ⟨regs', ?_, H10, msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2 Hms)⟩
      intro r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15
      rw [Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15]
      exact regupd_other regs 14 _ r Hx14
    · -- Unaligned: inspect the byte.
      have E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom) =
          MachineOk (mkst regs1 0x111fc mem rrom) := by
        apply step_beq_ft (hf := SF_111f8) (he := rfl) (hd := SD_111f8)
        dsimp only [regs1]; getr_resolve; exact c_eq_0_false _ Halg
      let b := byte_at (inp.in_argv.getD k []) j
      have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hsnz Hjlt
      let regs2 := regupd regs1 14 (Z_to_bv 64 (bv_unsigned b))
      have E3 : RiscvSemantics.step source_segs (mkst regs1 0x111fc mem rrom) =
          MachineOk (mkst regs2 0x11200 mem rrom) := by
        rw [step_lbu _ _ _ _ _ _ _ _ _ b SF_111fc rfl SD_111fc]
        · rfl
        · getr_resolve; imm_norm; rw [Hr15, v_addi_0]
          exact read_str_byte_m inp Hva Hve rsp rrnd Hsp_lo Hsp_hi mem Hmem k j Hk (by omega)
      have E4 : RiscvSemantics.step source_segs (mkst regs2 0x11200 mem rrom) =
          MachineOk (mkst regs2 0x111f0 mem rrom) := by
        apply step_bne_tk (hf := SF_11200) (he := rfl) (hd := SD_11200)
        dsimp only [regs2]; getr_resolve
        apply c_eq_0_false
        rw [u_zext8]
        exact byte_nz_u b Hbnz
      let regs3 := regupd regs2 15 (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word (j + 1))
      have E5 : RiscvSemantics.step source_segs (mkst regs2 0x111f0 mem rrom) =
          MachineOk (mkst regs3 0x111f4 mem rrom) := by
        apply step_addi_at (hf := SF_111f0) (he := rfl) (hd := SD_111f0) (hrd := rfl)
        dsimp only [regs2, regs1]; getr_resolve; imm_norm; rw [Hr15, word_add_nat_1]
      obtain ⟨regs', Hag, H10, Hms⟩ := IH (j + 1) regs3 (by omega)
        (by dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr10)
        (by dsimp only [regs3]; exact regupd_same _ _ _)
        (by dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr1)
      refine ⟨regs', ?_, H10, ?_⟩
      · intro r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15
        rw [Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15]
        dsimp only [regs3, regs2, regs1]
        repeat rw [regupd_other _ _ _ _ (by assumption)]
      · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2
          (msteps.mst_step _ _ _ rfl E3 (msteps.mst_step _ _ _ rfl E4 (msteps.mst_step _ _ _ rfl E5 Hms))))

/-- strlen(argv[k]): enter at 0x111e8 with a0 = &argv[k] and ra = RA,
return to RA with a0 = the length. Clobbers a0..a5 only. -/
theorem source_strlen (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (mem : word → Option byte)
    (Hmem : mem_ok inp rsp rrnd mem) (RA : word) (Hvj : v_jalr RA 0 = RA)
    (regs : bvmap 5 word)
    (Hr10 : reg_get regs 10 = cat_argv_ptr rsp inp.in_argv inp.in_envp k)
    (Hr1 : reg_get regs 1 = RA) :
    ∃ regs', (∀ r : reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 10 = nat_to_word (inp.in_argv.getD k []).length ∧
      msteps source_segs (mkst regs 0x111e8 mem rrom) (mkst regs' RA mem rrom) := by
  let regs1 := regupd regs 15 (cat_argv_ptr rsp inp.in_argv inp.in_envp k + nat_to_word 0)
  have E1 : RiscvSemantics.step source_segs (mkst regs 0x111e8 mem rrom) =
      MachineOk (mkst regs1 0x111ec mem rrom) := by
    apply step_addi_at (hf := SF_111e8) (he := rfl) (hd := SD_111e8) (hrd := rfl)
    getr_resolve; imm_norm; rw [Hr10, v_addi_0, word_add_nat_0]
  have E2 : RiscvSemantics.step source_segs (mkst regs1 0x111ec mem rrom) =
      MachineOk (mkst regs1 0x111f4 mem rrom) := by
    exact step_jal_x0 _ _ _ _ _ _ _ SF_111ec rfl SD_111ec
  obtain ⟨regs', Hag, H10, Hms⟩ := source_strlen_align inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
    k Hk mem Hmem RA Hvj (inp.in_argv.getD k []).length 0 regs1 (by omega)
    (by dsimp only [regs1]; regupd_resolve; exact Hr10)
    (by dsimp only [regs1]; exact regupd_same _ _ _)
    (by dsimp only [regs1]; regupd_resolve; exact Hr1)
  refine ⟨regs', ?_, H10, msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2 Hms)⟩
  intro r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15
  rw [Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15]
  exact regupd_other regs 15 _ r Hx15

theorem tab_join1 (l : List (List byte)) :
    total_arg_bytes_nat l = (join1 l).length + (if l.length == 0 then 0 else 1) := by
  cases l with
  | nil => simp only [List.length_nil, beq_self_eq_true, ite_true, join1, Nat.add_zero, total_arg_bytes_nat, List.foldr_nil]
  | cons a l =>
    rw [ite_eq_right (by simp only [beq_iff_eq, List.length_cons]; omega)]
    rw [← length_wjoin, wjoin_join1 _ (List.cons_ne_nil _ _)]
    simp only [List.length_append, List.length_cons, List.length_nil]

theorem jpre_step (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i) (Hi : i ≤ inp.in_argv.tail.length) :
    (join1 (inp.in_argv.tail.take i)).length =
      (join1 (inp.in_argv.tail.take (i - 1))).length + (inp.in_argv.getD i []).length +
        (if i == 1 then 0 else 1) := by
  have He : inp.in_argv.tail.take i =
      inp.in_argv.tail.take (i - 1) ++ [inp.in_argv.tail.getD (i - 1) []] := by
    calc
      _ = inp.in_argv.tail.take ((i - 1) + 1) := congrArg (fun n => inp.in_argv.tail.take n) (by omega)
      _ = _ := firstn_S_nth _ _ _ [] (by omega)
  rw [He, join1_snoc, List.length_append, length_wjoin, nth_tl,
    show i - 1 + 1 = i by omega, tab_join1, List.length_take]
  rw [Nat.min_eq_left (by omega)]
  simp only [beq_iff_eq]
  split <;> split <;> omega

def totn (inp : ProcInput) : Nat := total_arg_bytes_nat inp.in_argv.tail

def tot (inp : ProcInput) : word := nat_to_word (totn inp)

theorem tl_nonnil (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    inp.in_argv.tail ≠ [] := by
  cases H : inp.in_argv with
  | nil => simp only [H, List.length_nil] at Hge2; omega
  | cons a l =>
    cases l with
    | nil => simp only [H, List.length_cons, List.length_nil] at Hge2; omega
    | cons b l => exact List.cons_ne_nil b l

theorem length_tl_av (inp : ProcInput) : inp.in_argv.tail.length = inp.in_argv.length - 1 :=
  length_tl_list _

theorem totn_ge1 (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) : 1 ≤ totn inp := by
  unfold totn
  rw [tab_join1]
  have Hnz : inp.in_argv.tail.length ≠ 0 := by
    intro H
    exact tl_nonnil inp Hge2 (List.length_eq_zero_iff.mp H)
  rw [ite_eq_right (by simpa only [beq_iff_eq] using Hnz)]
  omega

theorem totn_bound (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    (totn inp : Int) ≤ 2097152 := by
  unfold totn
  have Hb := valid_argv_tab inp.in_argv Hva
  have Htlskip : inp.in_argv.tail = inp.in_argv.drop 1 := by cases inp.in_argv <;> rfl
  rw [Htlskip]
  have He := tab_app (inp.in_argv.take 1) (inp.in_argv.drop 1)
  rw [List.take_append_drop] at He
  omega

theorem u_tot (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (tot inp) = (totn inp : Int) := by
  unfold tot
  apply u_ntw
  have H := totn_bound inp Hva
  omega

theorem tot_ge1 (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hge2 : 2 ≤ inp.in_argv.length) : 1 ≤ bv_unsigned (tot inp) := by
  rw [u_tot inp Hva]
  have H := totn_ge1 inp Hge2
  omega

theorem totN_bound (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (tot inp) ≤ 2097152 := by
  rw [u_tot inp Hva]
  exact totn_bound inp Hva

theorem join1_tl_len_nat (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    (join1 inp.in_argv.tail).length = totn inp - 1 := by
  have H := length_join1 inp.in_argv.tail (tl_nonnil inp Hge2)
  unfold totn
  omega

theorem S_join1_tot (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    nat_to_word ((join1 inp.in_argv.tail).length + 1) = tot inp := by
  unfold tot totn
  rw [length_join1 _ (tl_nonnil inp Hge2)]

theorem jout_len_nat (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    (jout inp.in_argv).length = totn inp := by
  unfold jout
  rw [List.length_append]
  simp only [List.length_cons, List.length_nil]
  have H := join1_tl_len_nat inp Hge2
  have Hge := totn_ge1 inp Hge2
  omega

theorem jout_len_w (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hge2 : 2 ≤ inp.in_argv.length) : word_to_nat (tot inp) = (jout inp.in_argv).length := by
  rw [jout_len_nat inp Hge2]
  unfold tot
  apply word_to_nat_ntw
  have H := totn_bound inp Hva
  omega

/-- The single output buffer fits in one model write: both binaries exit 3
without writing when tot exceeds 65536, so a successful run writes at most
65536 bytes, well inside Uaccess.rw_bytes_max (131072). -/
theorem jout_modeled (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hge2 : 2 ≤ inp.in_argv.length) (Hcap : bv_unsigned (tot inp) ≤ 65536) :
    bufs_modeled [jout inp.in_argv] := by
  apply bufs_modeled_single
  unfold buf_modeled Sys.Uaccess.rw_bytes_max
  rw [jout_len_nat inp Hge2, ← u_tot inp Hva]
  omega

theorem argc_le_nat (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    inp.in_argv.length ≤ 1024 := by
  have H := valid_argv_len inp.in_argv Hva
  omega

theorem iN_le (inp : ProcInput) (Hva : valid_argv inp.in_argv) (i : Nat)
    (Hi : i ≤ inp.in_argv.length) : (i : Int) ≤ 1024 := by
  have H := argc_le_nat inp Hva
  omega

theorem acc_bound (inp : ProcInput) (Hva : valid_argv inp.in_argv) (i : Nat) :
    ((join1 (inp.in_argv.tail.take i)).length : Int) ≤ 2097152 := by
  have Hb := totn_bound inp Hva
  unfold totn at Hb
  have H1 : (join1 (inp.in_argv.tail.take i)).length ≤ total_arg_bytes_nat (inp.in_argv.tail.take i) := by
    rw [tab_join1]
    omega
  have He := tab_app (inp.in_argv.tail.take i) (inp.in_argv.tail.drop i)
  rw [List.take_append_drop] at He
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem source_to_loop (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) :
    ∃ regs1, reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs1 18 = argcN inp ∧
      reg_get regs1 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
      reg_get regs1 20 = Z_to_bv 64 1 ∧ reg_get regs1 9 = Z_to_bv 64 1 ∧
      reg_get regs1 8 = Z_to_bv 64 0 ∧
      msteps source_segs
        (init_machine_state source_segs 0x11190 source_phdrs rsp rrnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs1 0x11034 (fmem inp rsp rrnd) rrom) := by
  -- The Rocq block's 24 instructions: crt startup, six frame spills, the
  -- argc ≥ 2 fall-through and four moves initializing the outer loop.
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hsms := stack_max_size_val
  have HargcLe := valid_argv_len inp.in_argv Hva
  have Hu := u_argcN inp Hva
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 7
  ·
    rw [init_mkst]
    norm_pc
    stepi SF_11190 SD_11190
    stepi SF_11194 SD_11194
    apply msteps.mst_step _ _ _ rfl
    · apply step_ld (bs := word_le8 (argcN inp)) (v := argcN inp)
        (hfetch := SF_11198) (hecall := rfl) (hdecode := SD_11198)
      · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
        exact read_argc_w inp Hva Hve rsp rrnd Hsp_hi
      · exact bytes_le_n_to_le_8 _
    step_simpl
    stepiv SF_1119c SD_1119c (Z_to_bv 64 (bv_unsigned rsp + 8))
      (getr_resolve; regupd_resolve; sp_norm; rfl)
    stepiv SF_111a0 SD_111a0 (v_slli (argcN inp) 3)
      (getr_resolve; regupd_resolve; rfl)
    stepiv SF_111a4 SD_111a4
      (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp) 3))
      (getr_resolve; regupd_resolve; rfl)
    stepiv SF_111a8 SD_111a8 (envp_val inp rsp)
      (getr_resolve; regupd_resolve; exact envp_val_eq inp Hva rsp Hsp_lo Hsp_hi)
    stepi SF_111ac SD_111ac
    stepiv SF_111b0 SD_111b0 (0x13000 : word) (getr_resolve; regupd_resolve; bveq)
    stepsd SF_111b4 SD_111b4 (0x13000 : word) (envp_val inp rsp)
      (getr_resolve; regupd_resolve; rfl) (apply source_store_ok <;> decide +kernel)
    stepj SF_111b8 SD_111b8
    stepiv SF_11000 SD_11000 (Z_to_bv 64 (bv_unsigned rsp - 48))
      (getr_resolve; regupd_resolve; sp_norm; rfl)
    stepsd SF_11004 SD_11004 (Z_to_bv 64 (bv_unsigned rsp - 24)) (Z_to_bv 64 0)
      (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
    stepsd SF_11008 SD_11008 (Z_to_bv 64 (bv_unsigned rsp - 8)) ((0x111bc : word))
      (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
    stepsd SF_1100c SD_1100c (Z_to_bv 64 (bv_unsigned rsp - 16)) (Z_to_bv 64 0)
      (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
    stepsd SF_11010 SD_11010 (Z_to_bv 64 (bv_unsigned rsp - 32)) (Z_to_bv 64 0)
      (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
    stepsd SF_11014 SD_11014 (Z_to_bv 64 (bv_unsigned rsp - 40)) (Z_to_bv 64 0)
      (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
    stepsd SF_11018 SD_11018 (Z_to_bv 64 (bv_unsigned rsp - 48)) (Z_to_bv 64 0)
      (getr_resolve; regupd_resolve; bveq) (solve_store_ok)
    stepiv SF_1101c SD_1101c (Z_to_bv 64 1) (getr_resolve; bveq)
    apply msteps.mst_step _ _ _ rfl
    · apply step_bge_ft (hf := SF_11020) (he := rfl) (hd := SD_11020)
      getr_resolve; regupd_resolve
      rw [c_lts_small _ _ (by decide +kernel) (by omega), bv_ltu_Z]
      apply decide_eq_true
      change 1 < bv_unsigned (argcN inp)
      omega
    norm_pc
    stepiv SF_11024 SD_11024 (Z_to_bv 64 (bv_unsigned rsp + 8))
      (getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0])
    stepiv SF_11028 SD_11028 (argcN inp)
      (getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0])
    stepiv SF_1102c SD_1102c (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_11030 SD_11030 (Z_to_bv 64 1) (getr_resolve; regupd_resolve; bveq)
    exact msteps.mst_refl _
  all_goals regupd_resolve; rfl

set_option maxHeartbeats 2000000 in
theorem source_length (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (f i : Nat) (regs : bvmap 5 word) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length)
    (Hf : inp.in_argv.length - i ≤ f)
    (H18 : reg_get regs 18 = argcN inp)
    (H19 : reg_get regs 19 = Z_to_bv 64 (bv_unsigned rsp + 8))
    (H20 : reg_get regs 20 = Z_to_bv 64 1)
    (H9 : reg_get regs 9 = nat_to_word i)
    (H8 : reg_get regs 8 = nat_to_word (join1 (inp.in_argv.tail.take (i - 1))).length) :
    ∃ regs', (∀ r : reg, r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 8 = nat_to_word (join1 inp.in_argv.tail).length ∧
      msteps source_segs (mkst regs 0x11034 (fmem inp rsp rrnd) rrom)
        (mkst regs' 0x1105c (fmem inp rsp rrnd) rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  induction f generalizing i regs with
  | zero => omega
  | succ f IH =>
    have HiZ := iN_le inp Hva i (by omega)
    have HSiZ := iN_le inp Hva (i + 1) (by omega)
    have HniB := valid_argv_str_len inp.in_argv i Hva Hi
    have Haccb := acc_bound inp Hva (i - 1)
    let regs1 := regupd regs 15 (Z_to_bv 64 (8 * (i : Int)))
    have E1 : RiscvSemantics.step source_segs (mkst regs 0x11034 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst regs1 0x11038 (fmem inp rsp rrnd) rrom) := by
      apply step_slli_at (hf := SF_11034) (he := rfl) (hd := SD_11034) (hrd := rfl)
      getr_resolve; imm_norm; rw [H9]; exact v_slli3_nat i HiZ
    let regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (i : Int)))
    have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11038 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst regs2 0x1103c (fmem inp rsp rrnd) rrom) := by
      apply step_add_at (hf := SF_11038) (he := rfl) (hd := SD_11038) (hrd := rfl)
      dsimp only [regs1]; getr_resolve; rw [H19]
      unfold v_add
      u_norm
      congr 1 <;> omega
    let regs3 := regupd regs2 10 (sptr inp rsp i)
    have E3 : RiscvSemantics.step source_segs (mkst regs2 0x1103c (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst regs3 0x11040 (fmem inp rsp rrnd) rrom) := by
      rw [step_ld _ _ _ _ _ _ _ _ _ (word_le8 (sptr inp rsp i)) (sptr inp rsp i)
        SF_1103c rfl SD_1103c]
      · rfl
      · dsimp only [regs2]; getr_resolve; imm_norm; rw [v_addi_0]
        exact read_arg_ptr_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi i Hi
      · exact bytes_le_n_to_le_8 _
    let regs4 := regupd regs3 1 (0x11044 : word)
    have E4 : RiscvSemantics.step source_segs (mkst regs3 0x11040 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst regs4 0x111e8 (fmem inp rsp rrnd) rrom) := by
      rw [step_jal_link _ _ _ _ _ _ _ _ SF_11040 rfl SD_11040]
      rfl
    obtain ⟨regs5, Hag5, H10_5, Hms5⟩ := source_strlen inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
      i Hi (fmem inp rsp rrnd) (fmem_ok inp rsp rrnd) (0x11044 : word) (by bveq) regs4
      (by dsimp only [regs4, regs3]; regupd_resolve; rfl)
      (by dsimp only [regs4]; exact regupd_same _ _ _)
    have Hpres5 : ∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg_get regs5 r = reg_get regs r := by
      intro r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15
      rw [Hag5 r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15]
      dsimp only [regs4, regs3, regs2, regs1]
      repeat rw [regupd_other _ _ _ _ (by assumption)]
    have H8_5 : reg_get regs5 8 = nat_to_word (join1 (inp.in_argv.tail.take (i - 1))).length := by
      rw [Hpres5 _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
        (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H8
    let regs6 := regupd regs5 8 (nat_to_word
      ((join1 (inp.in_argv.tail.take (i - 1))).length + (inp.in_argv.getD i []).length))
    have E6 : RiscvSemantics.step source_segs (mkst regs5 0x11044 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst regs6 0x11048 (fmem inp rsp rrnd) rrom) := by
      apply step_add_at (hf := SF_11044) (he := rfl) (hd := SD_11044) (hrd := rfl)
      getr_resolve; rw [H8_5, H10_5, v_add_word, nat_to_word_merge]
    have Hpres6 : ∀ r : reg, r ≠ 8 → r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg_get regs6 r = reg_get regs r := by
      intro r Ha Hb Hc Hd He Hf' Hg Hh
      dsimp only [regs6]
      rw [regupd_other _ _ _ _ Ha]
      exact Hpres5 r Hb Hc Hd He Hf' Hg Hh
    have H9_6 : reg_get regs6 9 = nat_to_word i := by
      rw [Hpres6 _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
        (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H9
    have H20_6 : reg_get regs6 20 = Z_to_bv 64 1 := by
      rw [Hpres6 _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
        (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H20
    have H18_6 : reg_get regs6 18 = argcN inp := by
      rw [Hpres6 _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
        (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H18
    have H19_6 : reg_get regs6 19 = Z_to_bv 64 (bv_unsigned rsp + 8) := by
      rw [Hpres6 _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
        (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H19
    let sep : Nat := if i == 1 then 0 else 1
    let newacc := nat_to_word
      ((join1 (inp.in_argv.tail.take (i - 1))).length + (inp.in_argv.getD i []).length + sep)
    have Hnew : nat_to_word (join1 (inp.in_argv.tail.take i)).length = newacc := by
      unfold newacc sep
      rw [jpre_step inp i H1 (by rw [length_tl_av]; omega)]
    have HB : ∃ regsB, (∀ r : reg, r ≠ 8 → reg_get regsB r = reg_get regs6 r) ∧
        reg_get regsB 8 = newacc ∧
        msteps source_segs (mkst regs6 0x11048 (fmem inp rsp rrnd) rrom)
          (mkst regsB 0x11050 (fmem inp rsp rrnd) rrom) := by
      by_cases Hi1 : i = 1
      · refine ⟨regs6, fun _ _ => rfl, ?_, ?_⟩
        · dsimp only [regs6]; rw [regupd_same]
          unfold newacc sep
          rw [Hi1]
          simp only [beq_self_eq_true, ite_true, Nat.add_zero]
        · apply msteps.mst_step _ _ _ rfl
          · apply step_beq_tk (hf := SF_11048) (he := rfl) (hd := SD_11048)
            change c_eq (reg_get regs6 9) (reg_get regs6 20) = true
            rw [H9_6, H20_6, Hi1]
            exact c_eq_refl _
          norm_pc
          exact msteps.mst_refl _
      · refine ⟨regupd regs6 8 newacc, ?_, regupd_same _ _ _, ?_⟩
        · intro r Hr8; exact regupd_other _ _ _ _ Hr8
        · apply msteps.mst_step _ _ _ rfl
          · apply step_beq_ft (hf := SF_11048) (he := rfl) (hd := SD_11048)
            change c_eq (reg_get regs6 9) (reg_get regs6 20) = false
            rw [H9_6, H20_6]
            apply c_eq_neq
            rw [u_ntw i (by omega)]
            change (i : Int) ≠ 1
            omega
          norm_pc
          stepiv SF_1104c SD_1104c newacc
            (getr_resolve; imm_norm; rw [v_addi_Sj _ (by omega)]
             unfold newacc sep
             rw [ite_eq_right (by simpa only [beq_iff_eq] using Hi1)])
          exact msteps.mst_refl _
    obtain ⟨regsB, HagB, H8B, HmsB⟩ := HB
    have H9B : reg_get regsB 9 = nat_to_word i := by
      rw [HagB _ (by reg_neq_tac)]; exact H9_6
    have H18B : reg_get regsB 18 = argcN inp := by
      rw [HagB _ (by reg_neq_tac)]; exact H18_6
    have H19B : reg_get regsB 19 = Z_to_bv 64 (bv_unsigned rsp + 8) := by
      rw [HagB _ (by reg_neq_tac)]; exact H19_6
    have H20B : reg_get regsB 20 = Z_to_bv 64 1 := by
      rw [HagB _ (by reg_neq_tac)]; exact H20_6
    let regsC := regupd regsB 9 (nat_to_word (i + 1))
    have EC : RiscvSemantics.step source_segs (mkst regsB 0x11050 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst regsC 0x11054 (fmem inp rsp rrnd) rrom) := by
      apply step_addi_at (hf := SF_11050) (he := rfl) (hd := SD_11050) (hrd := rfl)
      getr_resolve; imm_norm; rw [H9B, v_addi_Sj _ (by omega)]
    let regsD := regupd regsC 15 (nat_to_word (i + 1))
    have ED : RiscvSemantics.step source_segs (mkst regsC 0x11054 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst regsD 0x11058 (fmem inp rsp rrnd) rrom) := by
      apply step_addiw_at (hf := SF_11054) (he := rfl) (hd := SD_11054) (hrd := rfl)
      dsimp only [regsC]; getr_resolve; imm_norm
      exact v_addiw_id _ (by rw [u_ntw _ (by omega)]; omega)
    have H15D : reg_get regsD 15 = nat_to_word (i + 1) := regupd_same _ _ _
    have H18D : reg_get regsD 18 = argcN inp := by
      dsimp only [regsD, regsC]; regupd_resolve; exact H18B
    have H8D : reg_get regsD 8 = newacc := by
      dsimp only [regsD, regsC]; regupd_resolve; exact H8B
    by_cases Hlti : i + 1 < inp.in_argv.length
    · have Eloop : RiscvSemantics.step source_segs (mkst regsD 0x11058 (fmem inp rsp rrnd) rrom) =
          MachineOk (mkst regsD 0x11034 (fmem inp rsp rrnd) rrom) := by
        apply step_blt_tk (Hf := SF_11058) (He := rfl) (Hd := SD_11058)
        change c_lts (reg_get regsD 15) (reg_get regsD 18) = _
        rw [H15D, H18D]
        rw [c_lts_ltb _ _ (by rw [u_ntw _ (by omega)]; omega)
          (by rw [u_argcN inp Hva]; omega), u_ntw _ (by omega), u_argcN inp Hva]
        exact decide_eq_true (by omega)
      obtain ⟨regs', Hag', H8', Hms'⟩ := IH (i + 1) regsD (by omega) Hlti (by omega) H18D
        (by dsimp only [regsD, regsC]; regupd_resolve; exact H19B)
        (by dsimp only [regsD, regsC]; regupd_resolve; exact H20B)
        (by dsimp only [regsD, regsC]; regupd_resolve; rfl)
        (by rw [H8D, ← Hnew]; simp only [Nat.add_one_sub_one])
      refine ⟨regs', ?_, H8', ?_⟩
      · intro r Ha Hb Hc Hd He Hf' Hg Hh Hj'
        rw [Hag' r Ha Hb Hc Hd He Hf' Hg Hh Hj']
        dsimp only [regsD, regsC]
        rw [regupd_other _ _ _ _ Hj', regupd_other _ _ _ _ Hc, HagB r Hb]
        exact Hpres6 r Hb Ha Hd He Hf' Hg Hh Hj'
      · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2
          (msteps.mst_step _ _ _ rfl E3 (msteps.mst_step _ _ _ rfl E4
          (msteps_trans _ _ _ _ Hms5 (msteps.mst_step _ _ _ rfl E6
          (msteps_trans _ _ _ _ HmsB (msteps.mst_step _ _ _ rfl EC
          (msteps.mst_step _ _ _ rfl ED (msteps.mst_step _ _ _ rfl Eloop Hms')))))))))
    · have Hieq : i = inp.in_argv.length - 1 := by omega
      have Efall : RiscvSemantics.step source_segs (mkst regsD 0x11058 (fmem inp rsp rrnd) rrom) =
          MachineOk (mkst regsD 0x1105c (fmem inp rsp rrnd) rrom) := by
        apply step_blt_ft (hf := SF_11058) (he := rfl) (hd := SD_11058)
        change c_lts (reg_get regsD 15) (reg_get regsD 18) = _
        rw [H15D, H18D]
        rw [c_lts_ltb _ _ (by rw [u_ntw _ (by omega)]; omega)
          (by rw [u_argcN inp Hva]; omega), u_ntw _ (by omega), u_argcN inp Hva]
        exact decide_eq_false (by omega)
      refine ⟨regsD, ?_, ?_, ?_⟩
      · intro r Ha Hb Hc Hd He Hf' Hg Hh Hj'
        dsimp only [regsD, regsC]
        rw [regupd_other _ _ _ _ Hj', regupd_other _ _ _ _ Hc, HagB r Hb]
        exact Hpres6 r Hb Ha Hd He Hf' Hg Hh Hj'
      · rw [H8D, ← Hnew, Hieq, ← length_tl_av, List.take_length]
      · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2
          (msteps.mst_step _ _ _ rfl E3 (msteps.mst_step _ _ _ rfl E4
          (msteps_trans _ _ _ _ Hms5 (msteps.mst_step _ _ _ rfl E6
          (msteps_trans _ _ _ _ HmsB (msteps.mst_step _ _ _ rfl EC
          (msteps.mst_step _ _ _ rfl ED (msteps.mst_step _ _ _ rfl Efall (msteps.mst_refl _))))))))))

theorem source_after_length (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) :
    ∃ regs2, reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs2 18 = argcN inp ∧ reg_get regs2 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
      reg_get regs2 8 = nat_to_word (join1 inp.in_argv.tail).length ∧
      msteps source_segs
        (init_machine_state source_segs 0x11190 source_phdrs rsp rrnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs2 0x1105c (fmem inp rsp rrnd) rrom) := by
  obtain ⟨regs1, H2, H18, H19, H20, H9, H8, Hms1⟩ := source_to_loop inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
  obtain ⟨regs2, Hag, H8', Hms2⟩ := source_length inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
    inp.in_argv.length 1 regs1 (by omega) (by omega) (by omega) H18 H19 H20 H9
    (by rw [H8]; simp only [show (1 - 1 : Nat) = 0 by rfl, List.take_zero, join1, List.length_nil]; rfl)
  refine ⟨regs2, ?_, ?_, ?_, H8', msteps_trans _ _ _ _ Hms1 Hms2⟩
  · rw [Hag _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
      (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]
    exact H2
  · rw [Hag _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
      (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]
    exact H18
  · rw [Hag _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
      (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]
    exact H19

theorem source_wexit_cap (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (Hcap : 65536 < bv_unsigned (tot inp)) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11190 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 3) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hg1 := tot_ge1 inp Hva Hge2
  have Htb := totN_bound inp Hva
  have Hjl := join1_tl_len_nat inp Hge2
  have Htn := totn_bound inp Hva
  obtain ⟨regs2, H2, H18, H19, H8, Hms⟩ := source_after_length inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
  apply msteps_to_wexit _ _ _ _ _ Hms
  stepiv SF_1105c SD_1105c (tot inp)
    (getr_resolve; imm_norm; rw [H8, v_addi_Sj _ (by omega)]; exact S_join1_tot inp Hge2)
  stepiv SF_11060 SD_11060 (Z_to_bv 64 0x10000) (bveq)
  stepiv SF_11064 SD_11064 (Z_to_bv 64 3) (getr_resolve; bveq)
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_bltu_tk (Hf := SF_11068) (He := rfl) (Hd := SD_11068)
    getr_resolve; regupd_resolve
    rw [c_ltu_ltb]
    apply decide_eq_true
    exact Hcap
  norm_pc
  apply source_epilogue rsp Hsp_lo Hsp_hi
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · decide +kernel
  · exact read_slot_ra inp rsp rrnd Hsp_lo Hsp_hi
  · exact read_slot_0 inp rsp rrnd Hsp_lo Hsp_hi

theorem source_exit4 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (regs : bvmap 5 word) (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48)) :
    to_wexit source_segs (mkst regs 0x11094 (fmem inp rsp rrnd) rrom) [] (Z_to_bv 64 4) := by
  stepiv SF_11094 SD_11094 (Z_to_bv 64 4) (getr_resolve; bveq)
  apply source_epilogue rsp Hsp_lo Hsp_hi
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · decide +kernel
  · exact read_slot_ra inp rsp rrnd Hsp_lo Hsp_hi
  · exact read_slot_0 inp rsp rrnd Hsp_lo Hsp_hi

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem source_copy_inner (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (rsp : word) (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
    (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (Hge2 : 2 ≤ inp.in_argv.length)
    (base_mem : word → Option byte) (r p : word) (s «prefix» : List byte)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + bv_unsigned (tot inp) ≤ bv_unsigned rsp - stack_max_size)
    (_Hfree : region_free (segments_reserved source_segs) r (tot inp) = true)
    (Hnz : Z_to_bv 8 0 ∉ s) (Hpsb : «prefix».length + s.length + 1 ≤ totn inp)
    (Hp : bv_unsigned rsp ≤ bv_unsigned p) (Hpbnd : bv_unsigned p + (s.length : Int) + 1 < 2 ^ 64)
    (Hrd : ∀ j, j ≤ s.length → rdn source_segs base_mem (p + nat_to_word j) 1 = some [byte_at s j])
    (Hgok : store_grant_ok source_segs base_mem r (tot inp))
    (d j : Nat) (regs : bvmap 5 word) (Hjd : j + d = s.length)
    (H6 : reg_get regs 6 = p) (H9 : reg_get regs 9 = r)
    (H12 : reg_get regs 12 = nat_to_word «prefix».length)
    (H15 : reg_get regs 15 = nat_to_word («prefix».length + j)) :
    ∃ regs', (∀ x : reg, x ≠ 8 → x ≠ 10 → x ≠ 13 → x ≠ 15 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 8 = nat_to_word («prefix».length + s.length + 1) ∧
      reg_get regs' 13 = r + nat_to_word («prefix».length + s.length) ∧
      reg_get regs' 15 = nat_to_word («prefix».length + s.length) ∧
      msteps source_segs
        (mkst regs 0x1111c (wbytes base_mem r («prefix» ++ s.take j)) rrom)
        (mkst regs' 0x11134 (wbytes base_mem r («prefix» ++ s)) rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hsms := stack_max_size_val
  have Htg1 := tot_ge1 inp Hva Hge2
  have Htb := totN_bound inp Hva
  have HtbZ := totn_bound inp Hva
  have Hut := u_tot inp Hva
  induction d generalizing j regs with
  | zero =>
    have Hj : j = s.length := by omega
    let b := byte_at s j
    have Hb0 : b = Z_to_bv 8 0 := by dsimp only [b]; rw [Hj, byte_at_len]
    let M := wbytes base_mem r («prefix» ++ s.take j)
    have HlenF : («prefix» ++ s.take j).length = «prefix».length + j := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
    let regs1 := regupd regs 13 (nat_to_word j)
    have E1 : RiscvSemantics.step source_segs (mkst regs 0x1111c M rrom) =
        MachineOk (mkst regs1 0x11120 M rrom) := by
      apply step_sub_at (hf := SF_1111c) (he := rfl) (hd := SD_1111c) (hrd := rfl)
      getr_resolve; rw [H15, H12, ntw_sub _ _ (by omega) (by omega)]
      exact congrArg nat_to_word (by omega)
    let regs2 := regupd regs1 13 (p + nat_to_word j)
    have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11120 M rrom) =
        MachineOk (mkst regs2 0x11124 M rrom) := by
      apply step_add_at (hf := SF_11120) (he := rfl) (hd := SD_11120) (hrd := rfl)
      dsimp only [regs1]; getr_resolve; rw [H6, v_add_word]
    let regs3 := regupd regs2 10 (Z_to_bv 64 (bv_unsigned b))
    have E3 : RiscvSemantics.step source_segs (mkst regs2 0x11124 M rrom) =
        MachineOk (mkst regs3 0x11128 M rrom) := by
      rw [step_lbu _ _ _ _ _ _ _ _ _ b SF_11124 rfl SD_11124]
      · rfl
      · dsimp only [regs2]; getr_resolve; imm_norm; rw [v_addi_0]
        dsimp only [M]
        rw [rdn_wbytes_disjoint _ _ _ _ _ _
          (by rw [HlenF, word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
        exact Hrd j (by omega)
    let regs4 := regupd regs3 8 (nat_to_word («prefix».length + j + 1))
    have E4 : RiscvSemantics.step source_segs (mkst regs3 0x11128 M rrom) =
        MachineOk (mkst regs4 0x1112c M rrom) := by
      apply step_addi_at (hf := SF_11128) (he := rfl) (hd := SD_11128) (hrd := rfl)
      dsimp only [regs3, regs2, regs1]; getr_resolve; imm_norm; rw [H15]
      exact v_addi_Sj _ (by omega)
    let regs5 := regupd regs4 13 (r + nat_to_word («prefix».length + j))
    have E5 : RiscvSemantics.step source_segs (mkst regs4 0x1112c M rrom) =
        MachineOk (mkst regs5 0x11130 M rrom) := by
      apply step_add_at (hf := SF_1112c) (he := rfl) (hd := SD_1112c) (hrd := rfl)
      dsimp only [regs4, regs3, regs2, regs1]; getr_resolve
      rw [H15, H9, v_add_word, word_add_comm]
    have E6 : RiscvSemantics.step source_segs (mkst regs5 0x11130 M rrom) =
        MachineOk (mkst regs5 0x11134 M rrom) := by
      apply step_bne_ft (hf := SF_11130) (he := rfl) (hd := SD_11130)
      dsimp only [regs5, regs4, regs3]; getr_resolve; rw [Hb0]; exact c_eq_0_true
    refine ⟨regs5, ?_, ?_, ?_, ?_, ?_⟩
    · intro x Hx8 Hx10 Hx13 _
      dsimp only [regs5, regs4, regs3, regs2, regs1]
      repeat rw [regupd_other _ _ _ _ (by assumption)]
    · dsimp only [regs5, regs4]; regupd_resolve; rw [Hj]
    · dsimp only [regs5]; regupd_resolve; rw [Hj]
    · dsimp only [regs5, regs4, regs3, regs2, regs1]; regupd_resolve; rw [H15, Hj]
    · apply msteps.mst_step _ _ _ rfl E1
      apply msteps.mst_step _ _ _ rfl E2
      apply msteps.mst_step _ _ _ rfl E3
      apply msteps.mst_step _ _ _ rfl E4
      apply msteps.mst_step _ _ _ rfl E5
      apply msteps.mst_step _ _ _ rfl E6
      dsimp only [M]
      rw [Hj, List.take_length]
      exact msteps.mst_refl _
  | succ d IH =>
    have Hjlt : j < s.length := by omega
    let b := byte_at s j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hnz Hjlt
    let M := wbytes base_mem r («prefix» ++ s.take j)
    have HlenF : («prefix» ++ s.take j).length = «prefix».length + j := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
    let regs1 := regupd regs 13 (nat_to_word j)
    have E1 : RiscvSemantics.step source_segs (mkst regs 0x1111c M rrom) =
        MachineOk (mkst regs1 0x11120 M rrom) := by
      apply step_sub_at (hf := SF_1111c) (he := rfl) (hd := SD_1111c) (hrd := rfl)
      getr_resolve; rw [H15, H12, ntw_sub _ _ (by omega) (by omega)]
      exact congrArg nat_to_word (by omega)
    let regs2 := regupd regs1 13 (p + nat_to_word j)
    have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11120 M rrom) =
        MachineOk (mkst regs2 0x11124 M rrom) := by
      apply step_add_at (hf := SF_11120) (he := rfl) (hd := SD_11120) (hrd := rfl)
      dsimp only [regs1]; getr_resolve; rw [H6, v_add_word]
    let regs3 := regupd regs2 10 (Z_to_bv 64 (bv_unsigned b))
    have E3 : RiscvSemantics.step source_segs (mkst regs2 0x11124 M rrom) =
        MachineOk (mkst regs3 0x11128 M rrom) := by
      rw [step_lbu _ _ _ _ _ _ _ _ _ b SF_11124 rfl SD_11124]
      · rfl
      · dsimp only [regs2]; getr_resolve; imm_norm; rw [v_addi_0]
        dsimp only [M]
        rw [rdn_wbytes_disjoint _ _ _ _ _ _
          (by rw [HlenF, word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
        exact Hrd j (by omega)
    let regs4 := regupd regs3 8 (nat_to_word («prefix».length + j + 1))
    have E4 : RiscvSemantics.step source_segs (mkst regs3 0x11128 M rrom) =
        MachineOk (mkst regs4 0x1112c M rrom) := by
      apply step_addi_at (hf := SF_11128) (he := rfl) (hd := SD_11128) (hrd := rfl)
      dsimp only [regs3, regs2, regs1]; getr_resolve; imm_norm; rw [H15]
      exact v_addi_Sj _ (by omega)
    let regs5 := regupd regs4 13 (r + nat_to_word («prefix».length + j))
    have E5 : RiscvSemantics.step source_segs (mkst regs4 0x1112c M rrom) =
        MachineOk (mkst regs5 0x11130 M rrom) := by
      apply step_add_at (hf := SF_1112c) (he := rfl) (hd := SD_1112c) (hrd := rfl)
      dsimp only [regs4, regs3, regs2, regs1]; getr_resolve
      rw [H15, H9, v_add_word, word_add_comm]
    have E6 : RiscvSemantics.step source_segs (mkst regs5 0x11130 M rrom) =
        MachineOk (mkst regs5 0x11154 M rrom) := by
      apply step_bne_tk (hf := SF_11130) (he := rfl) (hd := SD_11130)
      dsimp only [regs5, regs4, regs3]; getr_resolve
      apply c_eq_0_false
      rw [u_zext8]
      exact byte_nz_u b Hbnz
    let Mnext := wbytes base_mem r («prefix» ++ s.take (j + 1))
    have E7 : RiscvSemantics.step source_segs (mkst regs5 0x11154 M rrom) =
        MachineOk (mkst regs5 0x11158 Mnext rrom) := by
      rw [step_sb_atv _ _ _ _ _ _ _ _ _ (r + nat_to_word («prefix» ++ s.take j).length) b
        SF_11154 rfl SD_11154]
      · have He : «prefix» ++ s.take (j + 1) = («prefix» ++ s.take j) ++ [b] := by
          rw [firstn_S_nth _ s j (Z_to_bv 8 0) Hjlt, List.append_assoc]
          dsimp only [b]
          rw [nth_lt_byte_at s j Hjlt]
        dsimp only [Mnext, M]
        rw [He, wbytes_snoc]
        rfl
      · dsimp only [regs5]; getr_resolve; imm_norm; rw [v_addi_0, HlenF]
      · dsimp only [regs5, regs4, regs3]; getr_resolve; rfl
      · dsimp only [M]
        store_ok_peel
        apply Hgok
        all_goals rw [HlenF, word_add_nat]; u_norm; omega
    let regs6 := regupd regs5 15 (nat_to_word («prefix».length + (j + 1)))
    have E8 : RiscvSemantics.step source_segs (mkst regs5 0x11158 Mnext rrom) =
        MachineOk (mkst regs6 0x1115c Mnext rrom) := by
      apply step_addi_at (hf := SF_11158) (he := rfl) (hd := SD_11158) (hrd := rfl)
      dsimp only [regs5, regs4]; getr_resolve; imm_norm
      rw [v_addi_0]
      congr 1 <;> omega
    have E9 : RiscvSemantics.step source_segs (mkst regs6 0x1115c Mnext rrom) =
        MachineOk (mkst regs6 0x1111c Mnext rrom) := by
      exact step_jal_x0 _ _ _ _ _ _ _ SF_1115c rfl SD_1115c
    obtain ⟨regs', Hag', H8f, H13f, H15f, Hms'⟩ := IH (j + 1) regs6 (by omega)
      (by dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]; regupd_resolve; exact H6)
      (by dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]; regupd_resolve; exact H9)
      (by dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]; regupd_resolve; exact H12)
      (by dsimp only [regs6]; exact regupd_same _ _ _)
    refine ⟨regs', ?_, H8f, H13f, H15f, ?_⟩
    · intro x Hx8 Hx10 Hx13 Hx15
      rw [Hag' x Hx8 Hx10 Hx13 Hx15]
      dsimp only [regs6, regs5, regs4, regs3, regs2, regs1]
      repeat rw [regupd_other _ _ _ _ (by assumption)]
    · exact msteps.mst_step _ _ _ rfl E1 (msteps.mst_step _ _ _ rfl E2
        (msteps.mst_step _ _ _ rfl E3 (msteps.mst_step _ _ _ rfl E4
        (msteps.mst_step _ _ _ rfl E5 (msteps.mst_step _ _ _ rfl E6
        (msteps.mst_step _ _ _ rfl E7 (msteps.mst_step _ _ _ rfl E8
        (msteps.mst_step _ _ _ rfl E9 Hms'))))))))

/-- Length of the wjoin prefix at outer index i (args 1..i-1 done,
including the trailing separator), and its join1 companion without it. -/
def pbW (inp : ProcInput) (i : Nat) : Nat := (wjoin (inp.in_argv.tail.take (i - 1))).length

def pbJ (inp : ProcInput) (i : Nat) : Nat := (join1 (inp.in_argv.tail.take (i - 1))).length

theorem pbW_1 (inp : ProcInput) : pbW inp 1 = 0 := by
  simp only [pbW, show (1 - 1 : Nat) = 0 by rfl, List.take_zero, wjoin, List.length_nil]

theorem pbJ_1 (inp : ProcInput) : pbJ inp 1 = 0 := by
  simp only [pbJ, show (1 - 1 : Nat) = 0 by rfl, List.take_zero, join1, List.length_nil]

theorem pbW_le (inp : ProcInput) (i : Nat) : pbW inp i ≤ totn inp := by
  unfold pbW totn
  rw [length_wjoin]
  have He := tab_app (inp.in_argv.tail.take (i - 1)) (inp.in_argv.tail.drop (i - 1))
  rw [List.take_append_drop] at He
  omega

theorem pbW_pbJ (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) (i : Nat)
    (H2 : 2 ≤ i) (_Hi : i ≤ inp.in_argv.length) : pbW inp i = pbJ inp i + 1 := by
  unfold pbW pbJ
  rw [wjoin_join1 _ (firstn_nonnil _ _ (by omega) (tl_nonnil inp Hge2)), List.length_append]
  rfl

theorem pbJ_le (inp : ProcInput) (i : Nat) : pbJ inp i ≤ pbW inp i := by
  unfold pbW pbJ
  cases H : inp.in_argv.tail.take (i - 1) with
  | nil => simp only [join1, wjoin, List.length_nil, Nat.le_refl]
  | cons x l =>
    rw [wjoin_join1 _ (List.cons_ne_nil _ _), List.length_append]
    omega

theorem pbase_bound (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) :
    pbW inp i + (inp.in_argv.getD i []).length + 1 ≤ totn inp := by
  unfold pbW totn
  rw [length_wjoin]
  have Hstep : total_arg_bytes_nat (inp.in_argv.tail.take (i - 1)) +
      (inp.in_argv.getD i []).length + 1 = total_arg_bytes_nat (inp.in_argv.tail.take i) := by
    have He : inp.in_argv.tail.take i = inp.in_argv.tail.take (i - 1) ++
        [inp.in_argv.tail.getD (i - 1) []] := by
      calc
        _ = inp.in_argv.tail.take ((i - 1) + 1) := congrArg (fun n => inp.in_argv.tail.take n) (by omega)
        _ = _ := firstn_S_nth _ _ _ [] (by rw [length_tl_av]; omega)
    rw [He, tab_app, nth_tl, show i - 1 + 1 = i by omega]
    simp only [total_arg_bytes_nat, List.foldr_cons, List.foldr_nil]
    omega
  have He := tab_app (inp.in_argv.tail.take i) (inp.in_argv.tail.drop i)
  rw [List.take_append_drop] at He
  omega

theorem wjoin_firstn_step (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) :
    wjoin (inp.in_argv.tail.take i) =
      wjoin (inp.in_argv.tail.take (i - 1)) ++ inp.in_argv.getD i [] ++ [Z_to_bv 8 32] := by
  have He : inp.in_argv.tail.take i = inp.in_argv.tail.take (i - 1) ++
      [inp.in_argv.tail.getD (i - 1) []] := by
    calc
      _ = inp.in_argv.tail.take ((i - 1) + 1) := congrArg (fun n => inp.in_argv.tail.take n) (by omega)
      _ = _ := firstn_S_nth _ _ _ [] (by rw [length_tl_av]; omega)
  rw [He, nth_tl, show i - 1 + 1 = i by omega]
  generalize inp.in_argv.tail.take (i - 1) = l
  induction l with
  | nil => simp only [List.nil_append, wjoin]
  | cons a l IH => simp only [List.cons_append, wjoin, IH, List.append_assoc]

/-- The join1 prefix after arg i is the wjoin prefix before it plus the arg itself. -/
theorem join1_firstn_step (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) :
    join1 (inp.in_argv.tail.take i) = wjoin (inp.in_argv.tail.take (i - 1)) ++ inp.in_argv.getD i [] := by
  have He : inp.in_argv.tail.take i = inp.in_argv.tail.take (i - 1) ++
      [inp.in_argv.tail.getD (i - 1) []] := by
    calc
      _ = inp.in_argv.tail.take ((i - 1) + 1) := congrArg (fun n => inp.in_argv.tail.take n) (by omega)
      _ = _ := firstn_S_nth _ _ _ [] (by rw [length_tl_av]; omega)
  rw [He, join1_snoc, nth_tl, show i - 1 + 1 = i by omega]

theorem join1_tl_split (inp : ProcInput) (i : Nat) (HSi : i + 1 = inp.in_argv.length) (H1 : 1 ≤ i) :
    join1 inp.in_argv.tail = wjoin (inp.in_argv.tail.take (i - 1)) ++ inp.in_argv.getD i [] := by
  have Htl : i = inp.in_argv.tail.length := by rw [length_tl_av]; omega
  have H := join1_firstn_step inp i H1 (by omega)
  rw [Htl, List.take_length] at H
  rw [Htl]
  exact H

theorem pbW_step (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) :
    pbW inp (i + 1) = pbW inp i + (inp.in_argv.getD i []).length + 1 := by
  unfold pbW
  rw [Nat.add_one_sub_one, wjoin_firstn_step inp i H1 Hi]
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem pbJ_S (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) :
    pbJ inp (i + 1) = pbW inp i + (inp.in_argv.getD i []).length := by
  unfold pbJ pbW
  rw [Nat.add_one_sub_one, join1_firstn_step inp i H1 Hi, List.length_append]

theorem pbW_last (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) (i : Nat)
    (HSi : i + 1 = inp.in_argv.length) (H1 : 1 ≤ i) :
    pbW inp i + (inp.in_argv.getD i []).length = totn inp - 1 := by
  have Hjl := join1_tl_len_nat inp Hge2
  rw [join1_tl_split inp i HSi H1, List.length_append] at Hjl
  exact Hjl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem source_copy_outer (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (r grant : word)
    (Hgrant : bv_unsigned (tot inp) ≤ bv_unsigned grant)
    (Hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned rsp - stack_max_size)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + bv_unsigned (tot inp) ≤ bv_unsigned rsp - stack_max_size)
    (Hfree : region_free (segments_reserved source_segs) r (tot inp) = true)
    (f i : Nat) (regs : bvmap 5 word) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length)
    (Hf : inp.in_argv.length - i ≤ f)
    (H9 : reg_get regs 9 = r) (H16 : reg_get regs 16 = Z_to_bv 64 1)
    (H17 : reg_get regs 17 = Z_to_bv 64 32) (H14 : reg_get regs 14 = nat_to_word i)
    (H15 : reg_get regs 15 = nat_to_word (pbJ inp i))
    (H18 : reg_get regs 18 = argcN inp)
    (H19 : reg_get regs 19 = Z_to_bv 64 (bv_unsigned rsp + 8)) :
    ∃ regs', (∀ x : reg, x ≠ 6 → x ≠ 8 → x ≠ 10 → x ≠ 12 → x ≠ 13 → x ≠ 14 → x ≠ 15 →
        reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 8 = tot inp ∧ reg_get regs' 13 = r + nat_to_word (totn inp - 1) ∧
      msteps source_segs
        (mkst regs 0x110f8
          (wbytes (zmem (fmem inp rsp rrnd) r grant) r (join1 (inp.in_argv.tail.take (i - 1)))) rrom)
        (mkst regs' 0x11140 (wbytes (zmem (fmem inp rsp rrnd) r grant) r (join1 inp.in_argv.tail)) rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hsms := stack_max_size_val
  have Htg1 := tot_ge1 inp Hva Hge2
  have Htb := totN_bound inp Hva
  have HtbZ := totn_bound inp Hva
  have Htgn1 := totn_ge1 inp Hge2
  have Hut := u_tot inp Hva
  have HargcLe := valid_argv_len inp.in_argv Hva
  let base := zmem (fmem inp rsp rrnd) r grant
  induction f generalizing i regs with
  | zero => omega
  | succ f IH =>
    have HiZ := iN_le inp Hva i (by omega)
    have HSiZ := iN_le inp Hva (i + 1) (by omega)
    have HniB := valid_argv_str_len inp.in_argv i Hva Hi
    have HpbLe := pbW_le inp i
    have HpbLeS := pbW_le inp (i + 1)
    have HpbJle := pbJ_le inp i
    have Hpsb := pbase_bound inp i H1 Hi
    obtain ⟨Hptrlo, Hptrhi⟩ := sptr_bounds inp Hva Hve rsp Hsp_hi i Hi
    let M0 := wbytes base r (join1 (inp.in_argv.tail.take (i - 1)))
    let MW := wbytes base r (wjoin (inp.in_argv.tail.take (i - 1)))
    have HlenW : (wjoin (inp.in_argv.tail.take (i - 1))).length = pbW inp i := rfl
    have HlenJ : (join1 (inp.in_argv.tail.take (i - 1))).length = pbJ inp i := rfl
    have HB : ∃ regsB, (∀ x : reg, x ≠ 12 → x ≠ 15 → reg_get regsB x = reg_get regs x) ∧
        reg_get regsB 12 = nat_to_word (pbW inp i) ∧
        msteps source_segs (mkst regs 0x110f8 M0 rrom) (mkst regsB 0x1110c MW rrom) := by
      let regs1 := regupd regs 12 (nat_to_word (pbJ inp i))
      have E0 : RiscvSemantics.step source_segs (mkst regs 0x110f8 M0 rrom) =
          MachineOk (mkst regs1 0x110fc M0 rrom) := by
        apply step_addi_at (hf := SF_110f8) (he := rfl) (hd := SD_110f8) (hrd := rfl)
        getr_resolve; imm_norm; rw [H15, v_addi_0]
      by_cases Hi1 : i = 1
      · refine ⟨regs1, ?_, ?_, ?_⟩
        · intro x Hx12 _; exact regupd_other _ _ _ _ Hx12
        · dsimp only [regs1]; rw [regupd_same, Hi1, pbW_1, pbJ_1]
        · apply msteps.mst_step _ _ _ rfl E0
          apply msteps.mst_step _ _ _ rfl
          · apply step_beq_tk (hf := SF_110fc) (he := rfl) (hd := SD_110fc)
            dsimp only [regs1]; getr_resolve; rw [H14, H16, Hi1]; exact c_eq_refl _
          norm_pc
          have HM : MW = M0 := by
            dsimp only [MW, M0]
            rw [Hi1]
            simp only [show (1 - 1 : Nat) = 0 by rfl, List.take_zero, wjoin, join1]
          rw [HM]
          exact msteps.mst_refl _
      · have Hge2i : 2 ≤ i := by omega
        let regs2 := regupd regs1 12 (nat_to_word (pbW inp i))
        let regs3 := regupd regs2 15 (r + nat_to_word (pbJ inp i))
        refine ⟨regs3, ?_, ?_, ?_⟩
        · intro x Hx12 Hx15
          dsimp only [regs3, regs2, regs1]
          repeat rw [regupd_other _ _ _ _ (by assumption)]
        · dsimp only [regs3, regs2]; regupd_resolve; rfl
        · apply msteps.mst_step _ _ _ rfl E0
          apply msteps.mst_step _ _ _ rfl
          · apply step_beq_ft (hf := SF_110fc) (he := rfl) (hd := SD_110fc)
            dsimp only [regs1]; getr_resolve; rw [H14, H16]
            apply c_eq_neq
            rw [u_ntw i (by omega)]
            change (i : Int) ≠ 1
            omega
          norm_pc
          stepiv SF_11100 SD_11100 (nat_to_word (pbW inp i))
            (dsimp only [regs1]; getr_resolve; regupd_resolve; imm_norm; rw [H15]
             rw [v_addi_Sj _ (by omega), pbW_pbJ inp Hge2 i Hge2i (by omega)])
          stepiv SF_11104 SD_11104 (r + nat_to_word (pbJ inp i))
            (getr_resolve; regupd_resolve; rw [H9, H15, v_add_word])
          apply msteps.mst_step _ _ _ rfl
          · apply step_sb_atv (a := r + nat_to_word (join1 (inp.in_argv.tail.take (i - 1))).length)
              (b := Z_to_bv 8 32) (Hf := SF_11108) (He := rfl) (Hd := SD_11108)
            · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0, HlenJ]
            · getr_resolve; regupd_resolve; rw [H17]; rfl
            · dsimp only [M0, base]
              store_ok_peel
              apply store_ok_zmem
              all_goals rw [word_add_nat]; u_norm; rw [HlenJ]; omega
          step_simpl
          have HM : MW = wbytes M0 (r + nat_to_word (pbJ inp i)) [Z_to_bv 8 32] := by
            dsimp only [MW, M0, pbJ]
            rw [wjoin_join1 _ (firstn_nonnil _ _ (by omega) (tl_nonnil inp Hge2)), wbytes_snoc]
          rw [HM]
          exact msteps.mst_refl _
    obtain ⟨regsB, HagB, H12B, HmsB⟩ := HB
    have H9B : reg_get regsB 9 = r := by
      rw [HagB _ (by reg_neq_tac) (by reg_neq_tac)]; exact H9
    have H14B : reg_get regsB 14 = nat_to_word i := by
      rw [HagB _ (by reg_neq_tac) (by reg_neq_tac)]; exact H14
    have H16B : reg_get regsB 16 = Z_to_bv 64 1 := by
      rw [HagB _ (by reg_neq_tac) (by reg_neq_tac)]; exact H16
    have H17B : reg_get regsB 17 = Z_to_bv 64 32 := by
      rw [HagB _ (by reg_neq_tac) (by reg_neq_tac)]; exact H17
    have H18B : reg_get regsB 18 = argcN inp := by
      rw [HagB _ (by reg_neq_tac) (by reg_neq_tac)]; exact H18
    have H19B : reg_get regsB 19 = Z_to_bv 64 (bv_unsigned rsp + 8) := by
      rw [HagB _ (by reg_neq_tac) (by reg_neq_tac)]; exact H19
    let regs1 := regupd regsB 15 (Z_to_bv 64 (8 * (i : Int)))
    have E1 : RiscvSemantics.step source_segs (mkst regsB 0x1110c MW rrom) =
        MachineOk (mkst regs1 0x11110 MW rrom) := by
      apply step_slli_at (hf := SF_1110c) (he := rfl) (hd := SD_1110c) (hrd := rfl)
      getr_resolve; imm_norm; rw [H14B]; exact v_slli3_nat i HiZ
    let regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (i : Int)))
    have E2 : RiscvSemantics.step source_segs (mkst regs1 0x11110 MW rrom) =
        MachineOk (mkst regs2 0x11114 MW rrom) := by
      apply step_add_at (hf := SF_11110) (he := rfl) (hd := SD_11110) (hrd := rfl)
      dsimp only [regs1]; getr_resolve; rw [H19B]
      unfold v_add
      u_norm
      congr 1 <;> omega
    let regs3 := regupd regs2 6 (sptr inp rsp i)
    have E3 : RiscvSemantics.step source_segs (mkst regs2 0x11114 MW rrom) =
        MachineOk (mkst regs3 0x11118 MW rrom) := by
      rw [step_ld _ _ _ _ _ _ _ _ _ (word_le8 (sptr inp rsp i)) (sptr inp rsp i)
        SF_11114 rfl SD_11114]
      · rfl
      · dsimp only [regs2]; getr_resolve; imm_norm; rw [v_addi_0]
        dsimp only [MW]
        rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [HlenW]; u_norm; omega) (by u_norm; omega)]
        dsimp only [base]
        rw [rdn_zmem_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
        exact read_arg_ptr_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi i Hi
      · exact bytes_le_n_to_le_8 _
    let regs4 := regupd regs3 15 (nat_to_word (pbW inp i + 0))
    have E4 : RiscvSemantics.step source_segs (mkst regs3 0x11118 MW rrom) =
        MachineOk (mkst regs4 0x1111c MW rrom) := by
      apply step_addi_at (hf := SF_11118) (he := rfl) (hd := SD_11118) (hrd := rfl)
      dsimp only [regs3, regs2, regs1]; getr_resolve; regupd_resolve; imm_norm; rw [H12B, v_addi_0]
      rfl
    have Hrdb : ∀ j, j ≤ (inp.in_argv.getD i []).length →
        rdn source_segs base (sptr inp rsp i + nat_to_word j) 1 = some [byte_at (inp.in_argv.getD i []) j] := by
      intro j Hj
      dsimp only [base]
      rw [rdn_zmem_out _ _ _ _ _ _ (by rw [word_add_nat]; u_norm; omega)
        (by right; rw [word_add_nat]; u_norm; omega)]
      exact read_arg_byte_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi i j Hi Hj
    obtain ⟨regsI, HagI, H8I, H13I, H15I, HmsI⟩ := source_copy_inner inp Hva rsp Hsp_lo Hsp_hi Hge2
      base r (sptr inp rsp i) (inp.in_argv.getD i []) (wjoin (inp.in_argv.tail.take (i - 1)))
      Hr0 Hceil Hfree (arg_nz_k inp Hva i Hi) (by rw [HlenW]; exact Hpsb) Hptrlo Hptrhi Hrdb
      (store_grant_zmem_prefix _ _ _ _ _ Hgrant (by omega))
      (inp.in_argv.getD i []).length 0 regs4 (by omega)
      (by dsimp only [regs4, regs3]; regupd_resolve; rfl)
      (by dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; exact H9B)
      (by dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; rw [H12B, HlenW])
      (by dsimp only [regs4]; rw [regupd_same, HlenW])
    simp only [List.take_zero, List.append_nil] at HmsI
    let M1 := wbytes base r (wjoin (inp.in_argv.tail.take (i - 1)) ++ inp.in_argv.getD i [])
    have HpresI : ∀ x : reg, x ≠ 6 → x ≠ 8 → x ≠ 10 → x ≠ 12 → x ≠ 13 → x ≠ 15 →
        reg_get regsI x = reg_get regsB x := by
      intro x Hx6 Hx8 Hx10 Hx12 Hx13 Hx15
      rw [HagI x Hx8 Hx10 Hx13 Hx15]
      dsimp only [regs4, regs3, regs2, regs1]
      repeat rw [regupd_other _ _ _ _ (by assumption)]
    have H14I : reg_get regsI 14 = nat_to_word i := by
      rw [HpresI _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
        (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H14B
    have H18I : reg_get regsI 18 = argcN inp := by
      rw [HpresI _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
        (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H18B
    let regsA := regupd regsI 14 (nat_to_word (i + 1))
    have EA : RiscvSemantics.step source_segs (mkst regsI 0x11134 M1 rrom) =
        MachineOk (mkst regsA 0x11138 M1 rrom) := by
      apply step_addi_at (hf := SF_11134) (he := rfl) (hd := SD_11134) (hrd := rfl)
      getr_resolve; imm_norm; rw [H14I, v_addi_Sj _ (by omega)]
    let regsC := regupd regsA 12 (nat_to_word (i + 1))
    have EB : RiscvSemantics.step source_segs (mkst regsA 0x11138 M1 rrom) =
        MachineOk (mkst regsC 0x1113c M1 rrom) := by
      apply step_addiw_at (hf := SF_11138) (he := rfl) (hd := SD_11138) (hrd := rfl)
      dsimp only [regsA]; getr_resolve; imm_norm
      exact v_addiw_id _ (by rw [u_ntw _ (by omega)]; omega)
    have H12C : reg_get regsC 12 = nat_to_word (i + 1) := regupd_same _ _ _
    have H18C : reg_get regsC 18 = argcN inp := by
      dsimp only [regsC, regsA]; regupd_resolve; exact H18I
    have HM1J : M1 = wbytes base r (join1 (inp.in_argv.tail.take (i + 1 - 1))) := by
      dsimp only [M1]
      rw [Nat.add_one_sub_one, join1_firstn_step inp i H1 Hi]
    by_cases Hlti : i + 1 < inp.in_argv.length
    · have EC : RiscvSemantics.step source_segs (mkst regsC 0x1113c M1 rrom) =
          MachineOk (mkst regsC 0x110f8 M1 rrom) := by
        apply step_blt_tk (Hf := SF_1113c) (He := rfl) (Hd := SD_1113c)
        change c_lts (reg_get regsC 12) (reg_get regsC 18) = true
        rw [H12C, H18C, c_lts_ltb _ _ (by rw [u_ntw _ (by omega)]; omega)
          (by rw [u_argcN inp Hva]; omega), u_ntw _ (by omega), u_argcN inp Hva]
        exact decide_eq_true (by omega)
      obtain ⟨regs', Hag', H8', H13', Hms'⟩ := IH (i + 1) regsC (by omega) Hlti (by omega)
        (by dsimp only [regsC, regsA]; regupd_resolve
            rw [HpresI _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
              (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H9B)
        (by dsimp only [regsC, regsA]; regupd_resolve
            rw [HpresI _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
              (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H16B)
        (by dsimp only [regsC, regsA]; regupd_resolve
            rw [HpresI _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
              (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H17B)
        (by dsimp only [regsC, regsA]; regupd_resolve; rfl)
        (by dsimp only [regsC, regsA]; regupd_resolve; rw [H15I, HlenW, pbJ_S inp i H1 Hi]) H18C
        (by dsimp only [regsC, regsA]; regupd_resolve
            rw [HpresI _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
              (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]; exact H19B)
      refine ⟨regs', ?_, H8', H13', ?_⟩
      · intro x Hx6 Hx8 Hx10 Hx12 Hx13 Hx14 Hx15
        rw [Hag' x Hx6 Hx8 Hx10 Hx12 Hx13 Hx14 Hx15]
        dsimp only [regsC, regsA]
        rw [regupd_other _ _ _ _ Hx12, regupd_other _ _ _ _ Hx14,
          HpresI x Hx6 Hx8 Hx10 Hx12 Hx13 Hx15]
        exact HagB x Hx12 Hx15
      · rw [← HM1J] at Hms'
        exact msteps_trans _ _ _ _ HmsB (msteps.mst_step _ _ _ rfl E1
          (msteps.mst_step _ _ _ rfl E2 (msteps.mst_step _ _ _ rfl E3
          (msteps.mst_step _ _ _ rfl E4 (msteps_trans _ _ _ _ HmsI
          (msteps.mst_step _ _ _ rfl EA (msteps.mst_step _ _ _ rfl EB (msteps.mst_step _ _ _ rfl EC Hms'))))))))
    · have HSieq : i + 1 = inp.in_argv.length := by omega
      have EC : RiscvSemantics.step source_segs (mkst regsC 0x1113c M1 rrom) =
          MachineOk (mkst regsC 0x11140 M1 rrom) := by
        apply step_blt_ft (hf := SF_1113c) (he := rfl) (hd := SD_1113c)
        change c_lts (reg_get regsC 12) (reg_get regsC 18) = false
        rw [H12C, H18C, c_lts_ltb _ _ (by rw [u_ntw _ (by omega)]; omega)
          (by rw [u_argcN inp Hva]; omega), u_ntw _ (by omega), u_argcN inp Hva]
        exact decide_eq_false (by omega)
      have Hlast := pbW_last inp Hge2 i HSieq H1
      have HM1 : M1 = wbytes base r (join1 inp.in_argv.tail) := by
        dsimp only [M1]
        rw [join1_tl_split inp i HSieq H1]
      refine ⟨regsC, ?_, ?_, ?_, ?_⟩
      · intro x Hx6 Hx8 Hx10 Hx12 Hx13 Hx14 Hx15
        dsimp only [regsC, regsA]
        rw [regupd_other _ _ _ _ Hx12, regupd_other _ _ _ _ Hx14,
          HpresI x Hx6 Hx8 Hx10 Hx12 Hx13 Hx15]
        exact HagB x Hx12 Hx15
      · dsimp only [regsC, regsA]; regupd_resolve
        rw [H8I, HlenW]
        unfold tot
        exact congrArg nat_to_word (by omega)
      · dsimp only [regsC, regsA]; regupd_resolve
        rw [H13I, HlenW, Hlast]
      · rw [← HM1]
        exact msteps_trans _ _ _ _ HmsB (msteps.mst_step _ _ _ rfl E1
          (msteps.mst_step _ _ _ rfl E2 (msteps.mst_step _ _ _ rfl E3
          (msteps.mst_step _ _ _ rfl E4 (msteps_trans _ _ _ _ HmsI
          (msteps.mst_step _ _ _ rfl EA (msteps.mst_step _ _ _ rfl EB
          (msteps.mst_step _ _ _ rfl EC (msteps.mst_refl _)))))))))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- Nineteen register-only instructions reach the first `brk`: the
`tot ≤ 65536` test, main's six argument constants and syscall number,
the call into `raw_syscall`, and its seven register moves. The accumulated
length in s0 supplies the bound for the unsigned branch. The final `ecall`
is the allocator branch point. -/
theorem source_to_brk1 (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (Hcap : bv_unsigned (tot inp) ≤ 65536) :
    ∃ regs3,
      reg_get regs3 1 = (0x1108c : word) ∧
      reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs3 8 = tot inp ∧
      reg_get regs3 10 = Z_to_bv 64 0 ∧
      reg_get regs3 18 = argcN inp ∧
      reg_get regs3 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
      msteps source_segs
        (init_machine_state source_segs 0x11190 source_phdrs rsp rrnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        { ms_regs := regs3, ms_fregs := bvmap_empty, ms_pc_val := (0x111e0 : word),
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := fmem inp rsp rrnd, ms_rom := rrom } := by
  have Hjl := join1_tl_len_nat inp Hge2
  have Htn := totn_bound inp Hva
  obtain ⟨regs2, H2, H18, H19, H8, Hms⟩ :=
    source_after_length inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 7
  · apply msteps_trans _ _ _ _ Hms
    stepiv SF_1105c SD_1105c (tot inp)
      (getr_resolve; imm_norm; rw [H8, v_addi_Sj _ (by omega)]; exact S_join1_tot inp Hge2)
    stepiv SF_11060 SD_11060 (Z_to_bv 64 0x10000) (bveq)
    stepiv SF_11064 SD_11064 (Z_to_bv 64 3) (getr_resolve; bveq)
    apply msteps.mst_step _ _ _ rfl
    · apply step_bltu_ft (hf := SF_11068) (he := rfl) (hd := SD_11068)
      getr_resolve; regupd_resolve; rw [c_ltu_ltb]; change decide (65536 < bv_unsigned (tot inp)) = false
      exact decide_eq_false (by omega)
    norm_pc
    stepiv SF_1106c SD_1106c (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_11070 SD_11070 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_11074 SD_11074 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_11078 SD_11078 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_1107c SD_1107c (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_11080 SD_11080 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_11084 SD_11084 (Z_to_bv 64 214) (getr_resolve; bveq)
    stepj SF_11088 SD_11088
    stepiv SF_111c4 SD_111c4 (Z_to_bv 64 214) (getr_resolve; apply v_addi_0)
    stepiv SF_111c8 SD_111c8 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111cc SD_111cc (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111d0 SD_111d0 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111d4 SD_111d4 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111d8 SD_111d8 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111dc SD_111dc (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    apply msteps.mst_step _ _ _ rfl
    · exact step_ecall _ _ _ _ _ _ SF_111e0 rfl
    getr_resolve
    exact msteps.mst_refl _
  · regupd_resolve; bveq
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · regupd_resolve; rfl
  · regupd_resolve; exact H18
  · regupd_resolve; exact H19

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- Twenty register-only instructions run from the first `brk` to the
second: `raw_syscall`'s return through the pinned ra, main's nonzero test,
the no-wrap test for `r + tot`, the second `brk`'s seven arguments, the
call back into `raw_syscall`, and its seven moves. The two branch
conditions are nonzero `r` and `r < r + tot`. -/
theorem source_to_brk2 (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length)
    (regs3 : bvmap 5 word) (r : word)
    (H1 : reg_get regs3 1 = (0x1108c : word))
    (H2 : reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H8 : reg_get regs3 8 = tot inp)
    (H18 : reg_get regs3 18 = argcN inp)
    (H19 : reg_get regs3 19 = Z_to_bv 64 (bv_unsigned rsp + 8))
    (Hrnz : r ≠ Z_to_bv 64 0)
    (Hw : bv_unsigned r + bv_unsigned (tot inp) < 2^64) :
    ∃ regs5,
      reg_get regs5 1 = (0x110e0 : word) ∧
      reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs5 8 = r + tot inp ∧
      reg_get regs5 9 = r ∧
      reg_get regs5 10 = r + tot inp ∧
      reg_get regs5 18 = argcN inp ∧
      reg_get regs5 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
      msteps source_segs (mkst (regupd regs3 10 r) 0x111e4 (fmem inp rsp rrnd) rrom)
        { ms_regs := regs5, ms_fregs := bvmap_empty, ms_pc_val := (0x111e0 : word),
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := fmem inp rsp rrnd, ms_rom := rrom } := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Htg := tot_ge1 inp Hva Hge2
  have Hurt : bv_unsigned (r + tot inp) = bv_unsigned r + bv_unsigned (tot inp) :=
    u_add_small r (tot inp) Hw
  have Hur0 := word_neq0_unsigned r Hrnz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 8
  · stepjr SF_111e4 SD_111e4 (0x1108c : word) (getr_resolve; regupd_resolve; exact H1)
    stepiv SF_1108c SD_1108c r (getr_resolve; apply v_addi_0)
    apply msteps.mst_step _ _ _ rfl
    · apply step_bne_tk (hf := SF_11090) (he := rfl) (hd := SD_11090)
      getr_resolve; regupd_resolve; exact c_eq_0_false r Hur0
    norm_pc
    stepiv SF_110b8 SD_110b8 (r + tot inp)
      (getr_resolve; regupd_resolve; rw [H8, v_add_word]; exact word_add_comm _ _)
    apply msteps.mst_step _ _ _ rfl
    · apply step_bgeu_ft (Hf := SF_110bc) (He := rfl) (Hd := SD_110bc)
      getr_resolve; regupd_resolve; rw [c_ltu_ltb, Hurt]; exact decide_eq_true (by omega)
    norm_pc
    stepiv SF_110c0 SD_110c0 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_110c4 SD_110c4 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_110c8 SD_110c8 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_110cc SD_110cc (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_110d0 SD_110d0 (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_110d4 SD_110d4 (r + tot inp) (getr_resolve; apply v_addi_0)
    stepiv SF_110d8 SD_110d8 (Z_to_bv 64 214) (getr_resolve; bveq)
    stepj SF_110dc SD_110dc
    stepiv SF_111c4 SD_111c4 (Z_to_bv 64 214) (getr_resolve; apply v_addi_0)
    stepiv SF_111c8 SD_111c8 (r + tot inp) (getr_resolve; apply v_addi_0)
    stepiv SF_111cc SD_111cc (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111d0 SD_111d0 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111d4 SD_111d4 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111d8 SD_111d8 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    stepiv SF_111dc SD_111dc (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
    apply msteps.mst_step _ _ _ rfl
    · exact step_ecall _ _ _ _ _ _ SF_111e0 rfl
    getr_resolve
    exact msteps.mst_refl _
  · regupd_resolve; bveq
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · regupd_resolve; rfl
  · regupd_resolve; rfl
  · regupd_resolve; exact H18
  · regupd_resolve; exact H19

/-- The loop's only store is musl's own ra spill, inside the
RLIMIT_STACK window. -/
theorem aj_sok8 (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (mem : word → Option byte) (a : word)
    (Hg : mem_grows (wmem inp rsp rrnd) mem)
    (Hlo : bv_unsigned rsp - 80 ≤ bv_unsigned a)
    (Hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp) :
    RiscvSemantics.store_ok source_segs mem a 8 = true := by
  have Hlo' := rsp_lo_num rsp Hsp_lo
  have Hhi' := rsp_hi_num rsp Hsp_hi
  apply store_ok_mono _ _ _ _ _ Hg
  unfold wmem
  apply store_ok_wrap_window
  · unfold stack_max_size; omega
  · exact Hhi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- After a possibly short delivery of `k` bytes, the machine sits at
0x112f0 (`__syscall_cp_c`'s post-ecall return) with a0 equal to
`len_word (rest.take k)`. It returns through musl's `write` wrapper and
`__syscall_ret` to main's drain loop, which keeps the running pointer in
s4 and the running count in s0. The only store is musl's own ra spill.
The proof inducts on `fuel ≥ rest.length`. -/
theorem src_put_wall (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (fuel : Nat) (rest : List byte) (p : word) (k : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hk1 : 1 ≤ k) (Hk2 : k ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 2097152)
    (Hplo : 0 < bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) ≤ bv_unsigned rsp - 80)
    (H1 : reg_get regs 1 = (0x1128c : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H8 : reg_get regs 8 = len_word rest)
    (H10 : reg_get regs 10 = len_word (rest.take k))
    (H20 : reg_get regs 20 = p)
    (H17 : bv_unsigned (reg_get regs 17) = 64)
    (Hgrow : mem_grows (wmem inp rsp rrnd) mem)
    (Hra56 : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8 =
      some (word_to_le_bytes 8 (0x11170 : word)))
    (Hslra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111bc : word)))
    (Hsl : ∀ a : word, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Hread : rdn source_segs mem p rest.length = some rest) :
    to_wall_tail source_segs (Z_to_bv 64 1)
      (mkst regs (0x112f0 : word) mem rrom) (rest.drop k)
      (to_wallexit source_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p k regs mem with
  | zero => omega
  | succ fuel IH =>
    have Hlo := rsp_lo_num rsp Hsp_lo
    have Hhi := rsp_hi_num rsp Hsp_hi
    have Htake := u_len_word_firstn k rest Hk2 (by omega)
    stepjr SF_112f0 SD_112f0 (0x1128c : word) (getr_resolve; exact H1)
    stepld SF_1128c SD_1128c (Z_to_bv 64 (bv_unsigned rsp - 56))
      (0x11170 : word) (exact Hra56)
    stepiv SF_11290 SD_11290 (Z_to_bv 64 (bv_unsigned rsp - 48))
      (getr_resolve; regupd_resolve; rw [H2]; sp_norm; congr 1; omega)
    stepj SF_11294 SD_11294
    stepiv SF_11298 SD_11298 (Z_to_bv 64 18446744073709547520) (bveq)
    apply to_wall_tail.twt_step _ _ _ _ rfl
    · apply step_bltu_ft (hf := SF_1129c) (he := rfl) (hd := SD_1129c)
      getr_resolve; regupd_resolve; rw [H10, c_ltu_ltb, Htake]
      change decide (18446744073709547520 < (k : Int)) = false
      exact decide_eq_false (by omega)
    norm_pc
    stepjr SF_112a0 SD_112a0 (0x11170 : word) (getr_resolve; regupd_resolve; rfl)
    apply to_wall_tail.twt_step _ _ _ _ rfl
    · apply step_bge_ft (hf := SF_11170) (he := rfl) (hd := SD_11170)
      getr_resolve; regupd_resolve; rw [H10]
      exact c_lts_0_pos _ (by rw [Htake]; omega) (by rw [Htake]; omega)
    norm_pc
    stepiv SF_11174 SD_11174 (Z_to_bv 64 (bv_unsigned p + (k : Int)))
      (getr_resolve; regupd_resolve; rw [H20, H10]; exact v_add_len_firstn_Z p k rest Hk2 (by omega))
    stepiv SF_11178 SD_11178 (len_word (rest.drop k))
      (getr_resolve; regupd_resolve; rw [H8, H10]; exact v_sub_len_firstn k rest Hk2 (by omega))
    stepj SF_1117c SD_1117c
    by_cases Hfull : k = rest.length
    · subst k
      rw [List.drop_length]
      apply to_wall_tail.twt_step _ _ _ _ rfl
      · apply step_bne_ft (hf := SF_11148) (he := rfl) (hd := SD_11148)
        getr_resolve; regupd_resolve
        exact c_eq_0_of_u _ rfl
      norm_pc
      stepiv SF_1114c SD_1114c (Z_to_bv 64 0) (getr_resolve; bveq)
      stepj SF_11150 SD_11150
      apply to_wall_tail.twt_done
      change to_wexit source_segs _ [] (Z_to_bv 64 0)
      apply source_epilogue rsp Hsp_lo Hsp_hi
      · regupd_resolve; rfl
      · regupd_resolve; rfl
      · decide +kernel
      · exact Hslra
      · exact Hsl
    · have Hrem : 1 ≤ (rest.drop k).length := by rw [List.length_drop]; omega
      have HremU := u_len_word (rest.drop k) (by rw [List.length_drop]; omega)
      have HpU : bv_unsigned (Z_to_bv 64 (bv_unsigned p + (k : Int))) =
          bv_unsigned p + (k : Int) := u_Z2bv _ (by omega) (by omega)
      have HrestRead : rdn source_segs mem (Z_to_bv 64 (bv_unsigned p + (k : Int)))
          (rest.drop k).length = some (rest.drop k) := by
        have Hsk := rdn_skipn source_segs mem rest.length p rest k Hread Hk2
        rw [word_add_nat_Z _ _ (by omega)] at Hsk
        rw [List.length_drop]; exact Hsk
      apply to_wall_tail.twt_step _ _ _ _ rfl
      · apply step_bne_tk (hf := SF_11148) (he := rfl) (hd := SD_11148)
        getr_resolve; regupd_resolve
        exact c_eq_0_false _ (by rw [HremU]; omega)
      norm_pc
      stepiv SF_11160 SD_11160 (len_word (rest.drop k)) (getr_resolve; apply v_addi_0)
      stepiv SF_11164 SD_11164 (Z_to_bv 64 (bv_unsigned p + (k : Int))) (getr_resolve; apply v_addi_0)
      stepiv SF_11168 SD_11168 (Z_to_bv 64 1) (getr_resolve; bveq)
      stepj SF_1116c SD_1116c
      stepiv SF_11264 SD_11264 (Z_to_bv 64 (bv_unsigned rsp - 64))
        (getr_resolve; sp_norm; congr 1; omega)
      stepiv SF_11268 SD_11268 (len_word (rest.drop k)) (getr_resolve; apply v_addi_0)
      stepi SF_1126c SD_1126c
      stepiv SF_11270 SD_11270 (Z_to_bv 64 (bv_unsigned p + (k : Int))) (getr_resolve; apply v_addi_0)
      stepi SF_11274 SD_11274
      stepiv SF_11278 SD_11278 (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
      stepi SF_1127c SD_1127c
      stepiv SF_11280 SD_11280 (Z_to_bv 64 64) (getr_resolve; bveq)
      stepsd SF_11284 SD_11284 (Z_to_bv 64 (bv_unsigned rsp - 56))
        (0x11170 : word) (getr_resolve; bveq)
        (apply aj_sok8 inp rsp rrnd Hsp_lo Hsp_hi; exact Hgrow; u_norm; omega; u_norm; omega)
      stepj SF_11288 SD_11288
      stepj SF_112f4 SD_112f4
      stepiv SF_112d0 SD_112d0 (Z_to_bv 64 64) (getr_resolve; apply v_addi_0)
      stepiv SF_112d4 SD_112d4 (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
      stepiv SF_112d8 SD_112d8 (Z_to_bv 64 (bv_unsigned p + (k : Int))) (getr_resolve; apply v_addi_0)
      stepiv SF_112dc SD_112dc (len_word (rest.drop k)) (getr_resolve; apply v_addi_0)
      stepi SF_112e0 SD_112e0
      stepi SF_112e4 SD_112e4
      stepi SF_112e8 SD_112e8
      apply to_wall_tail.twt_step _ _ _ _ rfl
      · exact step_ecall _ _ _ _ _ _ SF_112ec rfl
      apply to_wall_tail.twt_more _ _ _ Hrem
      apply twl_write_rec source_segs (Z_to_bv 64 1)
      · getr_resolve; regupd_resolve; decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve
        rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        change rdn source_segs _ _ (word_to_nat (len_word (rest.drop k))) = _
        have Hwn : word_to_nat (len_word (rest.drop k)) = (rest.drop k).length := by
          unfold word_to_nat
          unfold bv_unsigned at HremU
          omega
        rw [Hwn, rdn_wbytes_below _ _ _ _ _ _
          (by rw [HpU, List.length_drop]; u_norm; omega)
          (by rw [length_N_to_le_bytes]; u_norm; omega)]
        exact HrestRead
      · exact Hrem
      · intro m Hm1 Hm2
        norm_pc
        apply IH (rest.drop k) (Z_to_bv 64 (bv_unsigned p + (k : Int))) m
        · rw [List.length_drop]; omega
        · exact Hm1
        · exact Hm2
        · rw [List.length_drop]; omega
        · rw [HpU]; omega
        · rw [HpU, List.length_drop]; omega
        · regupd_resolve; bveq
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; decide +kernel
        · exact mem_grows_trans _ _ _ Hgrow (wbytes_grows _ _ _)
        · apply rdn_wbytes_hit8; u_norm; omega
        · rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact Hslra
        · intro a Ha
          have Hab : bv_unsigned rsp - 48 ≤ bv_unsigned a ∧
              bv_unsigned a + 8 ≤ bv_unsigned rsp - 8 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
            rcases Ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
          rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
          exact Hsl a Ha
        · rw [rdn_wbytes_below _ _ _ _ _ _
            (by rw [HpU, List.length_drop]; u_norm; omega)
            (by rw [length_N_to_le_bytes]; u_norm; omega)]
          exact HrestRead

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem source_success (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (regs : bvmap 5 word) (r grant : word)
    (Hgrant : bv_unsigned (tot inp) ≤ bv_unsigned grant)
    (Hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned rsp - stack_max_size)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + bv_unsigned (tot inp) ≤ bv_unsigned rsp - stack_max_size)
    (Hfree : region_free (segments_reserved source_segs) r (tot inp) = true)
    (H1 : reg_get regs 1 = (0x110e0 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H8 : reg_get regs 8 = r + tot inp)
    (H9 : reg_get regs 9 = r)
    (H10 : reg_get regs 10 = r + tot inp)
    (H18 : reg_get regs 18 = argcN inp)
    (H19 : reg_get regs 19 = Z_to_bv 64 (bv_unsigned rsp + 8)) :
    to_wallexit source_segs (Z_to_bv 64 1) [jout inp.in_argv] (Z_to_bv 64 0)
      (mkst regs 0x111e4 (zmem (fmem inp rsp rrnd) r grant) rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Htg1 := tot_ge1 inp Hva Hge2
  have HtbZ := totn_bound inp Hva
  have Htgn1 := totn_ge1 inp Hge2
  have Hut := u_tot inp Hva
  have HgrantceilN : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned rsp - 8388608 := Hgrantceil
  have HceilN : bv_unsigned r + bv_unsigned (tot inp) ≤ bv_unsigned rsp - 8388608 := Hceil
  constructor
  · rw [jout_len_nat inp Hge2]; omega
  let mem0 := zmem (fmem inp rsp rrnd) r grant
  let regsA := regupd (regupd (regupd (regupd (regupd regs 14 (Z_to_bv 64 1))
    20 r) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 1)) 17 (Z_to_bv 64 32)
  -- Return, check the grant, and set up the five copy-loop constants.
  have HmsA : msteps source_segs (mkst regs 0x111e4 mem0 rrom)
      (mkst regsA 0x110f8 mem0 rrom) := by
    stepjr SF_111e4 SD_111e4 (0x110e0 : word) (getr_resolve; exact H1)
    apply msteps.mst_step _ _ _ rfl
    · apply step_bne_ft (hf := SF_110e0) (he := rfl) (hd := SD_110e0)
      getr_resolve; rw [H8, H10]; exact c_eq_refl _
    norm_pc
    stepiv SF_110e4 SD_110e4 (Z_to_bv 64 1) (getr_resolve; bveq)
    stepiv SF_110e8 SD_110e8 r (getr_resolve; regupd_resolve; rw [H9]; apply v_addi_0)
    stepiv SF_110ec SD_110ec (Z_to_bv 64 0) (getr_resolve; bveq)
    stepiv SF_110f0 SD_110f0 (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
    stepiv SF_110f4 SD_110f4 (Z_to_bv 64 32) (getr_resolve; bveq)
    exact msteps.mst_refl _
  apply msteps_to_wall_tail _ _ _ _ _ _ HmsA
  obtain ⟨regsC, HagC, H8C, H13C, HmsC⟩ :=
    source_copy_outer inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2 r grant
      Hgrant Hgrantceil Hr0 Hceil Hfree inp.in_argv.length 1 regsA
      (by omega) (by omega) (by omega)
      (by dsimp only [regsA]; regupd_resolve; exact H9)
      (by dsimp only [regsA]; regupd_resolve; rfl)
      (by dsimp only [regsA]; regupd_resolve; rfl)
      (by dsimp only [regsA]; regupd_resolve; rfl)
      (by dsimp only [regsA]; regupd_resolve; rw [pbJ_1]; rfl)
      (by dsimp only [regsA]; regupd_resolve; exact H18)
      (by dsimp only [regsA]; regupd_resolve; exact H19)
  simp only [Nat.sub_self, List.take_zero, join1, wbytes] at HmsC
  apply msteps_to_wall_tail _ _ _ _ _ _ HmsC
  have H2C : reg_get regsC 2 = Z_to_bv 64 (bv_unsigned rsp - 48) := by
    rw [HagC _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
      (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]
    dsimp only [regsA]; regupd_resolve; exact H2
  have H20C : reg_get regsC 20 = r := by
    rw [HagC _ (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)
      (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac) (by reg_neq_tac)]
    dsimp only [regsA]; regupd_resolve; rfl
  let memJ := wbytes mem0 r (jout inp.in_argv)
  let memW1 := wbytes memJ (Z_to_bv 64 (bv_unsigned rsp - 56))
    (word_to_le_bytes 8 (0x11170 : word))
  have Hgrow0 : mem_grows (wmem inp rsp rrnd) mem0 := by
    unfold mem0
    apply mem_grows_trans _ _ _ ?_ (zmem_grows _ _ _)
    unfold fmem emem
    repeat apply mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)
    exact mem_grows_refl _
  have HgrowJ : mem_grows (wmem inp rsp rrnd) memJ :=
    mem_grows_trans _ _ _ Hgrow0 (wbytes_grows _ _ _)
  have HgrowW : mem_grows (wmem inp rsp rrnd) memW1 :=
    mem_grows_trans _ _ _ HgrowJ (wbytes_grows _ _ _)
  have HreadW : rdn source_segs memW1 r (jout inp.in_argv).length = some (jout inp.in_argv) := by
    dsimp only [memW1]
    rw [rdn_wbytes_below _ _ _ _ _ _
      (by rw [jout_len_nat inp Hge2]; u_norm; omega)
      (by rw [length_N_to_le_bytes]; u_norm; omega)]
    apply rdn_wbytes_hit
    rw [jout_len_nat inp Hge2]; omega
  have HraW : rdn source_segs memW1 (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x111bc : word)) := by
    dsimp only [memW1, memJ, mem0]
    rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [jout_len_nat inp Hge2]; u_norm; omega) (by u_norm; omega)]
    rw [rdn_zmem_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
    exact read_slot_ra inp rsp rrnd Hsp_lo Hsp_hi
  have HslW : ∀ a : word, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 16),
      Z_to_bv 64 (bv_unsigned rsp - 24), Z_to_bv 64 (bv_unsigned rsp - 32),
      Z_to_bv 64 (bv_unsigned rsp - 40), Z_to_bv 64 (bv_unsigned rsp - 48)] →
      rdn source_segs memW1 a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
    intro a Ha
    have Hab : bv_unsigned rsp - 48 ≤ bv_unsigned a ∧
        bv_unsigned a + 8 ≤ bv_unsigned rsp - 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
      rcases Ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
    dsimp only [memW1, memJ, mem0]
    rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
    rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [jout_len_nat inp Hge2]; omega) (by omega)]
    rw [rdn_zmem_out _ _ _ _ _ _ (by omega) (by right; omega)]
    exact read_slot_0 inp rsp rrnd Hsp_lo Hsp_hi a Ha
  -- Store the newline and enter musl's write wrapper.
  stepiv SF_11140 SD_11140 (Z_to_bv 64 10) (getr_resolve; bveq)
  apply to_wall_tail.twt_step _ _ _ _ rfl
  · apply step_sb_atv (a := r + nat_to_word (totn inp - 1)) (b := Z_to_bv 8 10)
      (Hf := SF_11144) (He := rfl) (Hd := SD_11144)
    · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0, H13C]
    · getr_resolve; rfl
    · store_ok_peel
      apply store_ok_zmem
      all_goals rw [word_add_nat]; u_norm; omega
  step_simpl
  have HM : wbytes (wbytes mem0 r (join1 inp.in_argv.tail))
      (r + nat_to_word (totn inp - 1)) [Z_to_bv 8 10] = memJ := by
    dsimp only [memJ, jout]
    rw [wbytes_snoc, join1_tl_len_nat inp Hge2]
  rw [HM]
  apply to_wall_tail.twt_step _ _ _ _ rfl
  · apply step_bne_tk (hf := SF_11148) (he := rfl) (hd := SD_11148)
    getr_resolve; regupd_resolve; rw [H8C]
    exact c_eq_0_false _ (by omega)
  norm_pc
  stepiv SF_11160 SD_11160 (tot inp) (getr_resolve; regupd_resolve; rw [H8C]; apply v_addi_0)
  stepiv SF_11164 SD_11164 r (getr_resolve; regupd_resolve; rw [H20C]; apply v_addi_0)
  stepiv SF_11168 SD_11168 (Z_to_bv 64 1) (getr_resolve; bveq)
  stepj SF_1116c SD_1116c
  stepiv SF_11264 SD_11264 (Z_to_bv 64 (bv_unsigned rsp - 64))
    (getr_resolve; regupd_resolve; imm_norm; rw [H2C]
     change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 48)) - 16) = _
     rw [u_Z2bv _ (by omega) (by omega)]; apply congrArg (Z_to_bv 64); omega)
  stepiv SF_11268 SD_11268 (tot inp) (getr_resolve; apply v_addi_0)
  stepiv SF_1126c SD_1126c (Z_to_bv 64 0) (getr_resolve; bveq)
  stepiv SF_11270 SD_11270 r (getr_resolve; apply v_addi_0)
  stepiv SF_11274 SD_11274 (Z_to_bv 64 0) (getr_resolve; bveq)
  stepiv SF_11278 SD_11278 (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
  stepiv SF_1127c SD_1127c (Z_to_bv 64 0) (getr_resolve; bveq)
  stepiv SF_11280 SD_11280 (Z_to_bv 64 64) (getr_resolve; bveq)
  apply to_wall_tail.twt_step _ _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned rsp - 56)) (v := (0x11170 : word))
      (hf := SF_11284) (he := rfl) (hd := SD_11284)
    · getr_resolve; imm_norm
      change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 8) = _
      rw [u_Z2bv _ (by omega) (by omega)]
      apply congrArg (Z_to_bv 64); omega
    · getr_resolve; bveq
    · exact aj_sok8 inp rsp rrnd Hsp_lo Hsp_hi memJ _ HgrowJ (by u_norm; omega) (by u_norm; omega)
  norm_pc
  stepj SF_11288 SD_11288
  stepj SF_112f4 SD_112f4
  stepiv SF_112d0 SD_112d0 (Z_to_bv 64 64) (getr_resolve; apply v_addi_0)
  stepiv SF_112d4 SD_112d4 (Z_to_bv 64 1) (getr_resolve; apply v_addi_0)
  stepiv SF_112d8 SD_112d8 r (getr_resolve; apply v_addi_0)
  stepiv SF_112dc SD_112dc (tot inp) (getr_resolve; apply v_addi_0)
  stepiv SF_112e0 SD_112e0 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  stepiv SF_112e4 SD_112e4 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  stepiv SF_112e8 SD_112e8 (Z_to_bv 64 0) (getr_resolve; apply v_addi_0)
  apply to_wall_tail.twt_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ SF_112ec rfl
  apply to_wall_tail.twt_more
  · rw [jout_len_nat inp Hge2]; omega
  apply twl_write_rec source_segs (Z_to_bv 64 1)
  · getr_resolve; regupd_resolve; decide +kernel
  · regupd_resolve; rfl
  · regupd_resolve
    rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
    change rdn source_segs memW1 r (word_to_nat (tot inp)) = _
    rw [jout_len_w inp Hva Hge2]
    exact HreadW
  · rw [jout_len_nat inp Hge2]; omega
  · intro k Hk1 Hk2
    norm_pc
    apply src_put_wall inp rsp rrnd Hsp_lo Hsp_hi (jout inp.in_argv).length (jout inp.in_argv) r k
    · omega
    · exact Hk1
    · exact Hk2
    · rw [jout_len_nat inp Hge2]; omega
    · exact Hr0
    · rw [jout_len_nat inp Hge2]; omega
    · regupd_resolve; bveq
    · regupd_resolve; rfl
    · regupd_resolve; rw [H8C]; unfold tot nat_to_word len_word; rw [jout_len_nat inp Hge2]
    · regupd_resolve; rfl
    · regupd_resolve; exact H20C
    · regupd_resolve; decide +kernel
    · exact HgrowW
    · apply rdn_wbytes_hit8; u_norm; omega
    · exact HraW
    · exact HslW
    · exact HreadW

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- The outcome tree. -/
theorem source_outcomes (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
    (rbrk rmb : word)
    (Hbrk_lo : reserved_top (segments_reserved source_segs) ≤ bv_unsigned rbrk)
    (Hbrk_hi : bv_unsigned rbrk ≤ reserved_top (segments_reserved source_segs) + brk_aslr_max)
    (Hge2 : 2 ≤ inp.in_argv.length) (Hbrk_mod : bv_unsigned rbrk % page_size = 0) :
    bv_unsigned (tot inp) ≤ 65536 →
    to_outcomes source_segs
      (init_machine_state source_segs 0x11190 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (two_outcomes [] (Z_to_bv 64 4) [jout inp.in_argv] (Z_to_bv 64 0)) := by
  intro Hcap
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hsms := stack_max_size_val
  have Htg1 := tot_ge1 inp Hva Hge2
  have Htb := totn_bound inp Hva
  have Hut := u_tot inp Hva
  obtain ⟨regs3, E1, E2, E8, E10, E18, E19, Hms⟩ :=
    source_to_brk1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2 Hcap
  apply tou_msteps _ _ _ _ _ Hms
  apply tou_brk_r source_segs _ _ (Z_to_bv 64 214)
    (T1 (segments_reserved source_segs) source_alloc_limit
      (bv_unsigned rsp - stack_max_size) (tot inp) [jout inp.in_argv])
  · rfl
  · decide +kernel
  · intro r Hok
    simp only [ms_gpr, arg_reg_0, E10] at Hok ⊢
    have Hquery : r = rbrk := (brk_r_ok_query_iff _ r).mp Hok
    have Hblo := rbrk_lo_num rbrk Hbrk_lo
    have Hbhi := rbrk_hi_num rbrk Hbrk_hi
    have Hur : bv_unsigned r = bv_unsigned rbrk := congrArg bv_unsigned Hquery
    have Hrmod : bv_unsigned r % page_size = 0 := by rw [Hur]; exact Hbrk_mod
    have Hrnz : r ≠ Z_to_bv 64 0 := by
      intro He
      have := congrArg bv_unsigned He
      rw [show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
      omega
    have Hnw : bv_unsigned r + bv_unsigned (tot inp) < 2^64 := by omega
    have Hrtop : reserved_top (segments_reserved source_segs) ≤ bv_unsigned r := by
      rw [Hur]; exact Hbrk_lo
    have Hurt : bv_unsigned (r + tot inp) = bv_unsigned r + bv_unsigned (tot inp) :=
      u_add_small r (tot inp) Hnw
    have Hwant0 : r + tot inp ≠ Z_to_bv 64 0 := by
      intro He
      have := congrArg bv_unsigned He
      rw [Hurt, show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
      omega
    have Hne2 : r ≠ r + tot inp := by
      intro He
      have := congrArg bv_unsigned He
      rw [Hurt] at this
      omega
    rw [brk_zeros_query, brk_unmaps_query _ _ Hquery, adv_brk, apply_zeros_nil,
      brk_model_query _ _ Hquery]
    obtain ⟨regs5, F1, F2, F8, F9, F10, F18, F19, Hms2⟩ :=
      source_to_brk2 inp Hva rsp rrnd Hsp_lo Hsp_hi Hge2 regs3 r
        E1 E2 E8 E18 E19 Hrnz Hnw
    apply tou_msteps _ _ _ _ _ Hms2
    apply tou_brk_r source_segs _ _ (Z_to_bv 64 214) (T2 (r + tot inp) [jout inp.in_argv])
    · rfl
    · decide +kernel
    · intro r2 Hok2
      simp only [ms_gpr, arg_reg_0, F10] at Hok2 ⊢
      change brk_r_ok (VmMaps.mkVmMapsFull (segments_reserved source_segs) [] []
        rbrk r source_alloc_limit rmb rsp) (r + tot inp) r2 at Hok2
      have Hcases := (brk_r_ok_grow_iff _ _ _ _ _ _ _ _ _ _
        (by rw [Hurt]; omega) (by rw [Hurt]; omega) (by rw [Hurt]; omega)).mp Hok2
      by_cases Heq : r2 = r + tot inp
      · subst r2
        obtain ⟨_, Hgrow2⟩ := Hcases
        rw [brk_grow_ok_aligned_grow _ _ _ Hwant0 (by change 0 < bv_unsigned r; omega)
          (by change bv_unsigned r < bv_unsigned (r + tot inp); rw [Hurt]; omega) Hrmod] at Hgrow2
        simp only [List.append_nil, Bool.and_eq_true,
          decide_eq_true_eq] at Hgrow2
        obtain ⟨⟨Hle, Hfree⟩, _⟩ := Hgrow2
        let grant := Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + tot inp)) - bv_unsigned r)
        obtain ⟨_, Hgrant, Hphysceil, Hrawceil, Hrawfree, _⟩ :=
          brk_aligned_grant_ok _ r (tot inp) grant _ _ Hurt Hurt rfl
            (alloc_top_page_lt _) Hle Hfree
        change to_outcomes source_segs
          (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU _ []
            (Sys.Mm.Mmap.brk_zeros (r + tot inp) (r + tot inp) r) (Sys.Mm.Mmap.brk_unmaps (r + tot inp) r) [] []))) _ _
        rw [brk_zeros_aligned_grow _ _ _ Hwant0 (by omega) (by rw [Hurt]; omega) Hrmod,
          brk_unmaps_grow _ _ (by rw [Hurt]; omega), adv_brk, apply_zeros_one]
        apply tou_equiv _ _ _ _ _ ?_ (T2_succ_iff (r + tot inp) [jout inp.in_argv])
        apply tou_wexit_eq
        · apply fd1chan_brk_model
          apply fd1chan_with_vmmaps
          apply init_model_fd1chan
        · apply source_success inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge2
            (regupd regs5 10 (r + tot inp)) r grant Hgrant Hphysceil (by omega) Hrawceil Hrawfree
          · regupd_resolve; exact F1
          · regupd_resolve; exact F2
          · regupd_resolve; exact F8
          · regupd_resolve; exact F9
          · regupd_resolve; rfl
          · regupd_resolve; exact F18
          · regupd_resolve; exact F19
        · exact jout_modeled inp Hva Hge2 Hcap
      · obtain ⟨Hcase, _⟩ := Hcases
        rcases Hcase with Hc | Hc
        · exact False.elim (Heq Hc)
        subst r2
        change to_outcomes source_segs
          (advance_past_svc (apply_effect _ (SyscallEffect.mkEffectU _ []
            (Sys.Mm.Mmap.brk_zeros (r + tot inp) r r) (Sys.Mm.Mmap.brk_unmaps r r) [] []))) _ _
        rw [brk_zeros_keep, brk_unmaps_grow _ _ (by omega), adv_brk, apply_zeros_nil]
        apply tou_equiv _ _ _ _ _ ?_ (T2_fail_iff (r + tot inp) [jout inp.in_argv] r Hne2)
        apply tou_wexit_eq
        · apply fd1chan_brk_model
          apply fd1chan_with_vmmaps
          apply init_model_fd1chan
        · change to_wexit source_segs _ [] (Z_to_bv 64 4)
          stepjr SF_111e4 SD_111e4 (0x110e0 : word) (getr_resolve; regupd_resolve; exact F1)
          apply to_wexit.tw_step _ _ _ _ rfl
          · apply step_bne_tk (hf := SF_110e0) (he := rfl) (hd := SD_110e0)
            getr_resolve; regupd_resolve; rw [F8]
            apply c_eq_neq
            rw [Hurt]
            omega
          norm_pc
          apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi
          regupd_resolve; exact F2
        · intro b Hb; exact False.elim (List.not_mem_nil Hb)
    · intro o
      simp only [ms_gpr, arg_reg_0, F10]
      exact T1_iff_T2 (segments_reserved source_segs) source_alloc_limit rbrk rmb rsp
        (tot inp) [jout inp.in_argv] r Hrnz (by omega) Hnw o
  · intro o
    simp only [ms_gpr, arg_reg_0, E10]
    have Hblo := rbrk_lo_num rbrk Hbrk_lo
    have Hbhi := rbrk_hi_num rbrk Hbrk_hi
    apply twoU_iff_T1 (segments_reserved source_segs) source_alloc_limit
      (bv_unsigned rsp - stack_max_size) (tot inp) (jout inp.in_argv) rbrk
    · intro r0
      exact brk_r_ok_query_iff _ r0
    · refine ⟨?_, ?_, Or.inr ?_⟩
      · intro He
        have := congrArg bv_unsigned He
        rw [show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
        omega
      · omega
      · apply growable_aligned_grow
        · exact Hbrk_mod
        · exact Hbrk_lo
        · omega
        · unfold page_size; omega
        · change bv_unsigned (tot inp) ≤ 0x400000000; omega
    · intro He
      have := congrArg bv_unsigned He
      rw [show bv_unsigned (Z_to_bv 64 0) = 0 from rfl] at this
      omega

end LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_source
