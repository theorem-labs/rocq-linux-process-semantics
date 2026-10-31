import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.SymExec
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.SymBranch
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
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_code
import LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_defs
import LinuxProcessSemantics.Examples.alloc_join_ns.SourceMemImage
import LinuxProcessSemantics.Examples.alloc_join_ns.TargetMemImage

/-! rocq-baseline: b89fd3aefa642f07b01c02ead422e3cebfce5549 -/

/-! # alloc-join-ns TARGET binary (Zig)

PROOF-SIDE FILE (not part of the trusted specification).
Frames, prologue, length loop, early exits, the run up to the mmap ecall,
and both continuations.

Machine plan (see `alloc_join_ns_code`):
- `_start 0x1001158..0x1001174`: two-slot frame, argc/argv, call run.
- `run 0x1001180`: 48-byte frame; argc < 2 → a1 = 2 → 0x10012ac exit 2.
- Length loop `0x10011bc..0x10011e0` (slen callee at 0x10012d0):
  s2 = |join1(argv[1..])| = tot - 1.
- Cap: (tot - 1) >> 16 ≠ 0 → exit 3.
- mmap arguments, DIRECT ecall at 0x100120c (the tmw branch point).
- Failure (blt a0,0): exit 4.
- Success: nested copy loops 0x1001228..0x1001268, '\n' store,
  one-write put loop, exit 0. NO munmap.

Conventions: sp-relative values have the canonical
`Z_to_bv 64 (bv_unsigned asp - k)` form, loop indices use `nat_to_word`,
and the total byte count `ttot` is the word `nat_to_word ttotn`;
all range bookkeeping is `Int` over `bv_unsigned`.
-/

namespace LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
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
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Examples.alloc_join_ns.TargetMemImage
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_code
open LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_defs

def arom : word → Option byte := seg_rom target_segs

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001158 := by
  decide +kernel

/-- Successor step of a byte-walk pointer as a wrapping bitvector add
(hypothesis-free: both sides wrap identically). -/
theorem v_addi_ntw_S (p : word) (j : Nat) :
    v_addi (p + nat_to_word j) 1 = p + nat_to_word (j + 1) := by
  rw [word_add_nat, word_add_nat]
  apply bv_eq_of_unsigned
  unfold v_addi
  simp only [Z_to_bv_unsigned, bv_wrap64_mod]
  rw [Int.emod_add_emod]
  congr 1

/-- The register shift that `srli a0,s2,16` compiles to, in the
immediate-shift spelling the rest of the file uses. The shift amount
is a closed literal; only the shifted value is symbolic. -/
theorem v_srl_16 (x : word) : v_srl x (Z_to_bv 64 16) = v_srli x 16 := by
  rfl

-- Store legality (both target segments are read-only).

theorem target_avoids_high (a : word) (n : Int) (Ha : 0x1002000 ≤ bv_unsigned a) :
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true := by
  change ((false || !(decide (0x1000000 < bv_unsigned a + n) &&
      decide (bv_unsigned a < 0x1001000))) &&
    ((false || !(decide (0x1001000 < bv_unsigned a + n) &&
      decide (bv_unsigned a < 0x1002000))) && true)) = true
  have h0 : ¬ bv_unsigned a < 0x1001000 := by omega
  have h1 : ¬ bv_unsigned a < 0x1002000 := by omega
  simp only [h0, h1, decide_false, Bool.and_false, Bool.not_false,
    Bool.false_or, Bool.and_true]

-- Grant facts for the target image.

theorem target_reserved_val :
    segments_reserved target_segs = [(0x1000000, 0x1000), (0x1001000, 0x1000)] := by
  decide +kernel

set_option maxRecDepth 65536 in
theorem target_grant_witness (inp : ProcInput) (hint brk0 mb sp : word) (g : Int)
    (Hsp : sp_window_lo ≤ bv_unsigned sp) (_Hg0 : 0 ≤ g) (Hg : g ≤ 69632) :
    grant_ok hint
      (init_model (segments_reserved target_segs) brk0 mb sp target_alloc_limit inp)
      (0x2aaaaab000 : word) g = true := by
  unfold grant_ok
  change (decide (bv_unsigned (0x2aaaaab000 : word) % page_size = 0) &&
    decide (0 < bv_unsigned (0x2aaaaab000 : word)) &&
    decide (bv_unsigned (0x2aaaaab000 : word) + g ≤ bv_unsigned sp - stack_max_size) &&
    region_free (segments_reserved target_segs ++ []) (0x2aaaaab000 : word) (Z_to_bv 64 g) &&
    decide (0 + g ≤ target_alloc_limit)) = true
  rw [List.append_nil, target_reserved_val]
  have E1 : decide (bv_unsigned (0x2aaaaab000 : word) % page_size = 0) = true := by decide
  have E2 : decide (0 < bv_unsigned (0x2aaaaab000 : word)) = true := by decide
  have E3 : decide (bv_unsigned (0x2aaaaab000 : word) + g ≤
      bv_unsigned sp - stack_max_size) = true := by
    apply decide_eq_true
    imm_norm
    change 0x7fff80000000 ≤ bv_unsigned sp at Hsp
    change 0x2aaaaab000 + g ≤ bv_unsigned sp - 8388608
    omega
  rw [E1, E2, E3]
  simp only [Bool.true_and, Bool.and_eq_true]
  constructor
  · apply LinuxProcessSemantics.Common.AllocSim.region_free_above
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide
  · apply decide_eq_true
    change 0 + g ≤ 0x8000000000
    omega

theorem target_grant_unpack (inp : ProcInput) (hint brk0 mb sp aG : word) (g : Int)
    (Hg0 : 0 ≤ g) (Hg64 : g < 2 ^ 64)
    (Hg : grant_ok hint
      (init_model (segments_reserved target_segs) brk0 mb sp target_alloc_limit inp)
      aG g = true) :
    0 < bv_unsigned aG ∧ bv_unsigned aG + g ≤ bv_unsigned sp - stack_max_size ∧
      (bv_unsigned aG + g ≤ 0x1000000 ∨ 0x1001000 ≤ bv_unsigned aG) ∧
      (bv_unsigned aG + g ≤ 0x1001000 ∨ 0x1002000 ≤ bv_unsigned aG) := by
  obtain ⟨_, Hpos, Hceil, Hfree, _⟩ := grant_ok_unpack _ _ _ _ Hg
  change bv_unsigned aG + g ≤ bv_unsigned sp - stack_max_size at Hceil
  change region_free (segments_reserved target_segs ++ []) aG (Z_to_bv 64 g) = true at Hfree
  rw [target_reserved_val, List.append_nil] at Hfree
  obtain ⟨Hda, Hfree⟩ := region_free_cons _ _ _ _ _ Hfree
  obtain ⟨Hdb, _⟩ := region_free_cons _ _ _ _ _ Hfree
  change bv_unsigned aG + bv_unsigned (Z_to_bv 64 g) ≤ 0x1000000 ∨
    0x1000000 + 0x1000 ≤ bv_unsigned aG at Hda
  change bv_unsigned aG + bv_unsigned (Z_to_bv 64 g) ≤ 0x1001000 ∨
    0x1001000 + 0x1000 ≤ bv_unsigned aG at Hdb
  rw [u_Z2bv g Hg0 Hg64] at Hda Hdb
  exact ⟨Hpos, Hceil, Hda, Hdb⟩

theorem target_grant_avoids (aZ g x k : Int)
    (Hda : aZ + g ≤ 0x1000000 ∨ 0x1001000 ≤ aZ)
    (Hdb : aZ + g ≤ 0x1001000 ∨ 0x1002000 ≤ aZ)
    (Hx1 : aZ ≤ x) (Hx2 : x + k ≤ aZ + g) :
    range_avoids_ro_segs target_segs x k = true := by
  change ((false || !(decide (0x1000000 < x + k) && decide (x < 0x1001000))) &&
    ((false || !(decide (0x1001000 < x + k) && decide (x < 0x1002000))) && true)) = true
  have Hb0 : (decide (0x1000000 < x + k) && decide (x < 0x1001000)) = false := by
    rcases Hda with H | H
    · rw [decide_eq_false (show ¬ 0x1000000 < x + k by omega), Bool.false_and]
    · rw [decide_eq_false (show ¬ x < 0x1001000 by omega), Bool.and_false]
  have Hb1 : (decide (0x1001000 < x + k) && decide (x < 0x1002000)) = false := by
    rcases Hdb with H | H
    · rw [decide_eq_false (show ¬ 0x1001000 < x + k by omega), Bool.false_and]
    · rw [decide_eq_false (show ¬ x < 0x1002000 by omega), Bool.and_false]
  rw [Hb0, Hb1]
  rfl

-- The proof, generic over argv/envp and the stack pointer.

theorem asp_lo_num (asp : word) (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) :
    0x7fff80000000 ≤ bv_unsigned asp := Hsp_lo

theorem asp_hi_num (asp : word) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    bv_unsigned asp ≤ 0x800000000000 := Hsp_hi

def targcN (inp : ProcInput) : word := len_word inp.in_argv

def awmem (inp : ProcInput) (asp : word) (arnd : EntryDraw) : word → Option byte :=
  wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd

theorem u_targcN (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (targcN inp) = (inp.in_argv.length : Int) := by
  have H := valid_argv_len inp.in_argv Hva
  unfold targcN len_word
  apply u_Z2bv <;> omega

theorem targcN_le (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (targcN inp) ≤ 1024 := by
  rw [u_targcN inp Hva]
  exact valid_argv_len inp.in_argv Hva

theorem targc_le_nat (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    inp.in_argv.length ≤ 1024 := by
  have H := valid_argv_len inp.in_argv Hva
  omega

theorem targN_small (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (i : Nat) (Hi : i ≤ inp.in_argv.length) : (i : Int) < 2 ^ 63 := by
  have H := targc_le_nat inp Hva
  omega

theorem tiN_le (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (i : Nat) (Hi : i ≤ inp.in_argv.length) : (i : Int) ≤ 1024 := by
  have H := targc_le_nat inp Hva
  omega

/-- No-overflow bound for the initial stack image (feeds the stack-read
lemmas' new side conditions). -/
theorem target_bsb_nw (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    bv_unsigned asp + ((build_stack_bytes target_phdrs asp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap arnd).length : Int) < 2 ^ 64 := by
  have H := bsb_bound target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd Hva Hve
  have Hhi := asp_hi_num asp Hsp_hi
  omega

/-- Memory after _start's two frame stores. -/
def smem (inp : ProcInput) (asp : word) (arnd : EntryDraw) : word → Option byte :=
  wbytes (wbytes (awmem inp asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))

/-- Memory after run's frame stores (argc-agnostic: they always run). -/
def tfmem (inp : ProcInput) (asp : word) (arnd : EntryDraw) : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (smem inp asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 24)) (word_to_le_bytes 8 (0x1001178 : word)))
    (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 asp))
    (Z_to_bv 64 (bv_unsigned asp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0))

theorem rdn_awmem_stack (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (a : word) (k : Nat) (Ha : bv_unsigned asp ≤ bv_unsigned a)
    (Hk : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn target_segs (awmem inp asp arnd) a k =
      rdn target_segs (stack_to_mem asp (entry_stack_image target_phdrs asp
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd)) a k := by
  exact rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ Ha Hk

theorem rdn_smem_above (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (a : word) (k : Nat) (Ha : bv_unsigned asp ≤ bv_unsigned a)
    (Hk : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn target_segs (smem inp asp arnd) a k = rdn target_segs (awmem inp asp arnd) a k := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold smem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hk]

theorem rdn_tfmem_above (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (a : word) (k : Nat) (Ha : bv_unsigned asp ≤ bv_unsigned a)
    (Hk : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn target_segs (tfmem inp asp arnd) a k = rdn target_segs (awmem inp asp arnd) a k := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hk]
  exact rdn_smem_above inp asp arnd Hsp_lo Hsp_hi a k Ha Hk

-- Per-argument reads.

def tsptr (inp : ProcInput) (asp : word) (k : Nat) : word :=
  cat_argv_ptr asp inp.in_argv inp.in_envp k

theorem tsptr_bounds (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    bv_unsigned asp ≤ bv_unsigned (tsptr inp asp k) ∧
      bv_unsigned (tsptr inp asp k) + ((inp.in_argv.getD k []).length : Int) + 1 < 2 ^ 64 := by
  unfold tsptr
  apply argv_ptr_bounds _ _ _ _ Hva Hve Hk
  have Hhi := asp_hi_num asp Hsp_hi
  unfold argv_layout_slack
  omega

theorem tread_arg_ptr (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    rdn target_segs (tfmem inp asp arnd)
      (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (k : Int))) 8 =
      some (word_le8 (tsptr inp asp k)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have Hlen := valid_argv_len inp.in_argv Hva
  have HkZ : (k : Int) ≤ 1024 := by omega
  have E : Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (k : Int)) =
      asp + nat_to_word (8 + 8 * k) := by
    rw [word_add_nat]
    congr 1 <;> omega
  rw [E, rdn_tfmem_above inp asp arnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_awmem_stack inp asp arnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k _ _ _ _ _ _ _ _ _ Hk (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

theorem tread_arg_byte (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (k j : Nat) (Hk : k < inp.in_argv.length) (Hj : j ≤ (inp.in_argv.getD k []).length) :
    rdn target_segs (tfmem inp asp arnd) (tsptr inp asp k + nat_to_word j) 1 =
      some [byte_at (inp.in_argv.getD k []) j] := by
  obtain ⟨Hge, Hup⟩ := tsptr_bounds inp Hva Hve asp Hsp_hi k Hk
  have Hslen := valid_argv_str_len inp.in_argv k Hva Hk
  have Hasp := u64_range asp
  have Hptr := u64_range (tsptr inp asp k)
  rw [rdn_tfmem_above inp asp arnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_awmem_stack inp asp arnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_byte_k _ _ _ _ _ _ _ _ _ _ Hk Hj (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

theorem targ_bytes_k (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    ∀ b ∈ inp.in_argv.getD k [], bv_unsigned b < 256 := by
  exact valid_argv_str_bytes _ _ Hva Hk

theorem targ_nz_k (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (k : Nat) (Hk : k < inp.in_argv.length) :
    Z_to_bv 8 0 ∉ inp.in_argv.getD k [] := by
  exact valid_argv_str_nz _ _ Hva Hk

-- Frame-slot read-back.

theorem tfread_slot_ra (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    rdn target_segs (tfmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x1001178 : word)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _
        (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

theorem tfread_slot_s0 (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    rdn target_segs (tfmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _
        (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

theorem tfread_slot_0 (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (a : word) (Ha : a ∈ [Z_to_bv 64 (bv_unsigned asp - 40), Z_to_bv 64 (bv_unsigned asp - 48),
      Z_to_bv 64 (bv_unsigned asp - 56), Z_to_bv 64 (bv_unsigned asp - 64)]) :
    rdn target_segs (tfmem inp asp arnd) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
  rcases Ha with rfl | rfl | rfl | rfl <;>
    repeat first
      | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
      | rw [rdn_wbytes_disjoint _ _ _ _ _ _
          (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
      | rw [rdn_wbytes_below _ _ _ _ _ _
          (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

/-- The six frame reloads, the stack pop, the run function's return, and
crt's `li a7,93` before the exit ecall. The saved `s0` is symbolic;
the saved return address fixes the return target. -/
theorem target_epilogue (asp : word)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (H10 : reg_get regs 10 = code)
    (Hra : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x1001178 : word)))
    (Hs0 : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp))
    (Hsl : ∀ a : word,
      a ∈ [Z_to_bv 64 (bv_unsigned asp - 40), Z_to_bv 64 (bv_unsigned asp - 48),
        Z_to_bv 64 (bv_unsigned asp - 56), Z_to_bv 64 (bv_unsigned asp - 64)] →
      rdn target_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    ∃ regs', bv_unsigned (getr regs' 17) = 93 ∧ reg_get regs' 10 = code ∧
      msteps target_segs (mkst regs 0x10012b0 mem arom)
        { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := 0x100117c,
          ms_svc_pending := some (getr regs' 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := mem, ms_rom := arom } := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  let R := regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
    1 (0x1001178 : word)) 8 asp) 9 (Z_to_bv 64 0)) 18 (Z_to_bv 64 0))
    19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 0))
    2 (Z_to_bv 64 (bv_unsigned asp - 16))) 17 (Z_to_bv 64 93)
  refine ⟨R, ?_, ?_, ?_⟩
  · dsimp only [R]; getr_resolve; regupd_resolve; rfl
  · dsimp only [R]; regupd_resolve; exact H10
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := word_to_le_bytes 8 (0x1001178 : word)) (v := (0x1001178 : word))
      (hfetch := TF_10012b0) (hecall := rfl) (hdecode := TD_10012b0)
    · getr_resolve; regupd_resolve; rw [H2]
      change rdn target_segs mem
        (v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 40) 8 = _
      have E : v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 40 =
          Z_to_bv 64 (bv_unsigned asp - 24) := by
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1 <;> omega
      rw [E]
      exact Hra
    · rw [bytes_le_to_Z_8]
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := word_to_le_bytes 8 asp) (v := asp)
      (hfetch := TF_10012b4) (hecall := rfl) (hdecode := TD_10012b4)
    · getr_resolve; regupd_resolve; rw [H2]
      change rdn target_segs mem
        (v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 32) 8 = _
      have E : v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 32 =
          Z_to_bv 64 (bv_unsigned asp - 32) := by
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1 <;> omega
      rw [E]
      exact Hs0
    · rw [bytes_le_to_Z_8]
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := word_to_le_bytes 8 (Z_to_bv 64 0)) (v := (Z_to_bv 64 0))
      (hfetch := TF_10012b8) (hecall := rfl) (hdecode := TD_10012b8)
    · getr_resolve; regupd_resolve; rw [H2]
      change rdn target_segs mem
        (v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 24) 8 = _
      have E : v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 24 =
          Z_to_bv 64 (bv_unsigned asp - 40) := by
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1 <;> omega
      rw [E]
      apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, eq_self]
    · rw [bytes_le_to_Z_8]
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := word_to_le_bytes 8 (Z_to_bv 64 0)) (v := (Z_to_bv 64 0))
      (hfetch := TF_10012bc) (hecall := rfl) (hdecode := TD_10012bc)
    · getr_resolve; regupd_resolve; rw [H2]
      change rdn target_segs mem
        (v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 16) 8 = _
      have E : v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 16 =
          Z_to_bv 64 (bv_unsigned asp - 48) := by
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1 <;> omega
      rw [E]
      apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, eq_self]
    · rw [bytes_le_to_Z_8]
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := word_to_le_bytes 8 (Z_to_bv 64 0)) (v := (Z_to_bv 64 0))
      (hfetch := TF_10012c0) (hecall := rfl) (hdecode := TD_10012c0)
    · getr_resolve; regupd_resolve; rw [H2]
      change rdn target_segs mem
        (v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 8) 8 = _
      have E : v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 8 =
          Z_to_bv 64 (bv_unsigned asp - 56) := by
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1 <;> omega
      rw [E]
      apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, eq_self]
    · rw [bytes_le_to_Z_8]
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := word_to_le_bytes 8 (Z_to_bv 64 0)) (v := (Z_to_bv 64 0))
      (hfetch := TF_10012c4) (hecall := rfl) (hdecode := TD_10012c4)
    · getr_resolve; regupd_resolve; rw [H2]
      change rdn target_segs mem
        (v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 0) 8 = _
      have E : v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 0 =
          Z_to_bv 64 (bv_unsigned asp - 64) := by
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1 <;> omega
      rw [E]
      apply Hsl; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, eq_self]
    · rw [bytes_le_to_Z_8]
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp - 16))
      (hf := TF_10012c8) (he := rfl) (hd := TD_10012c8) (hrd := rfl)
    getr_resolve; regupd_resolve; rw [H2]
    change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 48 = _
    unfold v_addi
    rw [u_Z2bv _ (by omega) (by omega)]
    congr 1 <;> omega
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_jalr_x0 (tgt := (0x1001178 : word))
      (hf := TF_10012cc) (he := rfl) (hd := TD_10012cc)
    getr_resolve; regupd_resolve; rfl
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 93)
      (hf := TF_1001178) (he := rfl) (hd := TD_1001178) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_100117c rfl
  exact msteps.mst_refl _

set_option maxHeartbeats 800000 in
/-- From the entry to the argc branch at `0x10011a4`, with the run frame
stored: sp = asp-64, s0 = asp+8, a0 = argc, a1 = 2.
The entry and run frames spill eight words and load argc; the initial
callee-saved registers are zero, so the resulting memory is `tfmem`. -/
theorem target_to_dispatch (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    ∃ regsP,
      reg_get regsP 2 = Z_to_bv 64 (bv_unsigned asp - 64) ∧
      reg_get regsP 8 = Z_to_bv 64 (bv_unsigned asp + 8) ∧
      reg_get regsP 10 = targcN inp ∧ reg_get regsP 11 = Z_to_bv 64 2 ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regsP 0x10011a4 (tfmem inp asp arnd) arom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  let R0 := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp
  let R1 := regupd R0 2 (Z_to_bv 64 (bv_unsigned asp - 16))
  let R2 := regupd R1 8 asp
  let R3 := regupd R2 10 (targcN inp)
  let R4 := regupd R3 11 (Z_to_bv 64 (bv_unsigned asp + 8))
  let R5 := regupd R4 1 (0x1001170 : word)
  let R6 := regupd R5 1 (0x1001178 : word)
  let R7 := regupd R6 2 (Z_to_bv 64 (bv_unsigned asp - 64))
  let R8 := regupd R7 8 (Z_to_bv 64 (bv_unsigned asp + 8))
  let R9 := regupd R8 11 (Z_to_bv 64 2)
  refine ⟨R9, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [R9, R8, R7]; regupd_resolve; rfl
  · dsimp only [R9, R8]; regupd_resolve; rfl
  · dsimp only [R9, R8, R7, R6, R5, R4, R3]; regupd_resolve; rfl
  · dsimp only [R9]; regupd_resolve; rfl
  rw [init_mkst]
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp - 16))
      (hf := TF_1001158) (he := rfl) (hd := TD_1001158) (hrd := rfl)
    getr_resolve; regupd_resolve; rfl
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 8)) (v := (Z_to_bv 64 0))
      (hf := TF_100115c) (he := rfl) (hd := TD_100115c)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 16)) 8 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 16)) (v := (Z_to_bv 64 0))
      (hf := TF_1001160) (he := rfl) (hd := TD_1001160)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 16)) 0 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := asp)
      (hf := TF_1001164) (he := rfl) (hd := TD_1001164) (hrd := rfl)
    getr_resolve; regupd_resolve
    change v_addi (Z_to_bv 64 (bv_unsigned asp - 16)) 16 = asp
    unfold v_addi
    rw [u_Z2bv _ (by omega) (by omega)]
    rw [Int.sub_add_cancel]
    apply bv_eq_of_unsigned
    exact u_Z2bv _ (by omega) (by omega)
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := word_le8 (targcN inp)) (v := targcN inp)
      (hfetch := TF_1001168) (hecall := rfl) (hdecode := TD_1001168)
    · getr_resolve; regupd_resolve
      change rdn target_segs (smem inp asp arnd) (v_addi asp 0) 8 = _
      rw [v_addi_0, rdn_smem_above inp asp arnd Hsp_lo Hsp_hi _ _ (by omega) (by omega)]
      rw [rdn_awmem_stack inp asp arnd _ _ (by omega) (by omega)]
      exact read_argc _ _ _ _ _ _ _ _ (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    · exact bytes_le_n_to_le_8 _
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp + 8))
      (hf := TF_100116c) (he := rfl) (hd := TD_100116c) (hrd := rfl)
    getr_resolve; regupd_resolve; rfl
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_auipc_at (v := (0x1001170 : word))
      (hf := TF_1001170) (he := rfl) (hd := TD_1001170) (hrd := rfl)
    bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_jalr_link (tgt := (0x1001170 : word))
      (hf := TF_1001174) (he := rfl) (hd := TD_1001174) (hrd := rfl)
    getr_resolve; regupd_resolve; rfl
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp - 64))
      (hf := TF_1001180) (he := rfl) (hd := TD_1001180) (hrd := rfl)
    getr_resolve; regupd_resolve
    change v_addi (Z_to_bv 64 (bv_unsigned asp - 16)) (-48) = _
    unfold v_addi
    rw [u_Z2bv _ (by omega) (by omega)]
    congr 1 <;> omega
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 24)) (v := (0x1001178 : word))
      (hf := TF_1001184) (he := rfl) (hd := TD_1001184)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 40 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 32)) (v := asp)
      (hf := TF_1001188) (he := rfl) (hd := TD_1001188)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 32 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 40)) (v := (Z_to_bv 64 0))
      (hf := TF_100118c) (he := rfl) (hd := TD_100118c)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 24 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 48)) (v := (Z_to_bv 64 0))
      (hf := TF_1001190) (he := rfl) (hd := TD_1001190)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 16 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 56)) (v := (Z_to_bv 64 0))
      (hf := TF_1001194) (he := rfl) (hd := TD_1001194)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 8 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 64)) (v := (Z_to_bv 64 0))
      (hf := TF_1001198) (he := rfl) (hd := TD_1001198)
    · getr_resolve; regupd_resolve
      change v_addi (Z_to_bv 64 (bv_unsigned asp - 64)) 0 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · solve_store_ok
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp + 8))
      (hf := TF_100119c) (he := rfl) (hd := TD_100119c) (hrd := rfl)
    getr_resolve; regupd_resolve; apply v_addi_0
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 2)
      (hf := TF_10011a0) (he := rfl) (hd := TD_10011a0) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  exact msteps.mst_refl _

/-- argc < 2: no output, exit 2. -/
theorem target_wexit_lt2 (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hlt2 : inp.in_argv.length < 2) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 2) := by
  obtain ⟨regsP, P2, _P8, P10, P11, Hms⟩ :=
    target_to_dispatch inp Hva Hve asp arnd Hsp_lo Hsp_hi
  apply msteps_to_wexit _ _ _ _ _ Hms
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_bltu_tk (Hf := TF_10011a4) (He := rfl) (Hd := TD_10011a4)
    getr_resolve; rw [P10, P11, c_ltu_ltb, u_targcN inp Hva]
    apply decide_eq_true
    change (inp.in_argv.length : Int) < 2
    omega
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 2)
      (hf := TF_10012ac) (he := rfl) (hd := TD_10012ac) (hrd := rfl)
    getr_resolve; rw [P11]; apply v_addi_0
  step_simpl
  obtain ⟨regsE, HE17, HE10, HmsE⟩ := target_epilogue asp Hsp_lo Hsp_hi
    (regupd regsP 10 (Z_to_bv 64 2)) (tfmem inp asp arnd) (Z_to_bv 64 2)
    (by regupd_resolve; exact P2) (by regupd_resolve; rfl)
    (tfread_slot_ra inp asp arnd Hsp_lo Hsp_hi)
    (tfread_slot_s0 inp asp arnd Hsp_lo Hsp_hi)
    (tfread_slot_0 inp asp arnd Hsp_lo Hsp_hi)
  apply msteps_to_wexit _ _ _ _ _ HmsE
  exact tw_exit_coden _ _ _ _ _ _ HE17 HE10 (by decide)

-- Join-length theory (target-side duplicates).

def ttotn (inp : ProcInput) : Nat := total_arg_bytes_nat inp.in_argv.tail

def ttot (inp : ProcInput) : word := nat_to_word (ttotn inp)

theorem ttl_nonnil (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    inp.in_argv.tail ≠ [] := by
  intro H
  have := length_tl_list inp.in_argv
  rw [H] at this
  simp only [List.length_nil] at this
  omega

theorem tab_join1_t (l : List (List byte)) :
    total_arg_bytes_nat l = (join1 l).length + (if l.length == 0 then 0 else 1) := by
  cases l with
  | nil => simp only [join1, total_arg_bytes_nat, List.foldr_nil, List.length_nil]; rfl
  | cons a l =>
    simp only [List.length_cons, beq_iff_eq, Nat.add_one_ne_zero, ↓reduceIte]
    exact (length_join1 _ (List.cons_ne_nil _ _)).symm

theorem ttotn_ge1 (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    1 ≤ ttotn inp := by
  unfold ttotn
  rw [tab_join1_t]
  have H := ttl_nonnil inp Hge2
  have Hlen : inp.in_argv.tail.length ≠ 0 := by
    intro E; exact H (List.length_eq_zero_iff.mp E)
  simp only [beq_iff_eq, Hlen, ↓reduceIte]
  omega

theorem ttotn_bound (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    (ttotn inp : Int) ≤ 2097152 := by
  have Hb := valid_argv_tab inp.in_argv Hva
  have Hsplit := tab_app (inp.in_argv.take 1) (inp.in_argv.drop 1)
  rw [List.take_append_drop] at Hsplit
  have Htl : inp.in_argv.tail = inp.in_argv.drop 1 := by cases inp.in_argv <;> rfl
  unfold ttotn
  rw [Htl]
  omega

theorem u_ttot (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (ttot inp) = (ttotn inp : Int) := by
  unfold ttot
  apply u_ntw
  have := ttotn_bound inp Hva
  omega

theorem ttot_ge1 (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hge2 : 2 ≤ inp.in_argv.length) : 1 ≤ bv_unsigned (ttot inp) := by
  rw [u_ttot inp Hva]
  have := ttotn_ge1 inp Hge2
  omega

theorem ttot_bound (inp : ProcInput) (Hva : valid_argv inp.in_argv) :
    bv_unsigned (ttot inp) ≤ 2097152 := by
  rw [u_ttot inp Hva]
  exact ttotn_bound inp Hva

theorem tjoin1_tl_len_nat (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    (join1 inp.in_argv.tail).length = ttotn inp - 1 := by
  have := length_join1 inp.in_argv.tail (ttl_nonnil inp Hge2)
  unfold ttotn
  omega

theorem tjout_len_nat (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    (jout inp.in_argv).length = ttotn inp := by
  unfold jout
  rw [List.length_append, tjoin1_tl_len_nat inp Hge2]
  have := ttotn_ge1 inp Hge2
  simp only [List.length_cons, List.length_nil]
  omega

theorem tjout_len_w (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hge2 : 2 ≤ inp.in_argv.length) : word_to_nat (ttot inp) = (jout inp.in_argv).length := by
  rw [tjout_len_nat inp Hge2]
  apply word_to_nat_ntw
  have := ttotn_bound inp Hva
  omega

theorem tlength_tl_av (inp : ProcInput) : inp.in_argv.tail.length = inp.in_argv.length - 1 :=
  length_tl_list inp.in_argv

theorem tjpre_step (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i)
    (Hi : i ≤ inp.in_argv.tail.length) :
    (join1 (inp.in_argv.tail.take i)).length =
      (join1 (inp.in_argv.tail.take (i - 1))).length +
        (inp.in_argv.getD i []).length + (if i == 1 then 0 else 1) := by
  have E : i - 1 + 1 = i := by omega
  conv => lhs; rw [← E, firstn_S_nth _ _ _ [] (by omega)]
  rw [join1_snoc, List.length_append, length_wjoin, nth_tl, E, tab_join1_t,
    List.length_take, Nat.min_eq_left (by omega)]
  simp only [beq_iff_eq]
  by_cases H : i = 1
  · subst i; simp only [Nat.sub_self, ↓reduceIte]; omega
  · simp only [show i - 1 ≠ 0 by omega, H, ↓reduceIte]
    omega

/-- Length of the join1 prefix at outer index `i` (args 1..i-1 done). -/
def pbJ (inp : ProcInput) (i : Nat) : Nat :=
  (join1 (inp.in_argv.tail.take (i - 1))).length

theorem pbJ_1 (inp : ProcInput) : pbJ inp 1 = 0 := by
  simp only [pbJ, Nat.sub_self, List.take_zero, join1, List.length_nil]

theorem pbJ_le (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) (i : Nat) :
    pbJ inp i ≤ ttotn inp - 1 := by
  have Hj := tab_join1_t (inp.in_argv.tail.take (i - 1))
  have Hm : total_arg_bytes_nat (inp.in_argv.tail.take (i - 1)) ≤
      total_arg_bytes_nat inp.in_argv.tail := by
    have H := tab_app (inp.in_argv.tail.take (i - 1)) (inp.in_argv.tail.drop (i - 1))
    rw [List.take_append_drop] at H
    omega
  have Hg1 := ttotn_ge1 inp Hge2
  unfold ttotn at Hg1 ⊢
  unfold pbJ
  cases El : (inp.in_argv.tail.take (i - 1)).length with
  | zero =>
    rw [List.length_eq_zero_iff.mp El]
    simp only [join1, List.length_nil]
    omega
  | succ n =>
    simp only [El, beq_iff_eq, Nat.add_one_ne_zero, ↓reduceIte] at Hj
    omega

theorem pbJ_last (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    pbJ inp inp.in_argv.length = ttotn inp - 1 := by
  unfold pbJ
  rw [← tlength_tl_av inp, List.take_length]
  exact tjoin1_tl_len_nat inp Hge2

theorem pbJ_stepN (inp : ProcInput) (i : Nat) (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) :
    pbJ inp (i + 1) = pbJ inp i + (inp.in_argv.getD i []).length +
      (if i == 1 then 0 else 1) := by
  unfold pbJ
  rw [Nat.add_sub_cancel]
  exact tjpre_step inp i H1 (by rw [tlength_tl_av]; omega)

theorem tjoin_step (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length)
    (i : Nat) (H2 : 2 ≤ i) (Hi : i < inp.in_argv.length) :
    join1 (inp.in_argv.tail.take i) =
      join1 (inp.in_argv.tail.take (i - 1)) ++ Z_to_bv 8 32 :: inp.in_argv.getD i [] := by
  have E : i - 1 + 1 = i := by omega
  conv => lhs; rw [← E, firstn_S_nth _ _ _ [] (by rw [tlength_tl_av]; omega)]
  rw [join1_snoc, wjoin_join1 _ (firstn_nonnil _ _ (by omega) (ttl_nonnil inp Hge2)),
    nth_tl, E, List.append_assoc]
  rfl

theorem tjoin_1 (inp : ProcInput) (Hge2 : 2 ≤ inp.in_argv.length) :
    join1 (inp.in_argv.tail.take 1) = inp.in_argv.getD 1 [] := by
  cases H : inp.in_argv with
  | nil => simp only [H, List.length_nil] at Hge2; omega
  | cons a l =>
    cases l with
    | nil => simp only [H, List.length_cons, List.length_nil] at Hge2; omega
    | cons b l => simp only [List.tail_cons, List.take_succ_cons, List.take_zero, join1]; rfl

-- slen callee: loop at 0x10012d4, exit at 0x10012e4.

theorem target_slen (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (k : Nat) (Hk : k < inp.in_argv.length) (d j : Nat) (regs : bvmap 5 word)
    (Hjd : j + d = (inp.in_argv.getD k []).length)
    (Hr10 : reg_get regs 10 = tsptr inp asp k) (Hr11 : reg_get regs 11 = nat_to_word j) :
    ∃ regs',
      (∀ r : reg, r ≠ 11 → r ≠ 12 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 11 = nat_to_word (inp.in_argv.getD k []).length + 1 ∧
      msteps target_segs (mkst regs 0x10012d4 (tfmem inp asp arnd) arom)
        (mkst regs' 0x10012e4 (tfmem inp asp arnd) arom) := by
  have Hnz := targ_nz_k inp Hva k Hk
  have Hslen := valid_argv_str_len inp.in_argv k Hva Hk
  induction d generalizing j regs with
  | zero =>
    have Hj : j = (inp.in_argv.getD k []).length := by omega
    let regs1 := regupd regs 12 (tsptr inp asp k + nat_to_word j)
    let regs2 := regupd regs1 12 (Z_to_bv 64 0)
    let regs3 := regupd regs2 11 (nat_to_word (j + 1))
    refine ⟨regs3, ?_, ?_, ?_⟩
    · intro r H11 H12
      dsimp only [regs3, regs2, regs1]
      rw [regupd_other _ _ _ _ H11, regupd_other _ _ _ _ H12, regupd_other _ _ _ _ H12]
    · dsimp only [regs3]; rw [regupd_same, Hj]; exact ntw_S _
    apply msteps.mst_step _ _ _ rfl
    · apply step_add_at (v := tsptr inp asp k + nat_to_word j)
        (hf := TF_10012d4) (he := rfl) (hd := TD_10012d4) (hrd := rfl)
      getr_resolve; rw [Hr10, Hr11, v_add_word]
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_lbu (b := Z_to_bv 8 0)
        (hfetch := TF_10012d8) (hecall := rfl) (hdecode := TD_10012d8)
      getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
      rw [Hj]
      have Hrd := tread_arg_byte inp Hva Hve asp arnd Hsp_lo Hsp_hi k
        (inp.in_argv.getD k []).length Hk (Nat.le_refl _)
      rw [byte_at_len] at Hrd
      exact Hrd
    step_simpl
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := nat_to_word (j + 1))
        (hf := TF_10012dc) (he := rfl) (hd := TD_10012dc) (hrd := rfl)
      getr_resolve; regupd_resolve; rw [Hr11]
      apply v_addi_Sj; omega
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_bne_ft (hf := TF_10012e0) (he := rfl) (hd := TD_10012e0)
      getr_resolve; regupd_resolve
      exact c_eq_0_true
    norm_pc
    exact msteps.mst_refl _
  | succ d IH =>
    have Hjlt : j < (inp.in_argv.getD k []).length := by omega
    let b := byte_at (inp.in_argv.getD k []) j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hnz Hjlt
    let regs1 := regupd regs 12 (tsptr inp asp k + nat_to_word j)
    let regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 11 (nat_to_word (j + 1))
    obtain ⟨regs', Hag, H11, Hms⟩ := IH (j + 1) regs3 (by omega)
      (by dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr10)
      (by dsimp only [regs3]; regupd_resolve; rfl)
    refine ⟨regs', ?_, H11, ?_⟩
    · intro r H11' H12'
      rw [Hag r H11' H12']
      dsimp only [regs3, regs2, regs1]
      rw [regupd_other _ _ _ _ H11', regupd_other _ _ _ _ H12', regupd_other _ _ _ _ H12']
    apply msteps.mst_step _ _ _ rfl
    · apply step_add_at (v := tsptr inp asp k + nat_to_word j)
        (hf := TF_10012d4) (he := rfl) (hd := TD_10012d4) (hrd := rfl)
      getr_resolve; rw [Hr10, Hr11, v_add_word]
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_lbu (b := b)
        (hfetch := TF_10012d8) (hecall := rfl) (hdecode := TD_10012d8)
      getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
      exact tread_arg_byte inp Hva Hve asp arnd Hsp_lo Hsp_hi k j Hk (by omega)
    step_simpl
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := nat_to_word (j + 1))
        (hf := TF_10012dc) (he := rfl) (hd := TD_10012dc) (hrd := rfl)
      getr_resolve; regupd_resolve; rw [Hr11]
      apply v_addi_Sj; omega
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_bne_tk (hf := TF_10012e0) (he := rfl) (hd := TD_10012e0)
      getr_resolve; regupd_resolve
      apply c_eq_0_false
      rw [u_zext8]
      exact byte_nz_u b Hbnz
    norm_pc
    exact Hms

-- Outer length loop: 0x10011bc .. 0x10011e0.

set_option maxHeartbeats 1000000 in
theorem target_length (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (f i : Nat) (regs : bvmap 5 word)
    (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) (Hf : inp.in_argv.length - i ≤ f)
    (H9 : reg_get regs 9 = targcN inp) (H18 : reg_get regs 18 = nat_to_word (pbJ inp i))
    (H19 : reg_get regs 19 = Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (i : Int)))
    (H20 : reg_get regs 20 = nat_to_word i) :
    ∃ regs',
      (∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 18 →
        r ≠ 19 → r ≠ 20 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 18 = nat_to_word (ttotn inp - 1) ∧
      msteps target_segs (mkst regs 0x10011bc (tfmem inp asp arnd) arom)
        (mkst regs' 0x10011e4 (tfmem inp asp arnd) arom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  induction f generalizing i regs with
  | zero => omega
  | succ f IH =>
    have HiZ := tiN_le inp Hva i (by omega)
    have HSiZ := tiN_le inp Hva (i + 1) (by omega)
    let regs1 := regupd regs 10 (tsptr inp asp i)
    let regs2 := regupd regs1 1 (0x10011c0 : word)
    let regs3 := regupd regs2 1 (0x10011c8 : word)
    let regs4 := regupd regs3 11 (Z_to_bv 64 0)
    have Hms4 : msteps target_segs (mkst regs 0x10011bc (tfmem inp asp arnd) arom)
        (mkst regs4 0x10012d4 (tfmem inp asp arnd) arom) := by
      apply msteps.mst_step _ _ _ rfl
      · apply step_ld (bs := word_le8 (tsptr inp asp i)) (v := tsptr inp asp i)
          (hfetch := TF_10011bc) (hecall := rfl) (hdecode := TD_10011bc)
        · getr_resolve; rw [H19]; imm_norm; rw [v_addi_0]
          exact tread_arg_ptr inp Hva Hve asp arnd Hsp_lo Hsp_hi i Hi
        · exact bytes_le_n_to_le_8 _
      step_simpl
      apply msteps.mst_step _ _ _ rfl
      · apply step_auipc_at (v := (0x10011c0 : word))
          (hf := TF_10011c0) (he := rfl) (hd := TD_10011c0) (hrd := rfl)
        bveq
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_jalr_link (tgt := (0x10011c0 : word))
          (hf := TF_10011c4) (he := rfl) (hd := TD_10011c4) (hrd := rfl)
        getr_resolve; regupd_resolve; rfl
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_addi_at (v := Z_to_bv 64 0)
          (hf := TF_10012d0) (he := rfl) (hd := TD_10012d0) (hrd := rfl)
        getr_resolve; bveq
      norm_pc
      exact msteps.mst_refl _
    obtain ⟨regs5, Hag5, H11_5, Hms5⟩ := target_slen inp Hva Hve asp arnd Hsp_lo Hsp_hi
      i Hi (inp.in_argv.getD i []).length 0 regs4 (by omega)
      (by dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; rfl)
      (by dsimp only [regs4]; regupd_resolve; rfl)
    have H1_5 : reg_get regs5 1 = (0x10011c8 : word) := by
      rw [Hag5 1 (by decide) (by decide)]
      dsimp only [regs4, regs3]; regupd_resolve; rfl
    let regs6 := regupd regs5 10 (nat_to_word (inp.in_argv.getD i []).length)
    have H20_6 : reg_get regs5 20 = nat_to_word i := by
      rw [Hag5 20 (by decide) (by decide)]
      dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; exact H20
    have H18_6 : reg_get regs5 18 = nat_to_word (pbJ inp i) := by
      rw [Hag5 18 (by decide) (by decide)]
      dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; exact H18
    let regs7 := regupd regs6 11 (if decide ((i : Int) < 2) then Z_to_bv 64 1 else Z_to_bv 64 0)
    let regs8 := regupd regs7 20 (nat_to_word (i + 1))
    let sep : Nat := if i == 1 then 0 else 1
    let regs9 := regupd regs8 11 (nat_to_word sep)
    let regsA := regupd regs9 11 (nat_to_word (pbJ inp i + sep))
    let regsB := regupd regsA 18 (nat_to_word (pbJ inp (i + 1)))
    let regsC := regupd regsB 19 (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * ((i + 1 : Nat) : Int)))
    have HmsC : msteps target_segs (mkst regs5 0x10012e4 (tfmem inp asp arnd) arom)
        (mkst regsC 0x10011e0 (tfmem inp asp arnd) arom) := by
      apply msteps.mst_step _ _ _ rfl
      · apply step_addi_at (v := nat_to_word (inp.in_argv.getD i []).length)
          (hf := TF_10012e4) (he := rfl) (hd := TD_10012e4) (hrd := rfl)
        getr_resolve; rw [H11_5]; exact v_addi_pred _
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_jalr_x0 (tgt := (0x10011c8 : word))
          (hf := TF_10012e8) (he := rfl) (hd := TD_10012e8)
        getr_resolve; regupd_resolve; exact H1_5
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_sltiu_at
          (v := if decide ((i : Int) < 2) then Z_to_bv 64 1 else Z_to_bv 64 0)
          (hf := TF_10011c8) (he := rfl) (hd := TD_10011c8) (hrd := rfl)
        getr_resolve; rw [H20_6]; imm_norm
        rw [v_sltiu_2, u_ntw i (by omega)]
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_addi_at (v := nat_to_word (i + 1))
          (hf := TF_10011cc) (he := rfl) (hd := TD_10011cc) (hrd := rfl)
        getr_resolve; regupd_resolve; rw [H20_6]
        apply v_addi_Sj; omega
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_xori_at (v := nat_to_word sep)
          (hf := TF_10011d0) (he := rfl) (hd := TD_10011d0) (hrd := rfl)
        getr_resolve; regupd_resolve; imm_norm
        dsimp only [sep]
        by_cases Ei : i = 1
        · subst i
          exact v_xori_1_1
        · have Hge : ¬ (i : Int) < 2 := by omega
          simp only [decide_eq_false Hge, Bool.false_eq_true, ↓reduceIte, beq_iff_eq,
            ite_eq_right Ei]
          exact v_xori_0_1
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_add_at (v := nat_to_word (pbJ inp i + sep))
          (hf := TF_10011d4) (he := rfl) (hd := TD_10011d4) (hrd := rfl)
        getr_resolve; regupd_resolve; rw [H18_6, v_add_word]
        exact nat_to_word_merge _ _
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_add_at (v := nat_to_word (pbJ inp (i + 1)))
          (hf := TF_10011d8) (he := rfl) (hd := TD_10011d8) (hrd := rfl)
        getr_resolve; regupd_resolve
        rw [v_add_word, nat_to_word_merge, pbJ_stepN inp i H1 Hi]
        congr 1
        dsimp only [sep]
        omega
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp + 8 + 8 * ((i + 1 : Nat) : Int)))
          (hf := TF_10011dc) (he := rfl) (hd := TD_10011dc) (hrd := rfl)
        getr_resolve; regupd_resolve
        rw [Hag5 19 (by decide) (by decide)]
        dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; rw [H19]
        change v_addi (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (i : Int))) 8 = _
        unfold v_addi
        rw [u_Z2bv _ (by omega) (by omega)]
        congr 1 <;> omega
      norm_pc
      exact msteps.mst_refl _
    have H20C : reg_get regsC 20 = nat_to_word (i + 1) := by
      dsimp only [regsC, regsB, regsA, regs9, regs8]; regupd_resolve; rfl
    have H9C : reg_get regsC 9 = targcN inp := by
      dsimp only [regsC, regsB, regsA, regs9, regs8, regs7, regs6]; regupd_resolve
      rw [Hag5 9 (by decide) (by decide)]
      dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; exact H9
    have H18C : reg_get regsC 18 = nat_to_word (pbJ inp (i + 1)) := by
      dsimp only [regsC, regsB]; regupd_resolve; rfl
    have H19C : reg_get regsC 19 =
        Z_to_bv 64 (bv_unsigned asp + 8 + 8 * ((i + 1 : Nat) : Int)) := by
      dsimp only [regsC]; regupd_resolve; rfl
    have HagC : ∀ r : reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 18 →
        r ≠ 19 → r ≠ 20 → reg_get regsC r = reg_get regs r := by
      intro r Hx1 Hx10 Hx11 Hx12 Hx18 Hx19 Hx20
      dsimp only [regsC, regsB, regsA, regs9, regs8, regs7, regs6]
      repeat rw [regupd_other _ _ _ _ (by assumption)]
      rw [Hag5 r Hx11 Hx12]
      dsimp only [regs4, regs3, regs2, regs1]
      repeat rw [regupd_other _ _ _ _ (by assumption)]
    by_cases Hlti : i + 1 < inp.in_argv.length
    · obtain ⟨regs', Hag', H18', Hms'⟩ := IH (i + 1) regsC (by omega) Hlti (by omega)
        H9C H18C H19C H20C
      refine ⟨regs', ?_, H18', ?_⟩
      · intro r h1 h10 h11 h12 h18 h19 h20
        rw [Hag' r h1 h10 h11 h12 h18 h19 h20]
        exact HagC r h1 h10 h11 h12 h18 h19 h20
      apply msteps_trans _ _ _ _ Hms4
      apply msteps_trans _ _ _ _ Hms5
      apply msteps_trans _ _ _ _ HmsC
      apply msteps.mst_step _ _ _ rfl
      · apply step_bne_tk (hf := TF_10011e0) (he := rfl) (hd := TD_10011e0)
        rw [getr_nz _ _ (by decide), getr_nz _ _ (by decide), H9C, H20C]
        apply c_eq_neq
        rw [u_targcN inp Hva, u_ntw (i + 1) (by omega)]
        omega
      norm_pc
      exact Hms'
    · have HSieq : i + 1 = inp.in_argv.length := by omega
      refine ⟨regsC, HagC, ?_, ?_⟩
      · rw [H18C, HSieq, pbJ_last inp Hge2]
      apply msteps_trans _ _ _ _ Hms4
      apply msteps_trans _ _ _ _ Hms5
      apply msteps_trans _ _ _ _ HmsC
      apply msteps.mst_step _ _ _ rfl
      · apply step_bne_ft (hf := TF_10011e0) (he := rfl) (hd := TD_10011e0)
        rw [getr_nz _ _ (by decide), getr_nz _ _ (by decide), H9C, H20C, HSieq]
        exact c_eq_refl _
      norm_pc
      exact msteps.mst_refl _

/-- From entry to `0x10011e4`, after the length loop. The argc dispatch
falls through and initializes the loop registers; its argc ≠ 1 test is
already settled by argc ≥ 2. -/
theorem target_after_length (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) :
    ∃ regsA,
      reg_get regsA 2 = Z_to_bv 64 (bv_unsigned asp - 64) ∧
      reg_get regsA 8 = Z_to_bv 64 (bv_unsigned asp + 8) ∧
      reg_get regsA 9 = targcN inp ∧ reg_get regsA 18 = nat_to_word (ttotn inp - 1) ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regsA 0x10011e4 (tfmem inp asp arnd) arom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  obtain ⟨regsP, P2, P8, P10, P11, HmsP⟩ :=
    target_to_dispatch inp Hva Hve asp arnd Hsp_lo Hsp_hi
  let RA := regupd (regupd (regupd (regupd regsP 9 (targcN inp)) 18 (Z_to_bv 64 0))
    19 (Z_to_bv 64 (bv_unsigned asp + 16))) 20 (nat_to_word 1)
  have Hms : msteps target_segs (mkst regsP 0x10011a4 (tfmem inp asp arnd) arom)
      (mkst RA 0x10011bc (tfmem inp asp arnd) arom) := by
    apply msteps.mst_step _ _ _ rfl
    · apply step_bltu_ft (hf := TF_10011a4) (he := rfl) (hd := TD_10011a4)
      getr_resolve; rw [P10, P11, c_ltu_ltb, u_targcN inp Hva]
      apply decide_eq_false
      change ¬ (inp.in_argv.length : Int) < 2
      omega
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := targcN inp)
        (hf := TF_10011a8) (he := rfl) (hd := TD_10011a8) (hrd := rfl)
      getr_resolve; rw [P10]; apply v_addi_0
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 0)
        (hf := TF_10011ac) (he := rfl) (hd := TD_10011ac) (hrd := rfl)
      getr_resolve; bveq
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp + 16))
        (hf := TF_10011b0) (he := rfl) (hd := TD_10011b0) (hrd := rfl)
      getr_resolve; regupd_resolve; rw [P8]
      change v_addi (Z_to_bv 64 (bv_unsigned asp + 8)) 8 = _
      unfold v_addi
      rw [u_Z2bv _ (by omega) (by omega)]
      congr 1 <;> omega
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := nat_to_word 1)
        (hf := TF_10011b4) (he := rfl) (hd := TD_10011b4) (hrd := rfl)
      getr_resolve; bveq
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_beq_ft (hf := TF_10011b8) (he := rfl) (hd := TD_10011b8)
      getr_resolve; regupd_resolve; rw [P10]
      apply c_eq_neq
      rw [u_targcN inp Hva]
      change (inp.in_argv.length : Int) ≠ 1
      omega
    norm_pc
    exact msteps.mst_refl _
  have H9_4 : reg_get RA 9 = targcN inp := by dsimp only [RA]; regupd_resolve; rfl
  have H18_4 : reg_get RA 18 = nat_to_word (pbJ inp 1) := by
    rw [pbJ_1]; dsimp only [RA]; regupd_resolve; rfl
  have H19_4 : reg_get RA 19 = Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (1 : Int)) := by
    dsimp only [RA]; regupd_resolve; congr 1 <;> omega
  have H20_4 : reg_get RA 20 = nat_to_word 1 := by dsimp only [RA]; regupd_resolve; rfl
  obtain ⟨regsL, HagL, H18L, HmsL⟩ := target_length inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2
    inp.in_argv.length 1 RA (by omega) (by omega) (by omega) H9_4 H18_4 H19_4 H20_4
  refine ⟨regsL, ?_, ?_, ?_, H18L, ?_⟩
  · rw [HagL 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [RA]; regupd_resolve; exact P2
  · rw [HagL 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [RA]; regupd_resolve; exact P8
  · rw [HagL 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact H9_4
  exact msteps_trans _ _ _ _ HmsP (msteps_trans _ _ _ _ Hms HmsL)

/-- The cap check and jump onto the shared return tail: tot > 65536
produces no output and exits with code 3. -/
theorem target_wexit_cap (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (Hcap : 65536 < bv_unsigned (ttot inp)) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 3) := by
  have Htg1 := ttotn_ge1 inp Hge2
  have Htb := ttotn_bound inp Hva
  rw [u_ttot inp Hva] at Hcap
  obtain ⟨regsA, A2, _A8, _A9, A18, HmsA⟩ :=
    target_after_length inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2
  apply msteps_to_wexit _ _ _ _ _ HmsA
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_srli_at (v := v_srli (nat_to_word (ttotn inp - 1)) 16)
      (hf := TF_10011e4) (he := rfl) (hd := TD_10011e4) (hrd := rfl)
    getr_resolve; rw [A18]; rfl
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_beq_ft (hf := TF_10011e8) (he := rfl) (hd := TD_10011e8)
    getr_resolve; regupd_resolve; apply c_eq_0_false
    rw [v_srli_div _ _ (by omega), u_ntw _ (by omega)]
    change ((ttotn inp - 1 : Nat) : Int) / 65536 ≠ 0
    omega
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 3)
      (hf := TF_10011ec) (he := rfl) (hd := TD_10011ec) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_jal_x0 _ _ _ _ _ _ _ TF_10011f0 rfl TD_10011f0
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 3)
      (hf := TF_10012ac) (he := rfl) (hd := TD_10012ac) (hrd := rfl)
    getr_resolve; regupd_resolve; apply v_addi_0
  norm_pc
  let R := regupd (regupd (regupd regsA 10 (v_srli (nat_to_word (ttotn inp - 1)) 16))
    11 (Z_to_bv 64 3)) 10 (Z_to_bv 64 3)
  obtain ⟨regsE, HE17, HE10, HmsE⟩ := target_epilogue asp Hsp_lo Hsp_hi R
    (tfmem inp asp arnd) (Z_to_bv 64 3)
    (by dsimp only [R]; regupd_resolve; exact A2) (by dsimp only [R]; regupd_resolve; rfl)
    (tfread_slot_ra inp asp arnd Hsp_lo Hsp_hi)
    (tfread_slot_s0 inp asp arnd Hsp_lo Hsp_hi)
    (tfread_slot_0 inp asp arnd Hsp_lo Hsp_hi)
  apply msteps_to_wexit _ _ _ _ _ HmsE
  exact tw_exit_coden _ _ _ _ _ _ HE17 HE10 (by decide)

/-- For tot ≤ 65536, the shift and branch reach the mmap argument setup.
The accumulator is incremented to tot, and the run stops at the ecall,
which is the tmw branch point. -/
theorem target_to_mmap (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (Hcap : bv_unsigned (ttot inp) ≤ 65536) :
    ∃ regsE,
      reg_get regsE 2 = Z_to_bv 64 (bv_unsigned asp - 64) ∧
      reg_get regsE 8 = Z_to_bv 64 (bv_unsigned asp + 8) ∧ reg_get regsE 9 = targcN inp ∧
      reg_get regsE 11 = ttot inp ∧ reg_get regsE 12 = Z_to_bv 64 3 ∧
      reg_get regsE 13 = Z_to_bv 64 34 ∧ reg_get regsE 14 = Z_to_bv 64 (2 ^ 64 - 1) ∧
      reg_get regsE 15 = Z_to_bv 64 0 ∧ bv_unsigned (getr regsE 17) = 222 ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        { ms_regs := regsE, ms_fregs := bvmap_empty, ms_pc_val := 0x100120c,
          ms_svc_pending := some (getr regsE 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := tfmem inp asp arnd, ms_rom := arom } := by
  have Htg1 := ttotn_ge1 inp Hge2
  have Htb := ttotn_bound inp Hva
  rw [u_ttot inp Hva] at Hcap
  obtain ⟨regsA, A2, A8, A9, A18, HmsA⟩ :=
    target_after_length inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2
  let RA := regupd (regupd (regupd (regupd (regupd (regupd (regupd regsA
    10 (v_srli (nat_to_word (ttotn inp - 1)) 16)) 11 (ttot inp)) 17 (Z_to_bv 64 222))
    12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)
  refine ⟨RA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [RA]; regupd_resolve; exact A2
  · dsimp only [RA]; regupd_resolve; exact A8
  · dsimp only [RA]; regupd_resolve; exact A9
  · dsimp only [RA]; regupd_resolve; rfl
  · dsimp only [RA]; regupd_resolve; rfl
  · dsimp only [RA]; regupd_resolve; rfl
  · dsimp only [RA]; regupd_resolve; rfl
  · dsimp only [RA]; regupd_resolve; rfl
  · dsimp only [RA]; getr_resolve; regupd_resolve; rfl
  apply msteps_trans _ _ _ _ HmsA
  apply msteps.mst_step _ _ _ rfl
  · apply step_srli_at (v := v_srli (nat_to_word (ttotn inp - 1)) 16)
      (hf := TF_10011e4) (he := rfl) (hd := TD_10011e4) (hrd := rfl)
    getr_resolve; rw [A18]; rfl
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_beq_tk (hf := TF_10011e8) (he := rfl) (hd := TD_10011e8)
    getr_resolve; regupd_resolve; apply c_eq_0_of_u
    rw [v_srli_div _ _ (by omega), u_ntw _ (by omega)]
    change ((ttotn inp - 1 : Nat) : Int) / 65536 = 0
    omega
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := ttot inp)
      (hf := TF_10011f4) (he := rfl) (hd := TD_10011f4) (hrd := rfl)
    getr_resolve; regupd_resolve; rw [A18]; imm_norm
    rw [v_addi_Sj _ (by omega)]
    unfold ttot
    congr 1 <;> omega
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 222)
      (hf := TF_10011f8) (he := rfl) (hd := TD_10011f8) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 3)
      (hf := TF_10011fc) (he := rfl) (hd := TD_10011fc) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 34)
      (hf := TF_1001200) (he := rfl) (hd := TD_1001200) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (2 ^ 64 - 1))
      (hf := TF_1001204) (he := rfl) (hd := TD_1001204) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 0)
      (hf := TF_1001208) (he := rfl) (hd := TD_1001208) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_100120c rfl
  exact msteps.mst_refl _

-- Failure continuation: exit 4.

theorem target_fail_twm (inp : ProcInput) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (model : Model) (regs : bvmap 5 word) (e : Int) (He1 : 1 ≤ e) (He2 : e ≤ 4095)
    (Hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64)) :
    twm target_segs (mkst (regupd regs 10 (errno_ret e)) 0x1001210 (tfmem inp asp arnd) arom)
      model [] (Z_to_bv 64 4) := by
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_blt_tk (Hf := TF_1001210) (He := rfl) (Hd := TD_1001210)
    getr_resolve; regupd_resolve; exact c_lts_errno e He1 He2
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 4)
      (hf := TF_10012a0) (he := rfl) (hd := TD_10012a0) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · exact step_jal_x0 _ _ _ _ _ _ _ TF_10012a4 rfl TD_10012a4
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 4)
      (hf := TF_10012ac) (he := rfl) (hd := TD_10012ac) (hrd := rfl)
    getr_resolve; regupd_resolve; apply v_addi_0
  norm_pc
  let R := regupd (regupd (regupd regs 10 (errno_ret e)) 11 (Z_to_bv 64 4)) 10 (Z_to_bv 64 4)
  obtain ⟨regsE, HE17, HE10, HmsE⟩ := target_epilogue asp Hsp_lo Hsp_hi R
    (tfmem inp asp arnd) (Z_to_bv 64 4)
    (by dsimp only [R]; regupd_resolve; exact Hr2) (by dsimp only [R]; regupd_resolve; rfl)
    (tfread_slot_ra inp asp arnd Hsp_lo Hsp_hi)
    (tfread_slot_s0 inp asp arnd Hsp_lo Hsp_hi)
    (tfread_slot_0 inp asp arnd Hsp_lo Hsp_hi)
  apply msteps_twm _ _ _ _ _ _ HmsE
  exact twm_exit_coden _ _ _ _ _ _ _ HE17 HE10 (by decide)

-- Success continuation.

def zmemT (inp : ProcInput) (asp : word) (arnd : EntryDraw) (aG gz : word) :
    word → Option byte := zfill aG gz (tfmem inp asp arnd)

/-- The grant is zero-mapped (`zmemT` = `zfill aG gz _`), so every byte
of [aG, aG+gz) is writable whatever sits underneath — which is what
a machine store into the joined buffer has to show. -/
theorem tgrant_store_ok (asp : word) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (aG gz : word)
    (HaCeil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - stack_max_size)
    (m : word → Option byte) (a : word) (k : Nat)
    (Hx1 : bv_unsigned aG ≤ bv_unsigned a) (Hx2 : bv_unsigned a + (k : Int) ≤ bv_unsigned aG + bv_unsigned gz) :
    store_ok target_segs (zmem m aG gz) a k = true := by
  apply store_ok_zmem _ _ _ _ _ _ _ Hx1 Hx2
  have Hhi := asp_hi_num asp Hsp_hi
  change bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - 8388608 at HaCeil
  omega

-- Inner byte-copy loop: 0x1001248 .. 0x1001260.

set_option maxHeartbeats 1000000 in
theorem target_copy_inner (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (aG gz : word) (HaPos : 0 < bv_unsigned aG)
    (Hgz_lo : bv_unsigned (ttot inp) ≤ bv_unsigned gz)
    (HaCeil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - stack_max_size)
    (p : word) (s pre : List byte) (Hnz : Z_to_bv 8 0 ∉ s)
    (Hpsb : pre.length + s.length + 1 ≤ ttotn inp) (Hp : bv_unsigned asp ≤ bv_unsigned p)
    (Hpbnd : bv_unsigned p + (s.length : Int) + 1 < 2 ^ 64)
    (Hrd : ∀ j, j ≤ s.length →
      rdn target_segs (tfmem inp asp arnd) (p + nat_to_word j) 1 = some [byte_at s j])
    (d j : Nat) (regs : bvmap 5 word) (Hjd : j + d = s.length)
    (H11 : reg_get regs 11 = aG) (H12 : reg_get regs 12 = nat_to_word (pre.length + j))
    (H15 : reg_get regs 15 = p + nat_to_word j) :
    ∃ regs',
      (∀ r : reg, r ≠ 12 → r ≠ 15 → r ≠ 16 → r ≠ 17 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 12 = nat_to_word (pre.length + s.length) ∧
      msteps target_segs
        (mkst regs 0x1001248 (wbytes (zmemT inp asp arnd aG gz) aG (pre ++ s.take j)) arom)
        (mkst regs' 0x1001264 (wbytes (zmemT inp asp arnd aG gz) aG (pre ++ s)) arom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have Htg1 := ttotn_ge1 inp Hge2
  have Htb := ttotn_bound inp Hva
  have HuaG := u64_range aG
  have Hugz := u64_range gz
  have Hgzn : (ttotn inp : Int) ≤ bv_unsigned gz := by rw [← u_ttot inp Hva]; exact Hgz_lo
  have Hceil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - 8388608 := HaCeil
  have Hread : ∀ j, j ≤ s.length →
      rdn target_segs (wbytes (zmemT inp asp arnd aG gz) aG (pre ++ s.take j))
        (p + nat_to_word j) 1 = some [byte_at s j] := by
    intro j Hj
    have Hptr : bv_unsigned (p + nat_to_word j) = bv_unsigned p + (j : Int) := by
      rw [word_add_nat, u_Z2bv _ (by have := u64_range p; omega) (by omega)]
    rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [List.length_append, List.length_take, Nat.min_eq_left Hj, Hptr]; omega)
      (by rw [Hptr]; omega)]
    unfold zmemT
    rw [rdn_zfill_out _ _ _ _ _ _ (by rw [Hptr]; omega) (Or.inr (by rw [Hptr]; omega))]
    exact Hrd j Hj
  induction d generalizing j regs with
  | zero =>
    have Hj : j = s.length := by omega
    let regs1 := regupd regs 16 (Z_to_bv 64 0)
    refine ⟨regs1, ?_, ?_, ?_⟩
    · intro r _ _ H16 _
      exact regupd_other _ _ _ _ H16
    · dsimp only [regs1]; regupd_resolve; rw [H12, Hj]
    apply msteps.mst_step _ _ _ rfl
    · apply step_lbu (b := Z_to_bv 8 0)
        (hfetch := TF_1001248) (hecall := rfl) (hdecode := TD_1001248)
      getr_resolve; rw [H15]; imm_norm; rw [v_addi_0]
      have H := Hread j (by omega)
      rw [Hj, byte_at_len] at H
      rw [Hj]; exact H
    step_simpl
    apply msteps.mst_step _ _ _ rfl
    · apply step_beq_tk (hf := TF_100124c) (he := rfl) (hd := TD_100124c)
      getr_resolve; regupd_resolve; exact c_eq_0_true
    norm_pc
    rw [Hj, List.take_length]
    exact msteps.mst_refl _
  | succ d IH =>
    have Hjlt : j < s.length := by omega
    let b := byte_at s j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz s j Hnz Hjlt
    let regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned b))
    let regs2 := regupd regs1 17 (aG + nat_to_word (pre.length + j))
    let regs3 := regupd regs2 12 (nat_to_word (pre.length + (j + 1)))
    let regs4 := regupd regs3 15 (p + nat_to_word (j + 1))
    obtain ⟨regs', Hag', H12f, Hms'⟩ := IH (j + 1) regs4 (by omega)
      (by dsimp only [regs4, regs3, regs2, regs1]; regupd_resolve; exact H11)
      (by dsimp only [regs4, regs3]; regupd_resolve; rfl)
      (by dsimp only [regs4]; regupd_resolve; rfl)
    refine ⟨regs', ?_, H12f, ?_⟩
    · intro r h12 h15 h16 h17
      rw [Hag' r h12 h15 h16 h17]
      dsimp only [regs4, regs3, regs2, regs1]
      rw [regupd_other _ _ _ _ h15, regupd_other _ _ _ _ h12,
        regupd_other _ _ _ _ h17, regupd_other _ _ _ _ h16]
    apply msteps.mst_step _ _ _ rfl
    · apply step_lbu (b := b) (hfetch := TF_1001248) (hecall := rfl) (hdecode := TD_1001248)
      getr_resolve; rw [H15]; imm_norm; rw [v_addi_0]
      exact Hread j (by omega)
    step_simpl
    apply msteps.mst_step _ _ _ rfl
    · apply step_beq_ft (hf := TF_100124c) (he := rfl) (hd := TD_100124c)
      getr_resolve; regupd_resolve; apply c_eq_0_false
      rw [u_zext8]; exact byte_nz_u b Hbnz
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_add_at (v := aG + nat_to_word (pre.length + j))
        (hf := TF_1001250) (he := rfl) (hd := TD_1001250) (hrd := rfl)
      getr_resolve; regupd_resolve; rw [H11, H12, v_add_word]
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := nat_to_word (pre.length + (j + 1)))
        (hf := TF_1001254) (he := rfl) (hd := TD_1001254) (hrd := rfl)
      getr_resolve; regupd_resolve; rw [H12]; imm_norm
      rw [v_addi_Sj _ (by omega)]
      congr 1 <;> omega
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_sb_atv (a := aG + nat_to_word (pre ++ s.take j).length) (b := b)
        (Hf := TF_1001258) (He := rfl) (Hd := TD_1001258)
      · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
        rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
      · getr_resolve; regupd_resolve; rfl
      · store_ok_peel
        apply tgrant_store_ok asp Hsp_hi aG gz HaCeil
        all_goals rw [word_add_nat, List.length_append, List.length_take, Nat.min_eq_left (by omega),
          u_Z2bv _ (by omega) (by omega)]
        all_goals omega
    norm_pc
    have Hsnoc : pre ++ s.take (j + 1) = (pre ++ s.take j) ++ [b] := by
      rw [firstn_S_nth _ s j (Z_to_bv 8 0) Hjlt, List.append_assoc, ← nth_lt_byte_at s j Hjlt]
    rw [← wbytes_snoc, ← Hsnoc]
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := p + nat_to_word (j + 1))
        (hf := TF_100125c) (he := rfl) (hd := TD_100125c) (hrd := rfl)
      getr_resolve; regupd_resolve; rw [H15]; exact v_addi_ntw_S p j
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · exact step_jal_x0 _ _ _ _ _ _ _ TF_1001260 rfl TD_1001260
    norm_pc
    exact Hms'

set_option maxHeartbeats 2000000 in
/-- Outer copy loop: 0x1001228, exiting at 0x100126c. -/
theorem target_copy_outer (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (aG gz : word) (HaPos : 0 < bv_unsigned aG)
    (Hgz_lo : bv_unsigned (ttot inp) ≤ bv_unsigned gz)
    (HaCeil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - stack_max_size)
    (f i : Nat) (regs : bvmap 5 word)
    (H1 : 1 ≤ i) (Hi : i < inp.in_argv.length) (Hf : inp.in_argv.length - i ≤ f)
    (H8 : reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8))
    (H9 : reg_get regs 9 = targcN inp) (H10 : reg_get regs 10 = Z_to_bv 64 1)
    (H11 : reg_get regs 11 = aG) (H12 : reg_get regs 12 = nat_to_word (pbJ inp i))
    (H13 : reg_get regs 13 = Z_to_bv 64 32) (H14 : reg_get regs 14 = nat_to_word i) :
    ∃ regs',
      (∀ r : reg, r ≠ 12 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 12 = nat_to_word (ttotn inp - 1) ∧
      reg_get regs' 15 = aG + nat_to_word (ttotn inp - 1) ∧
      msteps target_segs
        (mkst regs 0x1001228
          (wbytes (zmemT inp asp arnd aG gz) aG (join1 (inp.in_argv.tail.take (i - 1)))) arom)
        (mkst regs' 0x100126c
          (wbytes (zmemT inp asp arnd aG gz) aG (join1 inp.in_argv.tail)) arom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have Htg1 := ttotn_ge1 inp Hge2
  have Htb := ttotn_bound inp Hva
  have HuaG := u64_range aG
  have Hugz := u64_range gz
  have Hgzn : (ttotn inp : Int) ≤ bv_unsigned gz := by rw [← u_ttot inp Hva]; exact Hgz_lo
  have Hceil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - 8388608 := HaCeil
  induction f generalizing i regs with
  | zero => omega
  | succ f IH =>
    have HiZ := tiN_le inp Hva i (by omega)
    have HSiZ := tiN_le inp Hva (i + 1) (by omega)
    have HpbLe := pbJ_le inp Hge2 i
    have HpbLeS := pbJ_le inp Hge2 (i + 1)
    obtain ⟨Hptrlo, Hptrhi⟩ := tsptr_bounds inp Hva Hve asp Hsp_hi i Hi
    let M0 := wbytes (zmemT inp asp arnd aG gz) aG (join1 (inp.in_argv.tail.take (i - 1)))
    let regs1 := regupd regs 15 (aG + nat_to_word (pbJ inp i))
    let sep : Nat := if i == 1 then 0 else 1
    let preI := if i == 1 then join1 (inp.in_argv.tail.take (i - 1))
      else join1 (inp.in_argv.tail.take (i - 1)) ++ [Z_to_bv 8 32]
    have HlenPre : preI.length = pbJ inp i + sep := by
      dsimp only [preI, sep, pbJ]
      split <;> (try simp only [List.length_append, List.length_singleton]) <;> omega
    have Hsep1 : sep ≤ 1 := by dsimp only [sep]; split <;> omega
    have HB : ∃ regsB,
        (∀ r : reg, r ≠ 12 → reg_get regsB r = reg_get regs1 r) ∧
        reg_get regsB 12 = nat_to_word (pbJ inp i + sep) ∧
        msteps target_segs (mkst regs1 0x1001230 M0 arom)
          (mkst regsB 0x100123c (wbytes (zmemT inp asp arnd aG gz) aG preI) arom) := by
      by_cases Hi1 : i = 1
      · have Es : sep = 0 := by simp only [sep, Hi1, beq_self_eq_true, ↓reduceIte]
        have Ep : preI = join1 (inp.in_argv.tail.take (i - 1)) := by
          simp only [preI, Hi1, beq_self_eq_true, ↓reduceIte]
        refine ⟨regs1, fun _ _ => rfl, ?_, ?_⟩
        · dsimp only [regs1]; regupd_resolve; rw [H12, Es, Nat.add_zero]
        apply msteps.mst_step _ _ _ rfl
        · apply step_bgeu_tk (Hf := TF_1001230) (He := rfl) (Hd := TD_1001230)
          dsimp only [regs1]; getr_resolve; regupd_resolve; rw [H10, H14, Hi1, c_ltu_ltb]
          decide
        norm_pc
        rw [Ep]
        exact msteps.mst_refl _
      · have Es : sep = 1 := by simp only [sep, beq_iff_eq, Hi1, ↓reduceIte]
        have Ep : preI = join1 (inp.in_argv.tail.take (i - 1)) ++ [Z_to_bv 8 32] := by
          simp only [preI, beq_iff_eq, Hi1, ↓reduceIte]
        let regs2 := regupd regs1 12 (nat_to_word (pbJ inp i + 1))
        refine ⟨regs2, ?_, ?_, ?_⟩
        · intro r hr; exact regupd_other _ _ _ _ hr
        · dsimp only [regs2]; regupd_resolve; rw [Es]
        apply msteps.mst_step _ _ _ rfl
        · apply step_bgeu_ft (Hf := TF_1001230) (He := rfl) (Hd := TD_1001230)
          dsimp only [regs1]; getr_resolve; regupd_resolve; rw [H10, H14, c_ltu_ltb, u_ntw _ (by omega)]
          apply decide_eq_true
          change (1 : Int) < (i : Int)
          omega
        norm_pc
        apply msteps.mst_step _ _ _ rfl
        · apply step_addi_at (v := nat_to_word (pbJ inp i + 1))
            (hf := TF_1001234) (he := rfl) (hd := TD_1001234) (hrd := rfl)
          dsimp only [regs1]; getr_resolve; regupd_resolve; rw [H12]; imm_norm
          exact v_addi_Sj _ (by omega)
        norm_pc
        apply msteps.mst_step _ _ _ rfl
        · apply step_sb_atv (a := aG + nat_to_word (pbJ inp i)) (b := Z_to_bv 8 32)
            (Hf := TF_1001238) (He := rfl) (Hd := TD_1001238)
          · dsimp only [regs1]; getr_resolve; regupd_resolve; apply v_addi_0
          · dsimp only [regs1]; getr_resolve; regupd_resolve; rw [H13]; rfl
          · dsimp only [M0]; store_ok_peel
            apply tgrant_store_ok asp Hsp_hi aG gz HaCeil
            all_goals rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]; omega
        norm_pc
        rw [Ep, wbytes_snoc]
        exact msteps.mst_refl _
    obtain ⟨regsB, HagB, H12B, HmsB⟩ := HB
    have H8B : reg_get regsB 8 = Z_to_bv 64 (bv_unsigned asp + 8) := by
      rw [HagB 8 (by decide)]; dsimp only [regs1]; regupd_resolve; exact H8
    have H11B : reg_get regsB 11 = aG := by
      rw [HagB 11 (by decide)]; dsimp only [regs1]; regupd_resolve; exact H11
    have H14B : reg_get regsB 14 = nat_to_word i := by
      rw [HagB 14 (by decide)]; dsimp only [regs1]; regupd_resolve; exact H14
    let regsC := regupd regsB 15 (Z_to_bv 64 (8 * (i : Int)))
    let regsD := regupd regsC 15 (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (i : Int)))
    let regsE := regupd regsD 15 (tsptr inp asp i)
    have Hpsb : preI.length + (inp.in_argv.getD i []).length + 1 ≤ ttotn inp := by
      rw [HlenPre]
      rw [pbJ_stepN inp i H1 Hi] at HpbLeS
      change pbJ inp i + (inp.in_argv.getD i []).length + sep ≤ ttotn inp - 1 at HpbLeS
      omega
    obtain ⟨regsI, HagI, H12I, HmsI⟩ := target_copy_inner inp Hva asp arnd Hsp_lo Hsp_hi
      Hge2 aG gz HaPos Hgz_lo HaCeil (tsptr inp asp i) (inp.in_argv.getD i []) preI
      (targ_nz_k inp Hva i Hi) Hpsb Hptrlo Hptrhi
      (fun j Hj => tread_arg_byte inp Hva Hve asp arnd Hsp_lo Hsp_hi i j Hi Hj)
      (inp.in_argv.getD i []).length 0 regsE (by omega)
      (by dsimp only [regsE, regsD, regsC]; regupd_resolve; exact H11B)
      (by dsimp only [regsE, regsD, regsC]; regupd_resolve; rw [H12B, HlenPre, Nat.add_zero])
      (by dsimp only [regsE]; regupd_resolve; rw [word_add_0])
    simp only [List.take_zero, List.append_nil] at HmsI
    have HpreApp : preI ++ inp.in_argv.getD i [] = join1 (inp.in_argv.tail.take i) := by
      dsimp only [preI]
      by_cases Ei : i = 1
      · subst i
        simp only [beq_self_eq_true, ↓reduceIte, Nat.sub_self, List.take_zero, join1,
          List.nil_append, tjoin_1 inp Hge2]
      · simp only [beq_iff_eq, Ei, ↓reduceIte]
        rw [tjoin_step inp Hge2 i (by omega) Hi, List.append_assoc]
        rfl
    have H12I' : reg_get regsI 12 = nat_to_word (pbJ inp (i + 1)) := by
      rw [H12I, HlenPre, pbJ_stepN inp i H1 Hi]
      congr 1
      change pbJ inp i + sep + _ = pbJ inp i + _ + sep
      omega
    let regsF := regupd regsI 14 (nat_to_word (i + 1))
    have HagF : ∀ r : reg, r ≠ 12 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        reg_get regsF r = reg_get regs r := by
      intro r h12 h14 h15 h16 h17
      dsimp only [regsF]
      rw [regupd_other _ _ _ _ h14, HagI r h12 h15 h16 h17]
      dsimp only [regsE, regsD, regsC]
      rw [regupd_other _ _ _ _ h15, regupd_other _ _ _ _ h15,
        regupd_other _ _ _ _ h15, HagB r h12]
      exact regupd_other _ _ _ _ h15
    have H8F := (HagF 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans H8
    have H9F := (HagF 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans H9
    have H10F := (HagF 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans H10
    have H11F := (HagF 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans H11
    have H13F := (HagF 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans H13
    have H12F : reg_get regsF 12 = nat_to_word (pbJ inp (i + 1)) := by
      dsimp only [regsF]; regupd_resolve; exact H12I'
    have H14F : reg_get regsF 14 = nat_to_word (i + 1) := by
      dsimp only [regsF]; regupd_resolve; rfl
    have HmsF : msteps target_segs (mkst regs 0x1001228 M0 arom)
        (mkst regsF 0x1001228
          (wbytes (zmemT inp asp arnd aG gz) aG (preI ++ inp.in_argv.getD i [])) arom) := by
      apply msteps.mst_step _ _ _ rfl
      · apply step_add_at (v := aG + nat_to_word (pbJ inp i))
          (hf := TF_1001228) (he := rfl) (hd := TD_1001228) (hrd := rfl)
        getr_resolve; rw [H11, H12, v_add_word]
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_beq_ft (hf := TF_100122c) (he := rfl) (hd := TD_100122c)
        getr_resolve; regupd_resolve; rw [H14, H9]
        apply c_eq_neq
        rw [u_ntw _ (by omega), u_targcN inp Hva]
        omega
      norm_pc
      apply msteps_trans _ _ _ _ HmsB
      apply msteps.mst_step _ _ _ rfl
      · apply step_slli_at (v := Z_to_bv 64 (8 * (i : Int)))
          (hf := TF_100123c) (he := rfl) (hd := TD_100123c) (hrd := rfl)
        getr_resolve; rw [H14B]; imm_norm
        exact v_slli3_nat i (by omega)
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_add_at (v := Z_to_bv 64 (bv_unsigned asp + 8 + 8 * (i : Int)))
          (hf := TF_1001240) (he := rfl) (hd := TD_1001240) (hrd := rfl)
        getr_resolve; regupd_resolve; rw [H8B]
        unfold v_add
        rw [u_Z2bv _ (by omega) (by omega), u_Z2bv _ (by omega) (by omega)]
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_ld (bs := word_le8 (tsptr inp asp i)) (v := tsptr inp asp i)
          (hfetch := TF_1001244) (hecall := rfl) (hdecode := TD_1001244)
        · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
          rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [HlenPre]; u_norm; omega) (by u_norm; omega)]
          unfold zmemT
          rw [rdn_zfill_out _ _ _ _ _ _ (by u_norm; omega) (Or.inr (by u_norm; omega))]
          exact tread_arg_ptr inp Hva Hve asp arnd Hsp_lo Hsp_hi i Hi
        · exact bytes_le_n_to_le_8 _
      step_simpl
      apply msteps_trans _ _ _ _ HmsI
      apply msteps.mst_step _ _ _ rfl
      · apply step_addi_at (v := nat_to_word (i + 1))
          (hf := TF_1001264) (he := rfl) (hd := TD_1001264) (hrd := rfl)
        getr_resolve
        rw [HagI 14 (by decide) (by decide) (by decide) (by decide)]
        dsimp only [regsE, regsD, regsC]; regupd_resolve; rw [H14B]; imm_norm
        exact v_addi_Sj _ (by omega)
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · exact step_jal_x0 _ _ _ _ _ _ _ TF_1001268 rfl TD_1001268
      norm_pc
      exact msteps.mst_refl _
    by_cases Hlti : i + 1 < inp.in_argv.length
    · obtain ⟨regs', Hag', H12', H15', Hms'⟩ := IH (i + 1) regsF (by omega) Hlti (by omega)
        H8F H9F H10F H11F H12F H13F H14F
      refine ⟨regs', ?_, H12', H15', ?_⟩
      · intro r h12 h14 h15 h16 h17
        exact (Hag' r h12 h14 h15 h16 h17).trans (HagF r h12 h14 h15 h16 h17)
      apply msteps_trans _ _ _ _ HmsF
      rw [HpreApp]
      exact Hms'
    · have HSieq : i + 1 = inp.in_argv.length := by omega
      have HpreAll : preI ++ inp.in_argv.getD i [] = join1 inp.in_argv.tail := by
        rw [HpreApp, List.take_of_length_le (by rw [tlength_tl_av]; omega)]
      have HpbSi : pbJ inp (i + 1) = ttotn inp - 1 := by rw [HSieq, pbJ_last inp Hge2]
      let regsH := regupd regsF 15 (aG + nat_to_word (ttotn inp - 1))
      refine ⟨regsH, ?_, ?_, ?_, ?_⟩
      · intro r h12 h14 h15 h16 h17
        dsimp only [regsH]
        rw [regupd_other _ _ _ _ h15]
        exact HagF r h12 h14 h15 h16 h17
      · dsimp only [regsH]; rw [regupd_other _ _ _ _ (by decide), H12F, HpbSi]
      · dsimp only [regsH]; regupd_resolve; rfl
      apply msteps_trans _ _ _ _ HmsF
      apply msteps.mst_step _ _ _ rfl
      · apply step_add_at (v := aG + nat_to_word (ttotn inp - 1))
          (hf := TF_1001228) (he := rfl) (hd := TD_1001228) (hrd := rfl)
        getr_resolve
        have H11I := H11F
        dsimp only [regsF] at H11I
        rw [regupd_other _ _ _ _ (by decide)] at H11I
        rw [H11I, H12I', HpbSi, v_add_word]
      norm_pc
      apply msteps.mst_step _ _ _ rfl
      · apply step_beq_tk (hf := TF_100122c) (he := rfl) (hd := TD_100122c)
        getr_resolve
        have H9I := H9F
        dsimp only [regsF] at H9I
        rw [regupd_other _ _ _ _ (by decide)] at H9I
        rw [H9I, HSieq]
        exact c_eq_refl _
      norm_pc
      rw [HpreAll]
      exact msteps.mst_refl _

/-- The tail after the put loop: exit code 0. Entered at 0x1001298
with the frame still in place. -/
theorem target_out_tail (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (aG gz : word)
    (Hgz_lo : bv_unsigned (ttot inp) ≤ bv_unsigned gz)
    (HaCeil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - stack_max_size)
    (model : Model) (regs : bvmap 5 word)
    (H2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64)) :
    twm target_segs (mkst regs 0x1001298 (wbytes (zmemT inp asp arnd aG gz) aG (jout inp.in_argv)) arom)
      model [] (Z_to_bv 64 0) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have Htb := ttotn_bound inp Hva
  have HuaG := u64_range aG
  have Hugz := u64_range gz
  have Hgzn : (ttotn inp : Int) ≤ bv_unsigned gz := by rw [← u_ttot inp Hva]; exact Hgz_lo
  have Hceil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - 8388608 := HaCeil
  let memJ := wbytes (zmemT inp asp arnd aG gz) aG (jout inp.in_argv)
  have Hframe : ∀ a : word, bv_unsigned asp - 64 ≤ bv_unsigned a →
      bv_unsigned a ≤ bv_unsigned asp - 24 →
      rdn target_segs memJ a 8 = rdn target_segs (tfmem inp asp arnd) a 8 := by
    intro a Ha Hb
    dsimp only [memJ]
    rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [tjout_len_nat inp Hge2]; omega) (by omega)]
    unfold zmemT
    rw [rdn_zfill_out _ _ _ _ _ _ (by omega) (Or.inr (by omega))]
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 0)
      (hf := TF_1001298) (he := rfl) (hd := TD_1001298) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · exact step_jal_x0 _ _ _ _ _ _ _ TF_100129c rfl TD_100129c
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 0)
      (hf := TF_10012ac) (he := rfl) (hd := TD_10012ac) (hrd := rfl)
    getr_resolve; regupd_resolve; apply v_addi_0
  norm_pc
  obtain ⟨regsE, HE17, HE10, HmsE⟩ := target_epilogue asp Hsp_lo Hsp_hi
    (regupd (regupd regs 11 (Z_to_bv 64 0)) 10 (Z_to_bv 64 0)) memJ (Z_to_bv 64 0)
    (by regupd_resolve; exact H2r) (by regupd_resolve; rfl)
    (by rw [Hframe _ (by u_norm; omega) (by u_norm; omega)];
        exact tfread_slot_ra inp asp arnd Hsp_lo Hsp_hi)
    (by rw [Hframe _ (by u_norm; omega) (by u_norm; omega)];
        exact tfread_slot_s0 inp asp arnd Hsp_lo Hsp_hi)
    (by
      intro a Ha
      have Hab : bv_unsigned asp - 64 ≤ bv_unsigned a ∧ bv_unsigned a ≤ bv_unsigned asp - 40 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at Ha
        rcases Ha with rfl | rfl | rfl | rfl <;> u_norm <;> omega
      rw [Hframe a Hab.1 (by omega)]
      exact tfread_slot_0 inp asp arnd Hsp_lo Hsp_hi a Ha)
  apply msteps_twm _ _ _ _ _ _ HmsE
  exact twm_exit_coden _ _ _ _ _ _ _ HE17 HE10 (by decide)

/-- The put-style write-all retry loop at 0x1001288: register-only, so
the memory and every register outside a0/a1/a2 carry through unchanged. -/
theorem tgt_put_wall (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (aG gz : word)
    (Hgz_lo : bv_unsigned (ttot inp) ≤ bv_unsigned gz)
    (HaCeil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - stack_max_size)
    (model : Model) (fuel : Nat) (rest : List byte) (p : word) (k : Nat) (regs : bvmap 5 word)
    (Hfuel : rest.length ≤ fuel) (Hk1 : 1 ≤ k) (Hk2 : k ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 2097152) (Hplo : 0 < bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) < 2 ^ 64)
    (H2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (H10 : reg_get regs 10 = len_word (rest.take k))
    (H11 : reg_get regs 11 = p) (H12 : reg_get regs 12 = len_word rest)
    (H17 : bv_unsigned (reg_get regs 17) = 64)
    (Hread : rdn target_segs (wbytes (zmemT inp asp arnd aG gz) aG (jout inp.in_argv))
      p rest.length = some rest) :
    twm_tail target_segs
      (mkst regs 0x1001288 (wbytes (zmemT inp asp arnd aG gz) aG (jout inp.in_argv)) arom)
      model (rest.drop k) [] (Z_to_bv 64 0) := by
  induction fuel generalizing rest p k regs with
  | zero => omega
  | succ fuel IH =>
    apply twm_tail.twmt_step _ _ _ _ _ _ rfl
    · apply step_bge_ft (hf := TF_1001288) (he := rfl) (hd := TD_1001288)
      getr_resolve; rw [H10]
      apply c_lts_0_pos
      all_goals rw [u_len_word_firstn _ _ Hk2 (by omega)]; omega
    norm_pc
    apply twm_tail.twmt_step _ _ _ _ _ _ rfl
    · apply step_add_at (v := Z_to_bv 64 (bv_unsigned p + (k : Int)))
        (hf := TF_100128c) (he := rfl) (hd := TD_100128c) (hrd := rfl)
      getr_resolve; rw [H11, H10]
      exact v_add_len_firstn_Z p k rest Hk2 (by omega)
    norm_pc
    apply twm_tail.twmt_step _ _ _ _ _ _ rfl
    · apply step_sub_at (v := len_word (rest.drop k))
        (hf := TF_1001290) (he := rfl) (hd := TD_1001290) (hrd := rfl)
      getr_resolve; regupd_resolve; rw [H12, H10]
      exact v_sub_len_firstn k rest Hk2 (by omega)
    norm_pc
    by_cases Heq : k = rest.length
    · subst k
      rw [List.drop_length]
      apply twm_tail.twmt_step _ _ _ _ _ _ rfl
      · apply step_bne_ft (hf := TF_1001294) (he := rfl) (hd := TD_1001294)
        getr_resolve; regupd_resolve; exact c_eq_0_true
      norm_pc
      apply twm_tail.twmt_done
      apply target_out_tail inp Hva asp arnd Hsp_lo Hsp_hi Hge2 aG gz Hgz_lo HaCeil
      regupd_resolve; exact H2r
    · have Hsk : rdn target_segs (wbytes (zmemT inp asp arnd aG gz) aG (jout inp.in_argv))
          (Z_to_bv 64 (bv_unsigned p + (k : Int))) (rest.drop k).length = some (rest.drop k) := by
        rw [List.length_drop]
        have H := rdn_skipn target_segs _ rest.length p rest k Hread Hk2
        rw [word_add_nat_Z p k (by omega)] at H
        exact H
      apply twm_tail.twmt_step _ _ _ _ _ _ rfl
      · apply step_bne_tk (hf := TF_1001294) (he := rfl) (hd := TD_1001294)
        getr_resolve; regupd_resolve
        apply c_eq_0_false
        rw [u_len_word _ (by rw [List.length_drop]; omega), List.length_drop]
        omega
      norm_pc
      apply twm_tail.twmt_step _ _ _ _ _ _ rfl
      · apply step_addi_at (v := Z_to_bv 64 1)
          (hf := TF_1001280) (he := rfl) (hd := TD_1001280) (hrd := rfl)
        getr_resolve; bveq
      norm_pc
      apply twm_tail.twmt_step _ _ _ _ _ _ rfl
      · exact step_ecall _ _ _ _ _ _ TF_1001284 rfl
      apply twm_tail_write_rec
      · getr_resolve; regupd_resolve; exact H17
      · regupd_resolve; rfl
      · regupd_resolve
        rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs _ _ (word_to_nat (len_word (rest.drop k))) = _
        have Hn : word_to_nat (len_word (rest.drop k)) = (rest.drop k).length := by
          change word_to_nat (nat_to_word (rest.drop k).length) = _
          apply word_to_nat_ntw
          rw [List.length_drop]; omega
        rw [Hn]
        exact Hsk
      · rw [List.length_drop]; omega
      · intro m Hm1 Hm2
        norm_pc
        apply IH (rest.drop k) (Z_to_bv 64 (bv_unsigned p + (k : Int))) m
        · rw [List.length_drop]; omega
        · exact Hm1
        · exact Hm2
        · rw [List.length_drop]; omega
        · rw [u_Z2bv _ (by omega) (by omega)]; omega
        · rw [u_Z2bv _ (by omega) (by omega), List.length_drop]; omega
        · regupd_resolve; exact H2r
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; exact H17
        · exact Hsk

theorem target_out (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (aG gz : word) (HaPos : 0 < bv_unsigned aG)
    (Hgz_lo : bv_unsigned (ttot inp) ≤ bv_unsigned gz)
    (HaCeil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - stack_max_size)
    (model : Model) (regs : bvmap 5 word)
    (H2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (H11 : reg_get regs 11 = aG) (H12 : reg_get regs 12 = nat_to_word (ttotn inp - 1))
    (H15 : reg_get regs 15 = aG + nat_to_word (ttotn inp - 1)) :
    twm target_segs
      (mkst regs 0x100126c (wbytes (zmemT inp asp arnd aG gz) aG (join1 inp.in_argv.tail)) arom)
      model [jout inp.in_argv] (Z_to_bv 64 0) := by
  have Hhi := asp_hi_num asp Hsp_hi
  have Htg1 := ttotn_ge1 inp Hge2
  have Htb := ttotn_bound inp Hva
  have HuaG := u64_range aG
  have Hugz := u64_range gz
  have Hgzn : (ttotn inp : Int) ≤ bv_unsigned gz := by rw [← u_ttot inp Hva]; exact Hgz_lo
  have Hceil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - 8388608 := HaCeil
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 10)
      (hf := TF_100126c) (he := rfl) (hd := TD_100126c) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_sb_atv (a := aG + nat_to_word (join1 inp.in_argv.tail).length) (b := Z_to_bv 8 10)
      (Hf := TF_1001270) (He := rfl) (Hd := TD_1001270)
    · getr_resolve; regupd_resolve; rw [H15]; imm_norm
      rw [v_addi_0, tjoin1_tl_len_nat inp Hge2]
    · getr_resolve; regupd_resolve; rfl
    · store_ok_peel
      apply tgrant_store_ok asp Hsp_hi aG gz HaCeil
      all_goals rw [word_add_nat, tjoin1_tl_len_nat inp Hge2,
        u_Z2bv _ (by omega) (by omega)]; omega
  norm_pc
  rw [← wbytes_snoc]
  change twm target_segs
    (mkst (regupd regs 10 (Z_to_bv 64 10)) 0x1001274
      (wbytes (zmemT inp asp arnd aG gz) aG (jout inp.in_argv)) arom) _ _ _
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := ttot inp)
      (hf := TF_1001274) (he := rfl) (hd := TD_1001274) (hrd := rfl)
    getr_resolve; regupd_resolve; rw [H12]; imm_norm
    rw [v_addi_Sj _ (by omega)]
    unfold ttot
    congr 1 <;> omega
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 64)
      (hf := TF_1001278) (he := rfl) (hd := TD_1001278) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_beq_ft (hf := TF_100127c) (he := rfl) (hd := TD_100127c)
    getr_resolve; regupd_resolve
    apply c_eq_0_false
    rw [u_ttot inp Hva]; omega
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 1)
      (hf := TF_1001280) (he := rfl) (hd := TD_1001280) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply twm.twm_step _ _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_1001284 rfl
  apply twm_write_ret
  · getr_resolve; regupd_resolve; rfl
  · regupd_resolve; rfl
  · regupd_resolve; rw [H11]
    rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
    change rdn target_segs _ _ (word_to_nat (ttot inp)) = _
    rw [tjout_len_w inp Hva Hge2]
    apply rdn_wbytes_hit
    rw [tjout_len_nat inp Hge2]; omega
  · rw [tjout_len_nat inp Hge2]; omega
  · intro k Hk1 Hk2
    norm_pc
    apply tgt_put_wall inp Hva asp arnd Hsp_lo Hsp_hi Hge2 aG gz Hgz_lo HaCeil
      model (jout inp.in_argv).length (jout inp.in_argv) aG k
    · omega
    · exact Hk1
    · exact Hk2
    · rw [tjout_len_nat inp Hge2]; omega
    · exact HaPos
    · rw [tjout_len_nat inp Hge2]; omega
    · regupd_resolve; exact H2r
    · regupd_resolve; rfl
    · regupd_resolve; exact H11
    · regupd_resolve
      unfold ttot nat_to_word len_word
      rw [tjout_len_nat inp Hge2]
    · regupd_resolve; rfl
    · apply rdn_wbytes_hit
      rw [tjout_len_nat inp Hge2]; omega

-- The whole success continuation from the mmap return.

theorem target_succ_twm (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (Hge2 : 2 ≤ inp.in_argv.length) (aG gz : word) (HaPos : 0 < bv_unsigned aG)
    (Hgz_lo : bv_unsigned (ttot inp) ≤ bv_unsigned gz)
    (HaCeil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - stack_max_size)
    (model : Model) (regs : bvmap 5 word)
    (H2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64))
    (H8r : reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8))
    (H9r : reg_get regs 9 = targcN inp) :
    twm target_segs (mkst (regupd regs 10 aG) 0x1001210 (zfill aG gz (tfmem inp asp arnd)) arom)
      model [jout inp.in_argv] (Z_to_bv 64 0) := by
  have Hhi := asp_hi_num asp Hsp_hi
  have Hugz := u64_range gz
  have Hceil : bv_unsigned aG + bv_unsigned gz ≤ bv_unsigned asp - 8388608 := HaCeil
  have Hagl : bv_unsigned aG < 2 ^ 63 := by omega
  let RA := regupd (regupd (regupd (regupd (regupd (regupd regs 10 aG) 11 aG)
    12 (Z_to_bv 64 0)) 10 (Z_to_bv 64 1)) 13 (Z_to_bv 64 32)) 14 (nat_to_word 1)
  have HmsA : msteps target_segs
      (mkst (regupd regs 10 aG) 0x1001210 (zfill aG gz (tfmem inp asp arnd)) arom)
      (mkst RA 0x1001228 (zmemT inp asp arnd aG gz) arom) := by
    apply msteps.mst_step _ _ _ rfl
    · apply step_blt_ft (hf := TF_1001210) (he := rfl) (hd := TD_1001210)
      getr_resolve; regupd_resolve
      apply c_lts_pos_0
      exact Hagl
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := aG)
        (hf := TF_1001214) (he := rfl) (hd := TD_1001214) (hrd := rfl)
      getr_resolve; regupd_resolve; apply v_addi_0
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 0)
        (hf := TF_1001218) (he := rfl) (hd := TD_1001218) (hrd := rfl)
      getr_resolve; bveq
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 1)
        (hf := TF_100121c) (he := rfl) (hd := TD_100121c) (hrd := rfl)
      getr_resolve; bveq
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 32)
        (hf := TF_1001220) (he := rfl) (hd := TD_1001220) (hrd := rfl)
      getr_resolve; bveq
    norm_pc
    apply msteps.mst_step _ _ _ rfl
    · apply step_addi_at (v := nat_to_word 1)
        (hf := TF_1001224) (he := rfl) (hd := TD_1001224) (hrd := rfl)
      getr_resolve; bveq
    norm_pc
    exact msteps.mst_refl _
  obtain ⟨regsC, HagC, H12C, H15C, HmsC⟩ := target_copy_outer inp Hva Hve asp arnd Hsp_lo Hsp_hi
    Hge2 aG gz HaPos Hgz_lo HaCeil inp.in_argv.length 1 RA (by omega) (by omega) (by omega)
    (by dsimp only [RA]; regupd_resolve; exact H8r)
    (by dsimp only [RA]; regupd_resolve; exact H9r)
    (by dsimp only [RA]; regupd_resolve; rfl)
    (by dsimp only [RA]; regupd_resolve; rfl)
    (by dsimp only [RA]; regupd_resolve; rw [pbJ_1]; rfl)
    (by dsimp only [RA]; regupd_resolve; rfl)
    (by dsimp only [RA]; regupd_resolve; rfl)
  simp only [Nat.sub_self, List.take_zero, join1, wbytes] at HmsC
  apply msteps_twm _ _ _ _ _ _ HmsA
  apply msteps_twm _ _ _ _ _ _ HmsC
  apply target_out inp Hva asp arnd Hsp_lo Hsp_hi Hge2 aG gz HaPos Hgz_lo HaCeil
  · rw [HagC 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [RA]; regupd_resolve; exact H2r
  · rw [HagC 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [RA]; regupd_resolve; rfl
  · exact H12C
  · exact H15C

-- The packaged tmw derivation for the target binary.

theorem target_tmw (inp : ProcInput) (Hva : valid_argv inp.in_argv)
    (Hve : valid_envp inp.in_envp) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
    (abrk amb : word) (Hge2 : 2 ≤ inp.in_argv.length)
    (Hcap : bv_unsigned (ttot inp) ≤ 65536) :
    tmw target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      [] (Z_to_bv 64 4) [jout inp.in_argv] (Z_to_bv 64 0) := by
  have Htg1 := ttotn_ge1 inp Hge2
  have Htb := ttotn_bound inp Hva
  have Hut := u_ttot inp Hva
  obtain ⟨regsE, HE2, HE8, HE9, HE11, HE12, HE13, HE14, HE15, HE17, Hms⟩ :=
    target_to_mmap inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2 Hcap
  apply msteps_tmw _ _ _ _ _ _ _ _ Hms
  apply tmw_mmap_rec
  · exact HE17
  · rw [HE11]
    intro Heq
    have H := congrArg bv_unsigned Heq
    rw [Hut] at H
    change (ttotn inp : Int) = 0 at H
    omega
  · exact HE12
  · exact HE13
  · rw [HE14]; decide
  · exact HE15
  · intro e HIn
    obtain ⟨He1, He2⟩ := mmap_errno_range e HIn
    norm_pc
    exact target_fail_twm inp asp arnd Hsp_lo Hsp_hi _ regsE e He1 He2 HE2
  · intro aa Hg
    rw [HE11] at Hg ⊢
    norm_pc
    obtain ⟨Hg1, Hg2⟩ := pru_Z_bounds (bv_unsigned (ttot inp)) (by omega)
    have Hpruu : bv_unsigned (page_round_up (ttot inp)) = page_round_up_Z (bv_unsigned (ttot inp)) :=
      pru_u _ (by omega)
    obtain ⟨Hpos, Hceil, _Hda, _Hdb⟩ := target_grant_unpack inp _ abrk amb asp aa
      (page_round_up_Z (bv_unsigned (ttot inp)))
      (by omega) (by omega) Hg
    apply target_succ_twm inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2 aa (page_round_up (ttot inp))
      Hpos (by rw [Hpruu]; exact Hg1) (by rw [Hpruu]; exact Hceil) _ regsE HE2 HE8 HE9
  · rw [HE11]
    obtain ⟨_Hg1, Hg2⟩ := pru_Z_bounds (bv_unsigned (ttot inp)) (by omega)
    refine ⟨(0x2aaaaab000 : word), ?_⟩
    exact target_grant_witness inp _ abrk amb asp _ Hsp_lo
      (by omega) (by omega)

end LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_target
