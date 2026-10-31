import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_defs
import LinuxProcessSemantics.Examples.brk_rev_ns.SourceMemImage
import LinuxProcessSemantics.Examples.brk_rev_ns.TargetMemImage
import LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_code

/-! rocq-baseline: 3bd94f932fe0933df59ec88e6cc87819fee0d9d1 -/

/-! # brk-rev-ns target binary: per-binary derivations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Deliverables (Section [TargetProof], generic over av/ev and the
    ASLR window sp):
    - [target_wexit_lt2]  : argc < 2             -> to_wexit [] 2
    - [target_wexit_cap]  : argc >= 2, n > 65536 -> to_wexit [] 3
    - [target_outcomes]   : argc >= 2, n <= 65536 ->
        to_outcomes (init) (init_model) (brkU (rev_buf argv[1])).

    Same conventions as brk_rev_ns_source.v. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_target

open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap (brk_zeros brk_unmaps)
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Examples.brk_rev_ns.SourceMemImage
open LinuxProcessSemantics.Examples.brk_rev_ns.TargetMemImage
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_code
open LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_defs

def trom : word → Option byte := seg_rom target_segs

/-- [sym_block]'s closers, [vm_compute]-free by construction: every goal
    below mentions the ASLR [asp] or the argv pointer, and [vm_compute]
    on an open [bv] term does not fail -- it allocates until the machine
    dies (see [StepTac.bveq]'s docstring). -/
local macro "sc0" : tactic => `(tactic| first
  | rfl | (congr 1 <;> omega) | (apply bv_eq_of_unsigned; u_norm; omega))

/-- The zero-extension a [lbu] leaves in a register, as a [Z] identity:
    this is what closes the [SCReadBase] obligation of every byte load. -/
theorem zext_byte_u : ∀ b : byte,
    bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b :=
  fun b => u_Z2bv _ (u8_range b).1 (by exact (fun h => by omega) (u8_range b).2)

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001158 := by
  rfl

theorem target_reserved_val :
    segments_reserved target_segs = [(0x1000000, 0x1000), (0x1001000, 0x1000)] := by
  decide

/-- Stores at/above the end of the second (read-only) segment are legal
    (ro segments: [0x1000000, 0x1000158) and [0x1001158, 0x1001288)). -/
theorem target_avoids_stack : ∀ (a : word) (n : Int),
    0x1002000 ≤ bv_unsigned a →
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true :=
  fun a n ha => by
    simp only [range_avoids_ro_segs, target_segs, Target.loaded_segments,
      TargetMemImage_loaded_segments, List.all_cons, List.all_nil,
      TargetMemImage_segment_000, TargetMemImage_segment_001, seg_writable,
      Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    omega

/-- A region free against the page-rounded reservations avoids both
    read-only segments everywhere inside it. -/
theorem target_free_avoids : ∀ (b l : word),
    region_free (segments_reserved target_segs) b l = true →
    0 < bv_unsigned l → ∀ (a : word) (k : Int),
    bv_unsigned b ≤ bv_unsigned a →
    bv_unsigned a + k ≤ bv_unsigned b + bv_unsigned l →
    range_avoids_ro_segs target_segs (bv_unsigned a) k = true :=
  fun b l hfree hl a k hlo hhi => by
    rw [target_reserved_val] at hfree
    simp only [region_free, iv_overlap, Bool.and_true, Bool.and_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hfree
    simp only [range_avoids_ro_segs, target_segs, Target.loaded_segments,
      TargetMemImage_loaded_segments, List.all_cons, List.all_nil,
      TargetMemImage_segment_000, TargetMemImage_segment_001, seg_writable,
      Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact (fun (h : (¬ bv_unsigned b < 0x1000000 + 0x1000 ∨
          ¬ 0x1000000 < bv_unsigned b + bv_unsigned l) ∧
        (¬ bv_unsigned b < 0x1001000 + 0x1000 ∨
          ¬ 0x1001000 < bv_unsigned b + bv_unsigned l)) => by omega) hfree

section TargetProof

variable (inp : ProcInput)
variable (Hva : valid_argv inp.in_argv) (Hve : valid_envp inp.in_envp)
variable (asp : word)

/-! The target run's own AT_RANDOM draw, independent of the source's
    (the [ed_random] half of [Run.ExecEntry]'s [en_draw]; see the source file). -/
variable (arnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned asp)
variable (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)

include Hsp_lo in
theorem asp_lo_num : 0x7fff80000000 ≤ bv_unsigned asp := Hsp_lo

include Hsp_hi in
theorem asp_hi_num : bv_unsigned asp ≤ 0x800000000000 := Hsp_hi

/-! The quantified initial program break ([Run.valid_brk] window, like the
    SP above), including the page alignment used by physical [brk] grants. -/
variable (abrk amb : word)
variable (Hbrk_lo : reserved_top (segments_reserved target_segs) ≤ bv_unsigned abrk)
variable (Hbrk_hi : bv_unsigned abrk ≤ reserved_top (segments_reserved target_segs) + brk_aslr_max)

theorem rtop_tgt_val : reserved_top (segments_reserved target_segs) = 0x1002000 := by
  rw [target_reserved_val]
  rfl

include Hbrk_lo in
theorem abrk_lo_num : 0x1002000 ≤ bv_unsigned abrk := by
  rw [← rtop_tgt_val]
  exact Hbrk_lo

include Hbrk_hi in
theorem abrk_hi_num : bv_unsigned abrk ≤ 0x1002000 + 1073741824 := by
  rw [← rtop_tgt_val, ← brk_aslr_max_val]
  exact Hbrk_hi

include Hbrk_hi in
theorem abrk_lt64 : bv_unsigned abrk < 2 ^ 64 := by
  exact (fun h => by omega) (abrk_hi_num abrk Hbrk_hi)

def targcN : word := len_word inp.in_argv

def awmem : word → Option byte :=
  wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd

include Hva in
theorem u_targcN : bv_unsigned (targcN inp) = (inp.in_argv.length : Int) := by
  exact u_Z2bv _ (by omega) (by exact (fun h => by omega) (valid_argv_len _ Hva))

include Hva Hve Hsp_hi in
theorem target_bsb_nw :
    bv_unsigned asp + ((build_stack_bytes target_phdrs asp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap arnd).length : Int) < 2 ^ 64 := by
  exact (fun hb hs => by omega)
    (bsb_bound target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd Hva Hve)
    (asp_hi_num asp Hsp_hi)

/-- Memory after the entry prologue (sp = asp - 16): ra = 0, s0 = 0. -/
def amem1 : word → Option byte :=
  wbytes (wbytes (awmem inp asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))

/-- Memory after main's prologue (sp = asp - 32):
    ra = 0x1001178 at asp-24, s0 = asp at asp-32. -/
def tfmem : word → Option byte :=
  wbytes (wbytes (amem1 inp asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 24)) (word_to_le_bytes 8 (0x1001178 : word)))
    (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 asp)

include Hsp_lo Hsp_hi in
theorem rdn_amem1_above (a : word) (n : Nat)
    (Ha : bv_unsigned asp ≤ bv_unsigned a) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs (amem1 inp asp arnd) a n = rdn target_segs (awmem inp asp arnd) a n := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold amem1
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hn]
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hn]

include Hsp_lo Hsp_hi in
theorem rdn_tfmem_above (a : word) (n : Nat)
    (Ha : bv_unsigned asp ≤ bv_unsigned a) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs (tfmem inp asp arnd) a n = rdn target_segs (awmem inp asp arnd) a n := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hn]
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) Hn]
  exact rdn_amem1_above inp asp arnd Hsp_lo Hsp_hi a n Ha Hn

theorem rdn_awmem_stack : ∀ (a : word) (n : Nat),
    bv_unsigned asp ≤ bv_unsigned a → bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    rdn target_segs (awmem inp asp arnd) a n =
      rdn target_segs (stack_to_mem asp (entry_stack_image target_phdrs asp
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd)) a n :=
  fun a n ha hn => rdn_wrap_stack_above target_segs target_phdrs asp
    inp.in_argv inp.in_envp a n inp.in_uid inp.in_hwcap arnd ha hn

include Hva Hve Hsp_lo Hsp_hi in
theorem read_argc_a1 :
    rdn target_segs (amem1 inp asp arnd) asp 8 = some (word_le8 (targcN inp)) := by
  have Hhi := asp_hi_num asp Hsp_hi
  rw [rdn_amem1_above inp asp arnd Hsp_lo Hsp_hi _ _ (by omega) (by omega)]
  rw [rdn_awmem_stack inp asp arnd _ _ (by omega) (by omega)]
  exact read_argc _ _ _ _ _ _ _ _ (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

def targ1 : List byte := inp.in_argv.getD 1 []

def tnn : Nat := (targ1 inp).length

def tnN : word := nat_to_word (tnn inp)

def ptrA : word := cat_argv_ptr asp inp.in_argv inp.in_envp 1

include Hsp_lo Hsp_hi in
theorem read_slot_ra_t :
    rdn target_segs (tfmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x1001178 : word)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega)
    (by u_norm; omega)]
  apply rdn_wbytes_hit8
  u_norm; omega

include Hsp_lo Hsp_hi in
theorem read_slot_s0_t :
    rdn target_segs (tfmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  apply rdn_wbytes_hit8
  u_norm; omega

include Hsp_lo Hsp_hi in
theorem target_exit (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (H14 : reg_get regs 14 = code) (Hc : bv_unsigned code < 256)
    (Hra : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x1001178 : word)))
    (Hs0 : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp)) :
    to_wexit target_segs (mkst regs 0x1001258 mem trom) [] code := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  sym_block target_segs 8 [] [ELit 0x1001178]
    [((2 : reg), EVar 32), ((14 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned asp - 32), code] [Z_to_bv 64 0, asp] R HR
  · refine ⟨⟨by omega, by omega, by omega⟩,
      ⟨word_to_le_bytes 8 asp, Hs0, bytes_le_to_Z_8 _⟩,
      ⟨by omega, by omega, by omega⟩,
      ⟨word_to_le_bytes 8 (0x1001178 : word), Hra, bytes_le_to_Z_8 _⟩⟩
  · exact H2
  · exact H14
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ TF_100117c rfl
  apply tw_exit_coden
  · sym_regs HR; decide +kernel
  · sym_regs HR; exact v_addi_0 _
  · exact Hc

include Hva Hve Hsp_lo Hsp_hi in
/-- argc < 2: no output, exit 2. -/
theorem target_wexit_lt2 (Hlt2 : inp.in_argv.length < 2) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 2) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  rw [init_mkst]
  norm_pc
  change to_wexit target_segs (mkst _ _ (awmem inp asp arnd) trom) _ _
  sym_block target_segs 17 [false] []
    [((2 : reg), EVar 32)] [asp] [targcN inp] R HR
  · have Hu := u_targcN inp Hva
    refine ⟨?_, ⟨by omega, by omega, by omega⟩, ?_,
      ⟨by omega, by omega, by omega⟩, ?_, ⟨by omega, by omega, by omega⟩, ?_⟩
    · sym_br
    · rw [Int.add_zero, show Z_to_bv 64 (bv_unsigned asp) = asp from v_addi_0 asp]
      refine ⟨word_le8 (targcN inp), ?_, bytes_le_n_to_le_8 _⟩
      rw [rdn_awmem_stack inp asp arnd _ _ (by omega) (by omega)]
      exact read_argc _ _ _ _ _ _ _ _ (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    · unfold awmem; solve_store_ok
    · unfold awmem; solve_store_ok
  · getr_resolve; rfl
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ TF_100117c rfl
  apply tw_exit_coden
  · sym_regs HR; decide +kernel
  · sym_regs HR; sym_close
  · decide

section Ge2MainT

variable (Hge2 : 2 ≤ inp.in_argv.length)

include Hva Hge2 in
theorem tnN_le : (tnn inp : Int) ≤ 131071 :=
  valid_argv_str_len inp.in_argv 1 Hva (by omega)

include Hva Hge2 in
/-- The one buffer this program ever writes -- argv[1] reversed plus a
    newline -- is short enough for the model to transfer in one [write]:
    [valid_argv] caps a single argv string at 131071 bytes, and
    131071 + 1 = [rw_bytes_max]. -/
theorem tbufs_modeled : bufs_modeled [rev_buf (targ1 inp)] := by
  exact bufs_modeled_single _ (by
    simp only [buf_modeled, length_rev_buf, Int.natCast_succ]
    exact (fun (h : ((targ1 inp).length : Int) ≤ 131071) => by
      exact (show ((targ1 inp).length : Int) + 1 ≤ 131072 from by omega))
      (tnN_le inp Hva Hge2))

include Hva Hge2 in
theorem u_tnN : bv_unsigned (tnN inp) = (tnn inp : Int) :=
  u_ntw (tnn inp) (by exact (fun h => by omega) (tnN_le inp Hva Hge2))

include Hva Hge2 in
theorem u_tnN1 : bv_unsigned (tnN inp + 1) = (tnn inp : Int) + 1 := by
  exact (fun (h1 : bv_unsigned (1 : word) = 1) => by
    rw [u_add_small (tnN inp) 1 (by
      rw [u_tnN inp Hva Hge2, h1]
      exact (fun h => by omega) (tnN_le inp Hva Hge2)), u_tnN inp Hva Hge2, h1]) rfl

include Hva Hge2 in
theorem targ1_nz : Z_to_bv 8 0 ∉ targ1 inp :=
  valid_argv_str_nz inp.in_argv 1 Hva (by omega)

include Hva Hve Hsp_hi Hge2 in
theorem ptrA_bounds :
    bv_unsigned asp ≤ bv_unsigned (ptrA inp asp) ∧
    bv_unsigned (ptrA inp asp) + (tnn inp : Int) + 1 < 2 ^ 64 :=
  argv_ptr_bounds asp inp.in_argv inp.in_envp 1 Hva Hve (by omega)
    (by simp only [argv_layout_slack]; exact (fun h => by omega) (asp_hi_num asp Hsp_hi))

include Hva Hve Hsp_hi Hge2 in
theorem ptrA_lo : bv_unsigned asp ≤ bv_unsigned (ptrA inp asp) :=
  (ptrA_bounds inp Hva Hve asp Hsp_hi Hge2).1

include Hva Hve Hsp_hi Hge2 in
theorem ptrA_hi : bv_unsigned (ptrA inp asp) + (tnn inp : Int) + 1 < 2 ^ 64 :=
  (ptrA_bounds inp Hva Hve asp Hsp_hi Hge2).2



include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- The whole NUL-terminated string at ptrA (through tfmem). -/
theorem read_str_t :
    rdn target_segs (tfmem inp asp arnd) (ptrA inp asp) (Nat.succ (tnn inp)) =
      some (targ1 inp ++ [Z_to_bv 8 0]) := by
  obtain ⟨Hlo, Hhi⟩ := ptrA_bounds inp Hva Hve asp Hsp_hi Hge2
  rw [rdn_tfmem_above inp asp arnd Hsp_lo Hsp_hi _ _ Hlo (by omega)]
  rw [rdn_awmem_stack inp asp arnd _ _ Hlo (by omega)]
  apply rdn_app (n1 := tnn inp) (n2 := 1)
  · exact read_argv_str_k _ _ _ _ _ _ _ _ _ (by omega)
      (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
  · have Hb := read_argv_byte_k target_phdrs target_segs asp inp.in_argv inp.in_envp
      1 (tnn inp) inp.in_uid inp.in_hwcap arnd (by omega) (Nat.le_refl _)
      (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    change rdn _ _ _ _ = some [byte_at (targ1 inp) (targ1 inp).length] at Hb
    rw [byte_at_len] at Hb
    exact Hb

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- From the entry point to the strlen loop head 0x1001270. -/
theorem target_to_loop :
    ∃ regs1, reg_get regs1 1 = (0x10011ac : word) ∧
      reg_get regs1 2 = Z_to_bv 64 (bv_unsigned asp - 32) ∧
      reg_get regs1 8 = ptrA inp asp ∧ reg_get regs1 10 = ptrA inp asp ∧
      reg_get regs1 11 = Z_to_bv 64 0 ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs1 0x1001270 (tfmem inp asp arnd) trom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  have Hplo := ptrA_lo inp Hva Hve asp Hsp_hi Hge2
  have Hphi := ptrA_hi inp Hva Hve asp Hsp_hi Hge2
  have HnnLe := tnN_le inp Hva Hge2
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
      (Z_to_bv 64 0x1001158) (awmem inp asp arnd) trom)
    18 [true] [] [((2 : reg), EVar 32)] [asp] [targcN inp, ptrA inp asp] R HR Hms
  · have Hu := u_targcN inp Hva
    refine ⟨⟨by omega, by omega, by omega⟩, ?_,
      ⟨by omega, by omega, by omega⟩, ?_, ⟨by omega, by omega, by omega⟩, ?_, ?_,
      ⟨by omega, by omega, by omega⟩, ?_,
      ⟨by omega, by omega, by omega⟩, ?_, ⟨by omega, by omega, by omega⟩, ?_⟩
    · have E : Z_to_bv 64 (bv_unsigned asp + 16) = asp + nat_to_word (8 + 8 * 1) := by
        rw [word_add_nat]; rfl
      rw [E]
      refine ⟨word_le8 (ptrA inp asp), ?_, bytes_le_n_to_le_8 _⟩
      rw [rdn_awmem_stack inp asp arnd _ _ (by rw [word_add_nat]; u_norm; omega)
        (by rw [word_add_nat]; u_norm; omega)]
      exact read_argv_ptr_k _ _ _ _ _ _ _ _ _ (by omega)
        (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    · unfold awmem; solve_store_ok
    · unfold awmem; solve_store_ok
    · sym_br
    · rw [Int.add_zero, show Z_to_bv 64 (bv_unsigned asp) = asp from v_addi_0 asp]
      refine ⟨word_le8 (targcN inp), ?_, bytes_le_n_to_le_8 _⟩
      rw [rdn_awmem_stack inp asp arnd _ _ (by omega) (by omega)]
      exact read_argc _ _ _ _ _ _ _ _ (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    · unfold awmem; solve_store_ok
    · unfold awmem; solve_store_ok
  · getr_resolve; rfl
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_regs HR <;> rfl
  · sym_regs HR; sc0
  · sym_regs HR
  · sym_regs HR; exact v_addi_0 _
  · sym_regs HR <;> rfl
  · rw [init_mkst]
    norm_pc
    sym_chain Hms
    unfold tfmem amem1
    sym_mem_norm
    getr_resolve
    regupd_resolve
    exact msteps.mst_refl _


include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- The strlen loop: from 0x1001270 with a1 = j, exit at 0x1001280 with
    a1 = n + 1. -/
theorem target_strlen (mem : word → Option byte)
    (Hread : rdn target_segs mem (ptrA inp asp) (Nat.succ (tnn inp)) =
      some (targ1 inp ++ [Z_to_bv 8 0])) (d j : Nat) (regs : bvmap 5 word)
    (Hjd : j + d = tnn inp) (Hr10 : reg_get regs 10 = ptrA inp asp)
    (Hr11 : reg_get regs 11 = nat_to_word j) :
    ∃ regs', (∀ x : reg, x ≠ 11 → x ≠ 12 → reg_get regs' x = reg_get regs x) ∧
      reg_get regs' 11 = tnN inp + 1 ∧
      msteps target_segs (mkst regs 0x1001270 mem trom) (mkst regs' 0x1001280 mem trom) := by
  have HnnLe := tnN_le inp Hva Hge2
  have Hplo := ptrA_lo inp Hva Hve asp Hsp_hi Hge2
  have Hlo := asp_lo_num asp Hsp_lo
  have Hnz := targ1_nz inp Hva Hge2
  induction d generalizing j regs with
  | zero =>
    have Hj : j = tnn inp := by omega
    let b : byte := Z_to_bv 8 0
    let regs1 := regupd regs 12 (ptrA inp asp + nat_to_word j)
    let regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 11 (nat_to_word (Nat.succ j))
    have Hb : rdn target_segs mem (ptrA inp asp + nat_to_word j) 1 = some [b] := by
      have H := rdn_nth _ _ _ _ _ j Hread (by omega)
      change rdn _ _ _ _ = some [byte_at (targ1 inp) j] at H
      rw [show j = (targ1 inp).length from Hj, byte_at_len] at H
      rw [Hj]
      exact H
    have Hms : msteps target_segs (mkst regs 0x1001270 mem trom)
        (mkst regs3 0x1001280 mem trom) := by
      stepiv TF_1001270 TD_1001270 (ptrA inp asp + nat_to_word j)
        (getr_resolve; rw [Hr10, Hr11]; exact alu_add _ _)
      chain_step
      · rfl
      · apply step_lbu (b := b) (hfetch := TF_1001274) (hecall := rfl) (hdecode := TD_1001274)
        getr_resolve; regupd_resolve
        imm_norm; rw [v_addi_0]; exact Hb
      step_simpl
      stepiv TF_1001278 TD_1001278 (nat_to_word (Nat.succ j))
        (getr_resolve; regupd_resolve; rw [Hr11]; imm_norm; exact nat_to_word_S j)
      chain_step
      · rfl
      · apply step_bne_ft (hf := TF_100127c) (he := rfl) (hd := TD_100127c)
        getr_resolve; regupd_resolve
        exact c_eq_0_true
      norm_pc
      exact msteps.mst_refl _
    refine ⟨regs3, ?_, ?_, Hms⟩
    · intro x H11 H12
      dsimp only [regs3, regs2, regs1]
      rw [regupd_other _ _ _ _ H11, regupd_other _ _ _ _ H12,
        regupd_other _ _ _ _ H12]
    · dsimp only [regs3]
      rw [regupd_same, Hj]
      unfold tnN
      rw [word1_nat, nat_to_word_merge]
  | succ d IH =>
    have Hjlt : j < tnn inp := by omega
    let b := byte_at (targ1 inp) j
    have Hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ Hnz Hjlt
    let regs1 := regupd regs 12 (ptrA inp asp + nat_to_word j)
    let regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))
    let regs3 := regupd regs2 11 (nat_to_word (Nat.succ j))
    have Hb : rdn target_segs mem (ptrA inp asp + nat_to_word j) 1 = some [b] := by
      have H := rdn_nth _ _ _ _ _ j Hread (by omega)
      exact H
    have Hms : msteps target_segs (mkst regs 0x1001270 mem trom)
        (mkst regs3 0x1001270 mem trom) := by
      stepiv TF_1001270 TD_1001270 (ptrA inp asp + nat_to_word j)
        (getr_resolve; rw [Hr10, Hr11]; exact alu_add _ _)
      chain_step
      · rfl
      · apply step_lbu (b := b) (hfetch := TF_1001274) (hecall := rfl) (hdecode := TD_1001274)
        getr_resolve; regupd_resolve
        imm_norm; rw [v_addi_0]; exact Hb
      step_simpl
      stepiv TF_1001278 TD_1001278 (nat_to_word (Nat.succ j))
        (getr_resolve; regupd_resolve; rw [Hr11]; imm_norm; exact nat_to_word_S j)
      chain_step
      · rfl
      · apply step_bne_tk (hf := TF_100127c) (he := rfl) (hd := TD_100127c)
        getr_resolve; regupd_resolve
        apply c_eq_0_false
        rw [u_zext8]
        exact byte_nz_u _ Hbnz
      norm_pc
      exact msteps.mst_refl _
    obtain ⟨regs', Hag, H11, Hms'⟩ := IH (Nat.succ j) regs3 (by omega)
      (by dsimp only [regs3, regs2, regs1]; regupd_resolve; exact Hr10)
      (by dsimp only [regs3]; exact regupd_same _ _ _)
    refine ⟨regs', ?_, H11, msteps_trans _ _ _ _ Hms Hms'⟩
    intro x H11' H12'
    rw [Hag x H11' H12']
    dsimp only [regs3, regs2, regs1]
    rw [regupd_other _ _ _ _ H11', regupd_other _ _ _ _ H12',
      regupd_other _ _ _ _ H12']

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- After strlen: back in main at 0x10011ac with a0 = n. -/
theorem target_to_captest :
    ∃ regs2, reg_get regs2 1 = (0x10011ac : word) ∧
      reg_get regs2 2 = Z_to_bv 64 (bv_unsigned asp - 32) ∧
      reg_get regs2 8 = ptrA inp asp ∧ reg_get regs2 10 = tnN inp ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs2 0x10011ac (tfmem inp asp arnd) trom) := by
  obtain ⟨regs1, H1, H2, H8, H10, H11, Hms1⟩ :=
    target_to_loop inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2
  obtain ⟨regs2, Hag, H11', Hms2⟩ := target_strlen inp Hva Hve asp Hsp_lo Hsp_hi Hge2
    (tfmem inp asp arnd) (read_str_t inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2)
    (tnn inp) 0 regs1 (by omega) H10 H11
  refine ⟨regupd regs2 10 (tnN inp), ?_, ?_, ?_, ?_, ?_⟩
  · regupd_resolve; rw [Hag 1 (by decide) (by decide)]; exact H1
  · regupd_resolve; rw [Hag 2 (by decide) (by decide)]; exact H2
  · regupd_resolve; rw [Hag 8 (by decide) (by decide)]; exact H8
  · regupd_resolve; rfl
  · apply msteps_trans _ _ _ _ Hms1
    apply msteps_trans _ _ _ _ Hms2
    stepiv TF_1001280 TD_1001280 (tnN inp)
      (getr_resolve; rw [H11']; imm_norm; exact v_addi_pred _)
    stepjr TF_1001284 TD_1001284 (0x10011ac : word)
      (getr_resolve; regupd_resolve; rw [Hag 1 (by decide) (by decide)]; exact H1)
    exact msteps.mst_refl _

include Hva Hve Hsp_lo Hsp_hi Hge2 in
/-- n > 65536: no output, exit 3. -/
theorem target_wexit_cap (Hcap : 65536 < (tnn inp : Int)) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 3) := by
  have HnnLe := tnN_le inp Hva Hge2
  obtain ⟨regs2, H1, H2, H8, H10, Hms⟩ :=
    target_to_captest inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2
  apply msteps_to_wexit _ _ _ _ _ Hms
  sym_block target_segs 4 [false] []
    [((2 : reg), EVar 32), ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned asp - 32), tnN inp] [] R HR
  · have Hu := u_tnN inp Hva Hge2
    sym_br
  · exact H2
  · exact H10
  apply target_exit asp Hsp_lo Hsp_hi
  · sym_regs HR <;> rfl
  · sym_regs HR <;> rfl
  · decide
  · exact read_slot_ra_t inp asp arnd Hsp_lo Hsp_hi
  · exact read_slot_s0_t inp asp arnd Hsp_lo Hsp_hi


include Hva Hve Hsp_lo Hsp_hi Hge2 in
theorem target_copy (r : word) (mem0 : word → Option byte)
    (Hgok : store_grant_ok target_segs mem0 r (tnN inp + 1))
    (Hstr : rdn target_segs mem0 (ptrA inp asp) (Nat.succ (tnn inp)) =
      some (targ1 inp ++ [Z_to_bv 8 0]))
    (_Hfree : region_free (segments_reserved target_segs) r (tnN inp + 1) = true)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + (tnn inp : Int) + 1 ≤ bv_unsigned asp - stack_max_size)
    (d : Nat) (regs : bvmap 5 word) (Hd1 : 1 ≤ d) (Hd : d ≤ tnn inp)
    (Hr10 : reg_get regs 10 = Z_to_bv 64 (-(d : Int)))
    (Hr14 : reg_get regs 14 = Z_to_bv 64 (bv_unsigned (ptrA inp asp) + (d : Int) - 1))
    (Hr15 : reg_get regs 15 = r + nat_to_word (tnn inp - d)) :
    ∃ regs', (∀ x : reg, x ≠ 16 → x ≠ 10 → x ≠ 14 → x ≠ 15 →
      reg_get regs' x = reg_get regs x) ∧ reg_get regs' 15 = r + tnN inp ∧
      msteps target_segs
        (mkst regs 0x1001208 (wbytes mem0 r ((targ1 inp).reverse.take (tnn inp - d))) trom)
        (mkst regs' 0x1001220 (wbytes mem0 r (targ1 inp).reverse) trom) := by
  have Hplo := ptrA_lo inp Hva Hve asp Hsp_hi Hge2
  have Hphi := ptrA_hi inp Hva Hve asp Hsp_hi Hge2
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HnnLe := tnN_le inp Hva Hge2
  have Hur := u64_range r
  have HnnA : (targ1 inp).length = tnn inp := rfl
  have Hsms := stack_max_size_val
  induction d generalizing regs with
  | zero => omega
  | succ d IH =>
    let memI := wbytes mem0 r ((targ1 inp).reverse.take (tnn inp - Nat.succ d))
    let b := byte_at (targ1 inp) d
    have HlenF : ((targ1 inp).reverse.take (tnn inp - Nat.succ d)).length =
        tnn inp - Nat.succ d := by
      rw [List.length_take, List.length_reverse, Nat.min_eq_left (by omega)]
    have Hud : bv_unsigned (ptrA inp asp + nat_to_word d) =
        bv_unsigned (ptrA inp asp) + (d : Int) := by
      rw [word_add_nat]; u_norm; rfl
    have HuW : bv_unsigned (r + nat_to_word (tnn inp - Nat.succ d)) =
        bv_unsigned r + (tnn inp - Nat.succ d : Nat) := by
      rw [word_add_nat]; u_norm; rfl
    let regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned b))
    let regs2 := regupd regs1 10 (Z_to_bv 64 (-(d : Int)))
    let regs3 := regupd regs2 14 (Z_to_bv 64 (bv_unsigned (ptrA inp asp) + (d : Int) - 1))
    let memI' := wbytes mem0 r ((targ1 inp).reverse.take (tnn inp - d))
    let regs4 := regupd regs3 15 (r + nat_to_word (tnn inp - d))
    have Hb : rdn target_segs memI
        (Z_to_bv 64 (bv_unsigned (ptrA inp asp) + (Nat.succ d : Int) - 1)) 1 = some [b] := by
      have E : Z_to_bv 64 (bv_unsigned (ptrA inp asp) + (Nat.succ d : Int) - 1) =
          ptrA inp asp + nat_to_word d := by
        rw [word_add_nat]
        exact congrArg (Z_to_bv 64) (by omega)
      rw [E]
      unfold memI
      rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [HlenF, Hud]; omega) (by rw [Hud]; omega)]
      exact rdn_nth _ _ _ _ _ d Hstr (by omega)
    have Ew : wbytes memI (r + nat_to_word (tnn inp - Nat.succ d)) [b] = memI' := by
      unfold memI' memI
      rw [show tnn inp - d = Nat.succ (tnn inp - Nat.succ d) by omega,
        firstn_rev_snoc _ _ (by omega), wbytes_app, HlenF]
      rw [show (targ1 inp).length - Nat.succ (tnn inp - Nat.succ d) = d by omega]
      dsimp only [b]
      rw [nth_lt_byte_at (targ1 inp) d (by omega)]
    have Hms : msteps target_segs (mkst regs 0x1001208 memI trom)
        (mkst regs4 0x100121c memI' trom) := by
      chain_step
      · rfl
      · apply step_lbu (b := b) (hfetch := TF_1001208) (hecall := rfl) (hdecode := TD_1001208)
        getr_resolve; rw [Hr14]; imm_norm; rw [v_addi_0]; exact Hb
      step_simpl
      stepiv TF_100120c TD_100120c (Z_to_bv 64 (-(d : Int)))
        (getr_resolve; regupd_resolve; rw [Hr10]; imm_norm; exact v_addi_neg_S d)
      stepiv TF_1001210 TD_1001210
        (Z_to_bv 64 (bv_unsigned (ptrA inp asp) + (d : Int) - 1))
        (getr_resolve; regupd_resolve; rw [Hr14]; imm_norm;
         rw [v_addi_m1 _ (by u_norm; omega)]; u_norm; exact congrArg (Z_to_bv 64) (by omega))
      chain_step
      · rfl
      · apply LinuxProcessSemantics.Common.MmapSim.step_sb_at (Hv := rfl)
          (a := r + nat_to_word (tnn inp - Nat.succ d)) (b := b)
          (Hf := TF_1001214) (He := rfl) (Hd := TD_1001214)
        · getr_resolve; regupd_resolve; rw [Hr15]; imm_norm; exact v_addi_0 _
        · getr_resolve; regupd_resolve; exact zext8_byte b
        · store_ok_peel
          apply Hgok
          all_goals simp only [u_tnN1 inp Hva Hge2, HuW] <;> omega
      step_simpl
      rw [Ew]
      stepiv TF_1001218 TD_1001218 (r + nat_to_word (tnn inp - d))
        (getr_resolve; regupd_resolve; rw [Hr15]; imm_norm;
         rw [LinuxProcessSemantics.Common.StepTac.word_add_nat_1]; exact congrArg (fun k => r + nat_to_word k) (by omega))
      exact msteps.mst_refl _
    by_cases Hz : d = 0
    · subst d
      refine ⟨regs4, ?_, ?_, ?_⟩
      · intro x H16 H10 H14 H15
        dsimp only [regs4, regs3, regs2, regs1]
        rw [regupd_other _ _ _ _ H15, regupd_other _ _ _ _ H14,
          regupd_other _ _ _ _ H10, regupd_other _ _ _ _ H16]
      · dsimp only [regs4]; rw [regupd_same, Nat.sub_zero]; rfl
      · apply msteps_trans _ _ _ _ Hms
        chain_step
        · rfl
        · apply step_bne_ft (hf := TF_100121c) (he := rfl) (hd := TD_100121c)
          dsimp only [regs4, regs3, regs2]
          getr_resolve; regupd_resolve; exact c_eq_0_true
        norm_pc
        dsimp only [memI']
        rw [Nat.sub_zero, show (targ1 inp).reverse.take (tnn inp) = (targ1 inp).reverse from firstn_all_rev _]
        exact msteps.mst_refl _
    · obtain ⟨regs', Hag, H15, Hms'⟩ := IH regs4 (by omega) (by omega)
        (by dsimp only [regs4, regs3, regs2]; regupd_resolve; rfl)
        (by dsimp only [regs4, regs3]; regupd_resolve; rfl)
        (by dsimp only [regs4]; exact regupd_same _ _ _)
      refine ⟨regs', ?_, H15, ?_⟩
      · intro x H16 H10 H14 H15'
        rw [Hag x H16 H10 H14 H15']
        dsimp only [regs4, regs3, regs2, regs1]
        rw [regupd_other _ _ _ _ H15', regupd_other _ _ _ _ H14,
          regupd_other _ _ _ _ H10, regupd_other _ _ _ _ H16]
      · apply msteps_trans _ _ _ _ Hms
        chain_step
        · rfl
        · apply step_bne_tk (hf := TF_100121c) (he := rfl) (hd := TD_100121c)
          dsimp only [regs4, regs3, regs2]
          getr_resolve; regupd_resolve
          apply c_eq_0_false
          rw [u_neg_small _ (by omega) (by omega)]; omega
        norm_pc
        exact Hms'


include Hsp_lo Hsp_hi in
/-- The put-style retry loop after a (possibly short) write delivery:
    from the post-write state at 0x100123c — a0 = the delivered length,
    a1 = the offered pointer, a2 = the offered count — the loop runs
    [blez a0] (fall-through, the error arm is dead), bumps the pointer,
    decrements the count, and either falls into the exit-0 tail
    ([bnez a2] not taken) or reissues the write on the remainder. The
    loop is register-only, so the exit tail's two frame reloads see the
    unchanged memory. -/
theorem tgt_put_wall (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 131073) (Hplo : 0 < bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) < 2 ^ 64)
    (H10 : reg_get regs 10 = len_word (rest.take n))
    (H11 : reg_get regs 11 = p) (H12 : reg_get regs 12 = len_word rest)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (H17 : bv_unsigned (reg_get regs 17) = 64)
    (Hread : rdn target_segs mem p rest.length = some rest)
    (Hra : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x1001178 : word)))
    (Hs0 : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp)) :
    to_wall_tail target_segs (Z_to_bv 64 1) (mkst regs 0x100123c mem trom)
      (rest.drop n) (to_wallexit target_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n regs with
  | zero => omega
  | succ fuel IH =>
    chain_step
    · rfl
    · apply step_bge_ft (hf := TF_100123c) (he := rfl) (hd := TD_100123c)
      getr_resolve; rw [H10]
      apply c_lts_0_pos
      all_goals rw [u_len_word_firstn _ _ Hn2 (by omega)]; omega
    norm_pc
    stepiv TF_1001240 TD_1001240 (Z_to_bv 64 (bv_unsigned p + (n : Int)))
      (getr_resolve; rw [H11, H10]; exact v_add_len_firstn_Z p n rest Hn2 (by omega))
    stepiv TF_1001244 TD_1001244 (len_word (rest.drop n))
      (getr_resolve; regupd_resolve; rw [H12, H10]; exact v_sub_len_firstn n rest Hn2 (by omega))
    by_cases Heq : n = rest.length
    · subst n
      rw [List.drop_length]
      chain_step
      · rfl
      · apply step_bne_ft (hf := TF_1001248) (he := rfl) (hd := TD_1001248)
        getr_resolve; regupd_resolve; exact c_eq_0_true
      norm_pc
      stepiv TF_100124c TD_100124c (Z_to_bv 64 0) (getr_resolve; bveq)
      stepj TF_1001250 TD_1001250
      apply to_wall_tail.twt_done
      apply target_exit asp Hsp_lo Hsp_hi
      · regupd_resolve; exact H2
      · regupd_resolve; rfl
      · decide
      · exact Hra
      · exact Hs0
    · have Hsk : rdn target_segs mem (Z_to_bv 64 (bv_unsigned p + (n : Int)))
          (rest.drop n).length = some (rest.drop n) := by
        rw [List.length_drop]
        have H := rdn_skipn target_segs mem rest.length p rest n Hread Hn2
        rw [word_add_nat_Z p n (by omega)] at H
        exact H
      chain_step
      · rfl
      · apply step_bne_tk (hf := TF_1001248) (he := rfl) (hd := TD_1001248)
        getr_resolve; regupd_resolve
        apply c_eq_0_false
        rw [u_len_word _ (by rw [List.length_drop]; omega), List.length_drop]; omega
      norm_pc
      stepiv TF_1001234 TD_1001234 (Z_to_bv 64 1) (getr_resolve; bveq)
      chain_step
      · rfl
      · exact step_ecall _ _ _ _ _ _ TF_1001238 rfl
      apply to_wall_tail.twt_more
      · rw [List.length_drop]; omega
      apply twl_write_rec
      · getr_resolve; regupd_resolve; exact H17
      · regupd_resolve; rfl
      · regupd_resolve
        rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs mem _ (word_to_nat (len_word (rest.drop n))) = _
        have Hcount : word_to_nat (len_word (rest.drop n)) = (rest.drop n).length := by
          change (bv_unsigned (len_word (rest.drop n))).toNat = _
          rw [u_len_word _ (by rw [List.length_drop]; omega), Int.toNat_natCast]
        rw [Hcount]
        exact Hsk
      · rw [List.length_drop]; omega
      · intro m Hm1 Hm2
        norm_pc
        apply IH (rest.drop n) (Z_to_bv 64 (bv_unsigned p + (n : Int))) m
        · rw [List.length_drop]; omega
        · exact Hm1
        · exact Hm2
        · rw [List.length_drop]; omega
        · rw [u_Z2bv _ (by omega) (by omega)]; omega
        · rw [u_Z2bv _ (by omega) (by omega), List.length_drop]; omega
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; exact H2
        · regupd_resolve; exact H17
        · exact Hsk


include Hva Hsp_lo Hsp_hi Hge2 in
theorem target_out (regs : bvmap 5 word) (r grant : word)
    (Hgrant : bv_unsigned (tnN inp + 1) ≤ bv_unsigned grant)
    (Hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned asp - stack_max_size)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + (tnn inp : Int) + 1 ≤ bv_unsigned asp - stack_max_size)
    (_Hfree : region_free (segments_reserved target_segs) r (tnN inp + 1) = true)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (H11 : reg_get regs 11 = r) (H12 : reg_get regs 12 = tnN inp + 1)
    (H13 : reg_get regs 13 = tnN inp) :
    to_wallexit target_segs (Z_to_bv 64 1) [rev_buf (targ1 inp)] (Z_to_bv 64 0)
      (mkst regs 0x1001220 (wbytes (zmem (tfmem inp asp arnd) r grant) r (targ1 inp).reverse) trom) := by
  refine ⟨by rw [length_rev_buf]; omega, ?_⟩
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HnnLe := tnN_le inp Hva Hge2
  have Hur := u64_range r
  have HnnA : (targ1 inp).length = tnn inp := rfl
  have Hun1 := u_tnN1 inp Hva Hge2
  have Hsms := stack_max_size_val
  have Hurn : bv_unsigned (r + tnN inp) = bv_unsigned r + (tnn inp : Int) := by
    rw [u_add_small _ _ (by rw [u_tnN inp Hva Hge2]; omega), u_tnN inp Hva Hge2]
  let mem0 := zmem (tfmem inp asp arnd) r grant
  let memB := wbytes mem0 r (rev_buf (targ1 inp))
  have Hcount : len_word (rev_buf (targ1 inp)) = tnN inp + 1 := by
    apply bv_eq_of_unsigned
    rw [u_len_word _ (by rw [length_rev_buf]; omega), Hun1, length_rev_buf]
    omega
  stepiv TF_1001220 TD_1001220 (r + tnN inp)
    (getr_resolve; rw [H11, H13]; exact alu_add _ _)
  stepiv TF_1001224 TD_1001224 (Z_to_bv 64 10) (getr_resolve; bveq)
  chain_step
  · rfl
  · apply LinuxProcessSemantics.Common.MmapSim.step_sb_at (Hv := rfl) (a := r + tnN inp) (b := Z_to_bv 8 10)
      (Hf := TF_1001228) (He := rfl) (Hd := TD_1001228)
    · getr_resolve; regupd_resolve; imm_norm; exact v_addi_0 _
    · getr_resolve; regupd_resolve; rfl
    · store_ok_peel
      apply store_ok_zmem
      all_goals rw [Hurn] <;> omega
  step_simpl
  have Emem : wbytes (wbytes mem0 r (targ1 inp).reverse) (r + tnN inp) [Z_to_bv 8 10] = memB := by
    unfold memB rev_buf
    rw [wbytes_app, List.length_reverse]
    rfl
  rw [Emem]
  stepiv TF_100122c TD_100122c (Z_to_bv 64 64) (getr_resolve; bveq)
  chain_step
  · rfl
  · apply step_beq_ft (hf := TF_1001230) (he := rfl) (hd := TD_1001230)
    getr_resolve; regupd_resolve; rw [H12]
    apply c_eq_0_false
    rw [Hun1]; omega
  norm_pc
  stepiv TF_1001234 TD_1001234 (Z_to_bv 64 1) (getr_resolve; bveq)
  chain_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ TF_1001238 rfl
  apply to_wall_tail.twt_more
  · rw [length_rev_buf]; omega
  apply twl_write_rec
  · getr_resolve; regupd_resolve; rfl
  · regupd_resolve; rfl
  · regupd_resolve; rw [H11, H12, ← Hcount]
    rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
    change rdn target_segs memB r (word_to_nat (len_word (rev_buf (targ1 inp)))) = _
    have Hnat : word_to_nat (len_word (rev_buf (targ1 inp))) = (rev_buf (targ1 inp)).length := by
      change (bv_unsigned (len_word (rev_buf (targ1 inp)))).toNat = _
      rw [u_len_word _ (by rw [length_rev_buf]; omega), Int.toNat_natCast]
    rw [Hnat]
    apply rdn_wbytes_hit
    rw [length_rev_buf]; omega
  · rw [length_rev_buf]; omega
  · intro n Hn1 Hn2
    norm_pc
    apply tgt_put_wall asp Hsp_lo Hsp_hi (rev_buf (targ1 inp)).length (rev_buf (targ1 inp)) r n
    · omega
    · exact Hn1
    · exact Hn2
    · rw [length_rev_buf]; omega
    · exact Hr0
    · rw [length_rev_buf]; omega
    · regupd_resolve; rfl
    · regupd_resolve; exact H11
    · regupd_resolve; rw [H12]; exact Hcount.symm
    · regupd_resolve; exact H2
    · regupd_resolve; rfl
    · apply rdn_wbytes_hit
      rw [length_rev_buf]; omega
    · unfold memB mem0
      rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_rev_buf]; u_norm; omega) (by u_norm; omega)]
      rw [rdn_zmem_out _ _ _ _ _ _ (by u_norm; omega) (Or.inr (by u_norm; omega))]
      exact read_slot_ra_t inp asp arnd Hsp_lo Hsp_hi
    · unfold memB mem0
      rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_rev_buf]; u_norm; omega) (by u_norm; omega)]
      rw [rdn_zmem_out _ _ _ _ _ _ (by u_norm; omega) (Or.inr (by u_norm; omega))]
      exact read_slot_s0_t inp asp arnd Hsp_lo Hsp_hi


include Hva Hve Hsp_lo Hsp_hi Hge2 in
theorem target_success (regs : bvmap 5 word) (r grant : word)
    (Hgrant : bv_unsigned (tnN inp + 1) ≤ bv_unsigned grant)
    (Hgrantceil : bv_unsigned r + bv_unsigned grant ≤ bv_unsigned asp - stack_max_size)
    (Hr0 : 0 < bv_unsigned r)
    (Hceil : bv_unsigned r + (tnn inp : Int) + 1 ≤ bv_unsigned asp - stack_max_size)
    (Hfree : region_free (segments_reserved target_segs) r (tnN inp + 1) = true)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (H8 : reg_get regs 8 = ptrA inp asp) (H10 : reg_get regs 10 = r + (tnN inp + 1))
    (H11 : reg_get regs 11 = r) (H12 : reg_get regs 12 = tnN inp + 1)
    (H13 : reg_get regs 13 = tnN inp) (H15 : reg_get regs 15 = r + (tnN inp + 1)) :
    to_wallexit target_segs (Z_to_bv 64 1) [rev_buf (targ1 inp)] (Z_to_bv 64 0)
      (mkst regs 0x10011f0 (zmem (tfmem inp asp arnd) r grant) trom) := by
  refine ⟨by rw [length_rev_buf]; omega, ?_⟩
  have Hplo := ptrA_lo inp Hva Hve asp Hsp_hi Hge2
  have Hphi := ptrA_hi inp Hva Hve asp Hsp_hi Hge2
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HnnLe := tnN_le inp Hva Hge2
  have Hur := u64_range r
  have Hsms := stack_max_size_val
  have Hupn : bv_unsigned (ptrA inp asp + tnN inp) = bv_unsigned (ptrA inp asp) + (tnn inp : Int) := by
    rw [u_add_small _ _ (by rw [u_tnN inp Hva Hge2]; omega), u_tnN inp Hva Hge2]
  let mem0 := zmem (tfmem inp asp arnd) r grant
  have Hstr0 : rdn target_segs mem0 (ptrA inp asp) (Nat.succ (tnn inp)) =
      some (targ1 inp ++ [Z_to_bv 8 0]) := by
    unfold mem0
    rw [rdn_zmem_out _ _ _ _ _ _ (by omega) (Or.inr (by omega))]
    exact read_str_t inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2
  let R := regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (-(tnn inp : Int))))
    14 (ptrA inp asp + tnN inp))
    14 (Z_to_bv 64 (bv_unsigned (ptrA inp asp) + (tnn inp : Int) - 1))) 15 r
  have Hms : msteps target_segs (mkst regs 0x10011f0 mem0 trom) (mkst R 0x1001204 mem0 trom) := by
    chain_step
    · rfl
    · apply step_bne_ft (hf := TF_10011f0) (he := rfl) (hd := TD_10011f0)
      getr_resolve; rw [H10, H15]; exact c_eq_refl _
    norm_pc
    stepiv TF_10011f4 TD_10011f4 (Z_to_bv 64 (-(tnn inp : Int)))
      (getr_resolve; rw [H13, v_sub_0_neg, u_tnN inp Hva Hge2])
    stepiv TF_10011f8 TD_10011f8 (ptrA inp asp + tnN inp)
      (getr_resolve; regupd_resolve; rw [H13, H8]; exact LinuxProcessSemantics.Common.StepTac.v_add_comm _ _)
    stepiv TF_10011fc TD_10011fc
      (Z_to_bv 64 (bv_unsigned (ptrA inp asp) + (tnn inp : Int) - 1))
      (getr_resolve; regupd_resolve; imm_norm;
       rw [v_addi_m1 _ (by rw [Hupn]; omega), Hupn])
    stepiv TF_1001200 TD_1001200 r
      (getr_resolve; regupd_resolve; rw [H11]; imm_norm; exact v_addi_0 _)
    exact msteps.mst_refl _
  apply msteps_to_wall_tail _ _ _ _ _ _ Hms
  by_cases Hz : tnn inp = 0
  · have Htarg : targ1 inp = [] := List.length_eq_zero_iff.mp Hz
    chain_step
    · rfl
    · apply step_beq_tk (hf := TF_1001204) (he := rfl) (hd := TD_1001204)
      dsimp only [R]; getr_resolve; regupd_resolve; rw [Hz]; exact c_eq_0_true
    norm_pc
    have Em : wbytes mem0 r (targ1 inp).reverse = mem0 := by rw [Htarg]; rfl
    rw [← Em]
    apply (target_out inp Hva asp arnd Hsp_lo Hsp_hi Hge2 R r grant Hgrant Hgrantceil Hr0 Hceil Hfree
      (by dsimp only [R]; regupd_resolve; exact H2)
      (by dsimp only [R]; regupd_resolve; exact H11)
      (by dsimp only [R]; regupd_resolve; exact H12)
      (by dsimp only [R]; regupd_resolve; exact H13)).2
  · chain_step
    · rfl
    · apply step_beq_ft (hf := TF_1001204) (he := rfl) (hd := TD_1001204)
      dsimp only [R]; getr_resolve; regupd_resolve
      apply c_eq_0_false
      rw [u_neg_small _ (by omega) (by omega)]; omega
    norm_pc
    obtain ⟨regsC, HagC, _H15C, HmsC⟩ :=
      target_copy inp Hva Hve asp Hsp_lo Hsp_hi Hge2 r mem0
        (store_grant_zmem_prefix _ _ _ _ _ Hgrant (by omega)) Hstr0 Hfree Hr0 Hceil (tnn inp) R
        (by omega) (Nat.le_refl _)
        (by dsimp only [R]; regupd_resolve; rfl)
        (by dsimp only [R]; regupd_resolve; rfl)
        (by dsimp only [R]; regupd_resolve; rw [Nat.sub_self, word_add_0])
    simp only [Nat.sub_self, List.take_zero, wbytes] at HmsC
    apply msteps_to_wall_tail _ _ _ _ _ _ HmsC
    apply (target_out inp Hva asp arnd Hsp_lo Hsp_hi Hge2 regsC r grant Hgrant Hgrantceil Hr0 Hceil Hfree
      (by rw [HagC 2 (by decide) (by decide) (by decide) (by decide)];
          dsimp only [R]; regupd_resolve; exact H2)
      (by rw [HagC 11 (by decide) (by decide) (by decide) (by decide)];
          dsimp only [R]; regupd_resolve; exact H11)
      (by rw [HagC 12 (by decide) (by decide) (by decide) (by decide)];
          dsimp only [R]; regupd_resolve; exact H12)
      (by rw [HagC 13 (by decide) (by decide) (by decide) (by decide)];
          dsimp only [R]; regupd_resolve; exact H13)).2


include Hva Hve Hsp_lo Hsp_hi Hge2 in
theorem target_to_brk1 (Hncap : (tnn inp : Int) ≤ 65536) :
    ∃ regs3, reg_get regs3 2 = Z_to_bv 64 (bv_unsigned asp - 32) ∧
      reg_get regs3 8 = ptrA inp asp ∧ reg_get regs3 10 = Z_to_bv 64 0 ∧
      reg_get regs3 13 = tnN inp ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        { ms_regs := regs3, ms_fregs := bvmap_empty, ms_pc_val := 0x10011c8,
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := tfmem inp asp arnd, ms_rom := trom } := by
  have HnnLe := tnN_le inp Hva Hge2
  obtain ⟨regs2, H1, H2, H8, H10, Hms⟩ :=
    target_to_captest inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2
  sym_block_ex target_segs (mkst regs2 (Z_to_bv 64 0x10011ac) (tfmem inp asp arnd) trom)
    6 [true] [] [((2 : reg), EVar 32), ((8 : reg), EVar 33), ((10 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned asp - 32), ptrA inp asp, tnN inp] [] R HR Hms2
  · have Hu := u_tnN inp Hva Hge2
    sym_br
  · exact H2
  · exact H8
  · exact H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · sym_regs HR
  · sym_regs HR
  · sym_regs HR <;> rfl
  · sym_regs HR; exact v_addi_0 _
  · apply msteps_trans _ _ _ _ Hms
    sym_chain Hms2
    chain_step
    · rfl
    · exact step_ecall _ _ _ _ _ _ TF_10011c8 rfl
    have H17 : getr R 17 = Z_to_bv 64 214 := by sym_regs HR <;> rfl
    rw [H17]
    exact msteps.mst_refl _

include Hva Hge2 in
theorem target_to_brk2 (regs3 : bvmap 5 word) (r : word)
    (H2 : reg_get regs3 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (H8 : reg_get regs3 8 = ptrA inp asp) (H13 : reg_get regs3 13 = tnN inp)
    (Hrnz : r ≠ Z_to_bv 64 0) (Hw : bv_unsigned r + (tnn inp : Int) + 1 < 2 ^ 64) :
    ∃ regs5, reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 32) ∧
      reg_get regs5 8 = ptrA inp asp ∧ reg_get regs5 10 = r + (tnN inp + 1) ∧
      reg_get regs5 11 = r ∧ reg_get regs5 12 = tnN inp + 1 ∧
      reg_get regs5 13 = tnN inp ∧ reg_get regs5 14 = Z_to_bv 64 4 ∧
      reg_get regs5 15 = r + (tnN inp + 1) ∧
      msteps target_segs (mkst (regupd regs3 10 r) 0x10011cc (tfmem inp asp arnd) trom)
        { ms_regs := regs5, ms_fregs := bvmap_empty, ms_pc_val := 0x10011ec,
          ms_svc_pending := some (Z_to_bv 64 214), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := tfmem inp asp arnd, ms_rom := trom } := by
  have HnnLe := tnN_le inp Hva Hge2
  have Hur := u64_range r
  have Hur0 := word_neq0_unsigned r Hrnz
  have Hun1 := u_tnN1 inp Hva Hge2
  have Hurn1 : bv_unsigned (r + (tnN inp + 1)) = bv_unsigned r + (tnn inp : Int) + 1 := by
    rw [u_add_small _ _ (by rw [Hun1]; omega), Hun1]; omega
  have Ht1 : Z_to_bv 64 (bv_unsigned (tnN inp) + 1) = tnN inp + 1 := by
    apply bv_eq_of_unsigned
    rw [Hun1, u_Z2bv _ (by rw [u_tnN inp Hva Hge2]; omega)
      (by rw [u_tnN inp Hva Hge2]; omega), u_tnN inp Hva Hge2]
  sym_block_ex target_segs
    (mkst (regupd regs3 10 r) (Z_to_bv 64 0x10011cc) (tfmem inp asp arnd) trom)
    9 [false, false] []
    [((2 : reg), EVar 32), ((8 : reg), EVar 33), ((10 : reg), EVar 34), ((13 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned asp - 32), ptrA inp asp, r, tnN inp] [] R HR Hms
  · constructor
    · rw [Ht1, LinuxProcessSemantics.Common.StepTac.v_add_comm]
      sym_br
    · exact bv_eqb_neq _ _ Hrnz
  · getr_resolve; regupd_resolve; exact H2
  · getr_resolve; regupd_resolve; exact H8
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; exact H13
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sym_regs HR
  · sym_regs HR
  · sym_regs HR
    change v_addi (v_add (Z_to_bv 64 (bv_unsigned (tnN inp) + 1)) r) 0 = _
    rw [v_addi_0, Ht1]
    exact LinuxProcessSemantics.Common.StepTac.v_add_comm _ _
  · sym_regs HR; exact v_addi_0 _
  · sym_regs HR; exact Ht1
  · sym_regs HR
  · sym_regs HR <;> rfl
  · sym_regs HR
    change v_add (Z_to_bv 64 (bv_unsigned (tnN inp) + 1)) r = _
    rw [Ht1]; exact LinuxProcessSemantics.Common.StepTac.v_add_comm _ _
  · sym_chain Hms
    chain_step
    · rfl
    · exact step_ecall _ _ _ _ _ _ TF_10011ec rfl
    have H17 : getr R 17 = Z_to_bv 64 214 := by sym_regs HR <;> rfl
    rw [H17]
    exact msteps.mst_refl _


variable (Hbrk_mod : bv_unsigned abrk % page_size = 0)

include Hva Hve Hsp_lo Hsp_hi Hbrk_lo Hbrk_hi Hge2 Hbrk_mod in
theorem target_outcomes (Hncap : (tnn inp : Int) ≤ 65536) :
    to_outcomes target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (brkU (rev_buf (targ1 inp))) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have Hsms := stack_max_size_val
  have HnnLe := tnN_le inp Hva Hge2
  have Hun1 := u_tnN1 inp Hva Hge2
  have Hblo := abrk_lo_num abrk Hbrk_lo
  have Hbhi := abrk_hi_num abrk Hbrk_hi
  let m0 := init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp
  let h0 := VmMaps.mkVmMapsFull (segments_reserved target_segs) [] [] abrk abrk target_alloc_limit amb asp
  have Hvm : m_vmmaps m0 = h0 := rfl
  obtain ⟨regs3, E2, E8, E10, E13, Hms⟩ :=
    target_to_brk1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2 Hncap
  apply tou_msteps _ _ _ _ _ Hms
  apply tou_brk_r _ _ _ (Z_to_bv 64 214)
    (T1 (segments_reserved target_segs) target_alloc_limit
      (bv_unsigned asp - stack_max_size) (tnN inp + 1) [rev_buf (targ1 inp)])
  · rfl
  · decide
  · intro r Hok
    change brk_resolution_ok m0 (reg_get regs3 10) r at Hok
    rw [E10] at Hok
    change brk_r_ok h0 (Z_to_bv 64 0) r at Hok
    have Heq : r = abrk := (brk_r_ok_query_iff h0 r).mp Hok
    have Hur : bv_unsigned r = bv_unsigned abrk := congrArg bv_unsigned Heq
    have Hrmod : bv_unsigned r % page_size = 0 := by rw [Hur]; exact Hbrk_mod
    have Hrnz : r ≠ Z_to_bv 64 0 := by
      intro Hc
      have H := congrArg bv_unsigned Hc
      change bv_unsigned r = 0 at H
      omega
    have Hnw : bv_unsigned r + (tnn inp : Int) + 1 < 2 ^ 64 := by omega
    have Hurn1 : bv_unsigned (r + (tnN inp + 1)) = bv_unsigned r + (tnn inp : Int) + 1 := by
      rw [u_add_small _ _ (by rw [Hun1]; omega), Hun1]; omega
    have Hwant0 : r + (tnN inp + 1) ≠ Z_to_bv 64 0 := by
      intro He
      have H := congrArg bv_unsigned He
      rw [Hurn1] at H
      change bv_unsigned r + (tnn inp : Int) + 1 = 0 at H
      omega
    have Hne2 : r ≠ r + (tnN inp + 1) := by
      intro He
      have H := congrArg bv_unsigned He
      rw [Hurn1] at H; omega
    change to_outcomes target_segs
      (advance_past_svc (apply_effect _
        (SyscallEffect.mkEffectU r [] (brk_zeros (reg_get regs3 10) r abrk)
          (brk_unmaps r abrk) [] []))) (brk_model (reg_get regs3 10) r m0) _
    rw [E10, brk_zeros_query, brk_unmaps_query h0 r Heq, adv_brk, apply_zeros_nil]
    norm_pc
    rw [brk_model_query r m0 Heq]
    let h1 := VmMaps.mkVmMapsFull (segments_reserved target_segs) [] [] abrk r target_alloc_limit amb asp
    change to_outcomes target_segs (mkst (regupd regs3 10 r) 0x10011cc (tfmem inp asp arnd) trom)
      (with_vmmaps h1 m0) _
    obtain ⟨regs5, F2, F8, F10, F11, F12, F13, F14, F15, Hms2⟩ :=
      target_to_brk2 inp Hva asp arnd Hge2 regs3 r E2 E8 E13 Hrnz Hnw
    apply tou_msteps _ _ _ _ _ Hms2
    apply tou_brk_r _ _ _ (Z_to_bv 64 214) (T2 (r + (tnN inp + 1)) [rev_buf (targ1 inp)])
    · rfl
    · decide
    · intro r2 Hok2
      change brk_resolution_ok (with_vmmaps h1 m0) (reg_get regs5 10) r2 at Hok2
      rw [F10] at Hok2
      change brk_r_ok h1 (r + (tnN inp + 1)) r2 at Hok2
      have Hgrow := (brk_r_ok_grow_iff (segments_reserved target_segs) target_alloc_limit abrk r
        [] [] amb asp (r + (tnN inp + 1)) r2 (by rw [Hurn1]; omega)
        (by rw [Hurn1]; omega) (by rw [Hurn1]; omega)).mp Hok2
      change to_outcomes target_segs
        (advance_past_svc (apply_effect _
          (SyscallEffect.mkEffectU r2 [] (brk_zeros (reg_get regs5 10) r2 r)
            (brk_unmaps r2 r) [] []))) (brk_model (reg_get regs5 10) r2 (with_vmmaps h1 m0)) _
      rw [F10]
      by_cases He2 : r2 = r + (tnN inp + 1)
      · subst r2
        have Hgrow2 := Hgrow.2
        rw [brk_grow_ok_aligned_grow h1 _ _ Hwant0 (by change 0 < bv_unsigned r; omega)
          (by change bv_unsigned r < _; rw [Hurn1]; omega) Hrmod] at Hgrow2
        change ((decide (page_round_up_Z (bv_unsigned (r + (tnN inp + 1))) ≤ bv_unsigned asp - stack_max_size) &&
          region_free (segments_reserved target_segs ++ []) r
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + (tnN inp + 1))) + page_size - bv_unsigned r))) &&
          _) = true at Hgrow2
        rw [List.append_nil] at Hgrow2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at Hgrow2
        obtain ⟨⟨Hle', Hfree⟩, _Hbud⟩ := Hgrow2
        let grant := Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + (tnN inp + 1))) - bv_unsigned r)
        obtain ⟨_HgrantU, Hgrant, Hphysceil, Hrawceil, Hrawfree, _⟩ :=
          brk_aligned_grant_ok (segments_reserved target_segs) r (tnN inp + 1) grant
            (bv_unsigned r + (tnn inp : Int) + 1) (bv_unsigned asp - stack_max_size)
            (u_add_small _ _ (by rw [Hun1]; omega)) Hurn1 rfl (alloc_top_page_lt h1) Hle' Hfree
        rw [brk_zeros_aligned_grow _ _ _ Hwant0 (by omega) (by rw [Hurn1]; omega) Hrmod,
          brk_unmaps_grow _ _ (by rw [Hurn1]; omega), adv_brk, apply_zeros_one]
        norm_pc
        apply tou_equiv
        · apply tou_wexit_eq (bufs := [rev_buf (targ1 inp)]) (code := Z_to_bv 64 0)
          · apply fd1chan_brk_model
            apply fd1chan_with_vmmaps
            exact init_model_fd1chan _ _ _ _ _ _
          · apply target_success inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge2 _ r grant
              Hgrant Hphysceil (by omega) Hrawceil Hrawfree
            · regupd_resolve; exact F2
            · regupd_resolve; exact F8
            · regupd_resolve; rfl
            · regupd_resolve; exact F11
            · regupd_resolve; exact F12
            · regupd_resolve; exact F13
            · regupd_resolve; exact F15
          · exact tbufs_modeled inp Hva Hge2
        · intro o
          exact T2_succ_iff _ _ o
      · have Hr2 : r2 = r := Hgrow.1.resolve_left He2
        subst r2
        rw [brk_zeros_keep, brk_unmaps_grow _ _ (by omega), adv_brk, apply_zeros_nil]
        norm_pc
        apply tou_equiv
        · apply tou_wexit_eq (bufs := []) (code := Z_to_bv 64 4)
          · apply fd1chan_brk_model
            apply fd1chan_with_vmmaps
            exact init_model_fd1chan _ _ _ _ _ _
          · chain_step
            · rfl
            · apply step_bne_tk (hf := TF_10011f0) (he := rfl) (hd := TD_10011f0)
              getr_resolve; regupd_resolve; rw [F15]
              apply c_eq_neq
              rw [Hurn1]; omega
            norm_pc
            apply target_exit asp Hsp_lo Hsp_hi
            · regupd_resolve; exact F2
            · regupd_resolve; exact F14
            · decide
            · exact read_slot_ra_t inp asp arnd Hsp_lo Hsp_hi
            · exact read_slot_s0_t inp asp arnd Hsp_lo Hsp_hi
          · intro b hb; cases hb
        · intro o
          exact T2_fail_iff _ _ _ Hne2 o
    · intro o
      change T1 _ _ _ _ _ _ o ↔ ∃ r2, brk_resolution_ok (with_vmmaps h1 m0) (reg_get regs5 10) r2 ∧ _
      rw [F10]
      change T1 _ _ _ _ _ _ o ↔ ∃ r2, brk_r_ok h1 (r + (tnN inp + 1)) r2 ∧ _
      exact LinuxProcessSemantics.Common.AllocSim.T1_iff_T2 (segments_reserved target_segs) target_alloc_limit abrk amb asp
        (tnN inp + 1) [rev_buf (targ1 inp)] r Hrnz (by omega)
        (by rw [Hun1]; omega) o
  · intro o
    change brkU _ o ↔ ∃ r, brk_resolution_ok m0 (reg_get regs3 10) r ∧ _
    rw [E10]
    change brkU _ o ↔ ∃ r, brk_r_ok h0 (Z_to_bv 64 0) r ∧ _
    apply brkU_iff_T1 (segments_reserved target_segs) target_alloc_limit
      (bv_unsigned asp - stack_max_size) (tnN inp) (rev_buf (targ1 inp)) abrk
    · intro r0
      exact brk_r_ok_query_iff h0 r0
    · refine ⟨?_, ?_, Or.inr ?_⟩
      · intro Hc
        have H := congrArg bv_unsigned Hc
        change bv_unsigned abrk = 0 at H
        omega
      · rw [Hun1]; omega
      · apply growable_aligned_grow _ _ _ _ _ Hbrk_mod Hbrk_lo
        · rw [Hun1]; omega
        · rw [Hun1]; change bv_unsigned abrk + ((tnn inp : Int) + 1) + 4096 - 1 ≤ _; omega
        · rw [Hun1]; change (tnn inp : Int) + 1 ≤ 0x8000000000; omega
    · intro Hc
      have H := congrArg bv_unsigned Hc
      rw [Hun1] at H
      change (tnn inp : Int) + 1 = 0 at H
      omega


end Ge2MainT
end TargetProof

end LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_target
