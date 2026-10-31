import LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_defs
import LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_code
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Common.SymTac

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
-/

/-! Proof-side twin of `theories/Examples/arena_tee_ns/arena_tee_ns_target.v`.
The target allocates its arena, drains input, writes the eight-byte hexadecimal
header, and retries partial writes on channel 2. Section parameters follow
Rocq order. The digit proof is split into continuation and final-iteration
helpers to keep the reflective blocks in separate elaboration units.
-/

namespace LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Run.config
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.Common.ShapeAlg.realizes
open LinuxProcessSemantics.Common.DrainAlg
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.DrainSim
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymSide
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Examples.arena_tee_ns.TargetMemImage
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_code
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem target_reserved_val : segments_reserved target_segs =
    [(Z_to_bv 64 0x1000000, Z_to_bv 64 0x1000),
     (Z_to_bv 64 0x1001000, Z_to_bv 64 0x1000)] := by decide

theorem target_grant_witness (inp : ProcInput) (hint brk0 mb sp : word)
    (hsp : sp_window_lo ≤ bv_unsigned sp) :
    grant_ok hint (init_model (segments_reserved target_segs) brk0 mb sp target_alloc_limit inp)
      (Z_to_bv 64 0x2aaaaab000) 4096 = true := by
  rw [target_reserved_val]
  unfold grant_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨by decide, by decide⟩, ?_⟩, ?_⟩, ?_⟩
  · change 0x2aaaaac000 ≤ bv_unsigned sp - stack_max_size
    unfold sp_window_lo at hsp
    unfold stack_max_size
    omega
  · change region_free [(Z_to_bv 64 0x1000000, Z_to_bv 64 4096),
      (Z_to_bv 64 0x1001000, Z_to_bv 64 4096)] (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 4096) = true
    decide
  · change 4096 ≤ target_alloc_limit
    decide

theorem target_grant_unpack (inp : ProcInput) (hint brk0 mb sp aG : word)
    (hg : grant_ok hint (init_model (segments_reserved target_segs) brk0 mb sp target_alloc_limit inp)
      aG 4096 = true) :
    0 < bv_unsigned aG ∧ bv_unsigned aG % page_size = 0 ∧
    bv_unsigned aG + 4096 ≤ bv_unsigned sp - stack_max_size ∧
    (bv_unsigned aG + 4096 ≤ 0x1000000 ∨ 0x1001000 ≤ bv_unsigned aG) ∧
    (bv_unsigned aG + 4096 ≤ 0x1001000 ∨ 0x1002000 ≤ bv_unsigned aG) := by
  obtain ⟨hal, hpos, hceil, hfree, _⟩ := grant_ok_unpack _ _ _ _ hg
  change region_free (segments_reserved target_segs ++ []) aG (Z_to_bv 64 4096) = true at hfree
  rw [List.append_nil, target_reserved_val] at hfree
  obtain ⟨hda, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨hdb, _⟩ := region_free_cons _ _ _ _ _ hfree
  change bv_unsigned aG + 4096 ≤ 0x1000000 ∨ 0x1001000 ≤ bv_unsigned aG at hda
  change bv_unsigned aG + 4096 ≤ 0x1001000 ∨ 0x1002000 ≤ bv_unsigned aG at hdb
  exact ⟨hpos, hal, hceil, hda, hdb⟩

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001158 := rfl

theorem v_srl_3 (x : word) : v_srl x (Z_to_bv 64 3) = v_srli x 3 := rfl

theorem v_and_15 (x : word) : v_and x (Z_to_bv 64 15) = v_andi x 15 := rfl

theorem dig_byte_lo (n k' : Nat) (Hn : n ≤ cap) (Hk' : k' ≤ 7)
    (Hd : nib n k' < 10) :
    word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned
      (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * (k' : Int))))
        (Z_to_bv 64 15)) + 48)) = [hex_digit (nib n k')] := by
  rw [v_and_15, dig_val n k' _ Hn Hk' rfl]
  have H := nib_lt16 n k'
  rw [u_Z2bv _ (by omega) (by omega)]
  have Hv : (nib n k' : Int) + 48 = digZ n k' := by
    simp only [digZ, ite_eq_left Hd]; omega
  rw [Hv, N_to_le_bytes_1_small, digb]

theorem dig_byte_hi (n k' : Nat) (Hn : n ≤ cap) (Hk' : k' ≤ 7)
    (Hd : 10 ≤ nib n k') :
    word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned
      (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * (k' : Int))))
        (Z_to_bv 64 15)) + 87)) = [hex_digit (nib n k')] := by
  rw [v_and_15, dig_val n k' _ Hn Hk' rfl]
  have H := nib_lt16 n k'
  rw [u_Z2bv _ (by omega) (by omega)]
  have Hv : (nib n k' : Int) + 87 = digZ n k' := by
    simp only [digZ, ite_eq_right (show ¬ nib n k' < 10 by omega)]; omega
  rw [Hv, N_to_le_bytes_1_small, digb]

def tgbounds (sp aG : word) : Prop :=
  0 < bv_unsigned aG ∧ bv_unsigned aG % page_size = 0 ∧
  bv_unsigned aG + 4096 ≤ bv_unsigned sp - stack_max_size ∧
  (bv_unsigned aG + 4096 ≤ 0x1000000 ∨ 0x1001000 ≤ bv_unsigned aG) ∧
  (bv_unsigned aG + 4096 ≤ 0x1001000 ∨ 0x1002000 ≤ bv_unsigned aG)

def tbufA (aG : word) (k : Nat) : word := Z_to_bv 64 (bv_unsigned aG + 8 + (k : Int))

theorem tbufA_split (sp aG : word) (k : Nat) (Hb : tgbounds sp aG) (_Hk : k ≤ cap) :
    Z_to_bv 64 (bv_unsigned aG + 8) + nat_to_word k = tbufA aG k := by
  obtain ⟨_, _, Hc, _⟩ := Hb
  have Ha := u64_range aG
  have Hsp := u64_range sp
  unfold stack_max_size at Hc
  rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]
  rfl

theorem tbufA_calc (sp aG : word) (k : Nat) (Hb : tgbounds sp aG) (Hk : k ≤ cap) :
    Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned aG + 8)) +
      bv_unsigned (nat_to_word k)) = tbufA aG k := by
  obtain ⟨_, _, Hc, _⟩ := Hb
  have Ha := u64_range aG
  have Hsp := u64_range sp
  unfold stack_max_size at Hc
  rw [u_Z2bv _ (by omega) (by omega), u_ntw k (by unfold cap at Hk; omega)]
  rfl

theorem tdcnt (k : Nat) (Hk : k ≤ cap) :
    Z_to_bv 64 (bv_unsigned (Z_to_bv 64 4088) - bv_unsigned (nat_to_word k)) =
      Z_to_bv 64 (cap - k : Nat) := by
  rw [u_Z2bv _ (by omega) (by omega), u_ntw k (by unfold cap at Hk; omega)]
  congr 1
  unfold cap at *
  omega

theorem tntw_add (k : Nat) (bs : List byte) (H : k + bs.length ≤ cap) :
    Z_to_bv 64 (bv_unsigned (len_word bs) + bv_unsigned (nat_to_word k)) =
      nat_to_word (k + bs.length) := by
  unfold cap at H
  rw [u_len_word bs (by omega), u_ntw k (by omega)]
  unfold nat_to_word
  congr 1
  omega

section TargetProof
variable (inp : ProcInput) (Hva : valid_argv inp.in_argv) (Hve : valid_envp inp.in_envp)
variable (asp : word) (arnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
variable (abrk amb : word)

include Hsp_lo in
theorem asp_lo_num : 0x7fff80000000 ≤ bv_unsigned asp := Hsp_lo
include Hsp_hi in
theorem asp_hi_num : bv_unsigned asp ≤ 0x800000000000 := Hsp_hi

def twmem : word → Option byte :=
  wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd
def trom : word → Option byte := seg_rom target_segs

def tfmem : word → Option byte :=
  wbytes (twmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 8))
    (word_to_le_bytes 8 (Z_to_bv 64 0))

def tgmem (aG : word) : word → Option byte := zfill aG (Z_to_bv 64 4096) (tfmem inp asp arnd)
def tmem_ok (aG : word) (mem : word → Option byte) : Prop := mem_grows (tgmem inp asp arnd aG) mem

theorem tmem_ok_grows_w (aG : word) (mem : word → Option byte)
    (Hg : tmem_ok inp asp arnd aG mem) : mem_grows (twmem inp asp arnd) mem := by
  apply mem_grows_trans _ _ _ _ Hg
  unfold tgmem zfill tfmem
  solve_mem_grows

theorem tgrant_below_stack (aG : word) (Hb : tgbounds asp aG) :
    bv_unsigned aG + 4096 ≤ bv_unsigned asp - 0x800000 := Hb.2.2.1

include Hsp_hi in
theorem tgrant_store_ok (aG : word) (mem : word → Option byte) (a : word) (k : Nat)
    (Hg : tmem_ok inp asp arnd aG mem) (Hb : tgbounds asp aG)
    (Hlo : bv_unsigned aG ≤ bv_unsigned a)
    (Hhi : bv_unsigned a + (k : Int) ≤ bv_unsigned aG + 4096) :
    store_ok target_segs mem a k = true := by
  have Hceil := tgrant_below_stack asp aG Hb
  have Hsp := asp_hi_num asp Hsp_hi
  apply store_ok_mono _ _ _ _ _ Hg
  unfold tgmem zfill
  apply store_ok_zmem
  · omega
  · exact Hlo
  · exact Hhi

theorem tmem_ok_grant (aG : word) (mem : word → Option byte) (a : word) (bs : List byte)
    (Hg : tmem_ok inp asp arnd aG mem) : tmem_ok inp asp arnd aG (wbytes mem a bs) := by
  unfold tmem_ok at *
  solve_mem_grows

theorem tmem_ok_buf (aG : word) (mem : word → Option byte) (buf : word) (bs : List byte)
    (Hg : tmem_ok inp asp arnd aG mem) : tmem_ok inp asp arnd aG (write_to_mem mem buf bs) := by
  unfold tmem_ok at *
  solve_mem_grows

def tgt_mmap_ms (regs : bvmap 5 word) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := 0x1001190,
    ms_svc_pending := some (getr regs 17), ms_resv := none,
    ms_fcsr := Z_to_bv 32 0, ms_mem := tfmem inp asp arnd, ms_rom := trom }

include Hsp_lo Hsp_hi in
theorem tgt_to_mmap :
    ∃ regs,
      getr regs 1 = (0x1001168 : word) ∧
      getr regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x10) ∧
      getr regs 5 = Z_to_bv 64 4096 ∧
      getr regs 11 = Z_to_bv 64 4096 ∧
      getr regs 12 = Z_to_bv 64 3 ∧
      getr regs 13 = Z_to_bv 64 34 ∧
      getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1) ∧
      getr regs 15 = Z_to_bv 64 0 ∧
      bv_unsigned (getr regs 17) = 222 ∧
      msteps target_segs
        (init_machine_state target_segs TargetMemImage_init_pc target_phdrs
          asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (tgt_mmap_ms inp asp arnd regs) := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  have hsms := stack_max_size_val
  rw [target_init_pc_val, init_mkst]
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
      (Z_to_bv 64 0x1001158)
      (wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd)
      (seg_rom target_segs))
    20 [] [] [(1, ELit 0), (2, EVar 32)] [asp] [] RA HRA Hms
  · repeat' apply And.intro
    all_goals first | omega | solve_store_ok
  · getr_resolve; rfl
  · getr_resolve; rfl
  · refine ⟨RA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_regs HRA; sym_close
    · sym_regs HRA; sym_close
    · sym_regs HRA; sym_close
    · sym_regs HRA; sym_close
    · sym_regs HRA; sym_close
    · sym_regs HRA; sym_close
    · sym_regs HRA; sym_close
    · sym_regs HRA; sym_close
    · sym_regs HRA; rfl
    · unfold tgt_mmap_ms
      apply msteps_trans _ _ _ _ Hms
      norm_pc; sym_pc_lit
      exact msteps.mst_step _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_1001190 (by decide)) (msteps.mst_refl _)

theorem tgt_fail_wexit (regs : bvmap 5 word) (e : Int) (He1 : 1 ≤ e) (He2 : e ≤ 4095)
    (Hr1 : getr regs 1 = (0x1001168 : word)) :
    to_wexit target_segs
      (advance_past_svc (set_gpr0 (tgt_mmap_ms inp asp arnd regs) (errno_ret e)))
      [] (Z_to_bv 64 1) := by
  obtain ⟨Her1, Her2⟩ := errno_ret_range e He1 He2
  unfold tgt_mmap_ms
  rw [adv_set]
  norm_pc
  sym_block target_segs 4 [true] []
    [(1, ELit 0x1001168), (10, EVar 32)] [errno_ret e] [] RA HRA
  · apply c_lts_neg_0; omega
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide), Hr1]; rfl
  · getr_resolve; regupd_resolve; rfl
  · apply to_wexit.tw_step _ _ _ _ rfl
      (step_ecall _ _ _ _ _ _ TF_100116c (by decide))
    apply tw_exit_coden
    · sym_regs HRA; rfl
    · sym_regs HRA; rfl
    · decide

def tgt_LH (fs0 : Fs.Fs) (acc : List byte) (c : config) : Prop :=
  ∃ (aG : word) (regs : bvmap 5 word) (mem : word → Option byte),
    tgbounds asp aG ∧ m_halted (cfg_model c) = none ∧ m_vm_lazy (cfg_model c) = [] ∧
    m_fs (cfg_model c) = fs0 ∧
    fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)) ∧
    fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (cfg_model c) ∧
    msteps target_segs (cfg_ms c) (mkst regs 0x10011b0 mem trom) ∧
    getr regs 1 = (0x1001168 : word) ∧ getr regs 5 = Z_to_bv 64 4088 ∧
    getr regs 11 = nat_to_word acc.length ∧ getr regs 13 = aG ∧
    getr regs 15 = Z_to_bv 64 (bv_unsigned aG + 8) ∧
    getr regs 16 = Z_to_bv 64 510 ∧ getr regs 17 = Z_to_bv 64 63 ∧
    acc.length ≤ cap ∧ tmem_ok inp asp arnd aG mem ∧
    rdn target_segs mem (Z_to_bv 64 (bv_unsigned aG + 8)) acc.length = some acc

def tgt_TH (fs0 : Fs.Fs) (acc : List byte) (c : config) : Prop :=
  ∃ (aG : word) (regs : bvmap 5 word) (mem : word → Option byte),
    tgbounds asp aG ∧ m_halted (cfg_model c) = none ∧ m_vm_lazy (cfg_model c) = [] ∧
    m_fs (cfg_model c) = fs0 ∧
    fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (cfg_model c) ∧
    msteps target_segs (cfg_ms c) (mkst regs 0x10011d8 mem trom) ∧
    getr regs 1 = (0x1001168 : word) ∧ getr regs 13 = aG ∧
    getr regs 14 = nat_to_word acc.length ∧ acc.length ≤ cap ∧
    tmem_ok inp asp arnd aG mem ∧
    rdn target_segs mem (Z_to_bv 64 (bv_unsigned aG + 8)) acc.length = some acc

theorem c_eq_sub_self (x : word) : bv_eqb (v_sub x x) (Z_to_bv 64 0) = true := by
  unfold v_sub
  rw [Int.sub_self]
  rfl

theorem word_to_nat_ntw (n : Nat) (Hn : (n : Int) < 2 ^ 64) :
    word_to_nat (nat_to_word n) = n := by
  have H := u_ntw n Hn
  change (word_to_nat (nat_to_word n) : Int) = (n : Int) at H
  omega

include Hsp_hi in
theorem arena_tee_tgt_dig_more (aG : word) (R : bvmap 5 word) (mem : word → Option byte) (n k : Nat)
    (Hb : tgbounds asp aG) (Hn : n ≤ cap) (Hk : k < 8) (Hmok : tmem_ok inp asp arnd aG mem)
    (L1 : getr R 1 = (0x1001168 : word))
    (L10 : getr R 10 = Z_to_bv 64 (4 * (7 - k : Nat)))
    (L11 : getr R 11 = Z_to_bv 64 (2 ^ 64 - 4))
    (L12 : getr R 12 = Z_to_bv 64 10) (L13 : getr R 13 = aG)
    (L14 : getr R 14 = nat_to_word n) (L15 : getr R 15 = aG + nat_to_word k)
    (HSk : k + 1 < 8) :
    ∃ R', getr R' 1 = (0x1001168 : word) ∧
      (k + 1 < 8 → getr R' 10 = Z_to_bv 64 (4 * (7 - (k + 1) : Nat))) ∧
      getr R' 11 = Z_to_bv 64 (2 ^ 64 - 4) ∧ getr R' 12 = Z_to_bv 64 10 ∧
      getr R' 13 = aG ∧ getr R' 14 = nat_to_word n ∧
      getr R' 15 = aG + nat_to_word (k + 1) ∧
      msteps target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 8 then 0x10011ec else 0x1001214))
          (wbytes mem (aG + nat_to_word k) [hex_digit (nib n (7 - k))]) trom) := by
  have Hceil := tgrant_below_stack asp aG Hb
  have Hsp := asp_hi_num asp Hsp_hi
  have Ha := u64_range aG
  have Hso : store_ok target_segs mem (aG + nat_to_word k) 1 = true := by
    apply tgrant_store_ok inp asp arnd Hsp_hi aG mem _ _ Hmok Hb
    · rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]; omega
    · rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]; omega
  have Har := u64_range (aG + nat_to_word k)
  have Hnib := nib_lt16 n (7 - k)
  by_cases Hd : nib n (7 - k) < 10
  · sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
      8 [true, true] []
      [(1, ELit 0x1001168), (10, EVar 32), (11, EVar 33), (12, ELit 10),
       (13, EVar 34), (14, EVar 35), (15, EVar 36)]
      [Z_to_bv 64 (4 * (7 - k : Nat)), Z_to_bv 64 (2 ^ 64 - 4), aG,
       nat_to_word n, aG + nat_to_word k] [] R' HR' Hms
    · repeat' apply And.intro
      all_goals first
        | (rw [show Z_to_bv 64 (bv_unsigned (aG + nat_to_word k) + 0) = aG + nat_to_word k from v_addi_0 _]; exact Hso)
        | (rw [v_and_15, dig_val n (7 - k) _ Hn (by omega) rfl, bv_ltu_Z]
           u_norm; simp only [decide_eq_true_eq]; omega)
        | (simp only [Bool.not_eq_true', bv_eqb_Z, decide_eq_false_iff_not]
           u_norm; omega)
        | sym_br
        | decide
        | omega
    · rw [L1]; rfl
    · exact L10
    · exact L11
    · exact L12
    · exact L13
    · exact L14
    · exact L15
    · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sym_regs HR' <;> rfl
      · intro h; sym_regs HR'; congr 1; omega
      · sym_regs HR' <;> rfl
      · sym_regs HR' <;> rfl
      · sym_regs HR'
      · sym_regs HR'
      · sym_regs HR'; exact word_add_nat_1 aG k
      · simp only [ite_eq_left HSk]
        revert Hms
        sym_mem_norm
        intro Hms
        rw [dig_byte_lo n (7 - k) Hn (by omega) Hd] at Hms
        simp only [← v_addi_Z, v_addi_0] at Hms
        exact Hms
  · sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
      9 [false, true] []
      [(1, ELit 0x1001168), (10, EVar 32), (11, EVar 33), (12, ELit 10),
       (13, EVar 34), (14, EVar 35), (15, EVar 36)]
      [Z_to_bv 64 (4 * (7 - k : Nat)), Z_to_bv 64 (2 ^ 64 - 4), aG,
       nat_to_word n, aG + nat_to_word k] [] R' HR' Hms
    · repeat' apply And.intro
      all_goals first
        | (rw [show Z_to_bv 64 (bv_unsigned (aG + nat_to_word k) + 0) = aG + nat_to_word k from v_addi_0 _]; exact Hso)
        | (rw [v_and_15, dig_val n (7 - k) _ Hn (by omega) rfl, bv_ltu_Z]
           u_norm; simp only [decide_eq_false_iff_not]; omega)
        | (simp only [Bool.not_eq_true', bv_eqb_Z, decide_eq_false_iff_not]
           u_norm; omega)
        | sym_br
        | decide
        | omega
    · rw [L1]; rfl
    · exact L10
    · exact L11
    · exact L12
    · exact L13
    · exact L14
    · exact L15
    · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sym_regs HR' <;> rfl
      · intro h; sym_regs HR'; congr 1; omega
      · sym_regs HR' <;> rfl
      · sym_regs HR' <;> rfl
      · sym_regs HR'
      · sym_regs HR'
      · sym_regs HR'; exact word_add_nat_1 aG k
      · simp only [ite_eq_left HSk]
        revert Hms
        sym_mem_norm
        intro Hms
        rw [dig_byte_hi n (7 - k) Hn (by omega) (by omega)] at Hms
        simp only [← v_addi_Z, v_addi_0] at Hms
        exact Hms

include Hsp_hi in
theorem arena_tee_tgt_dig_last (aG : word) (R : bvmap 5 word) (mem : word → Option byte) (n k : Nat)
    (Hb : tgbounds asp aG) (Hn : n ≤ cap) (Hk : k < 8) (Hmok : tmem_ok inp asp arnd aG mem)
    (L1 : getr R 1 = (0x1001168 : word))
    (L10 : getr R 10 = Z_to_bv 64 (4 * (7 - k : Nat)))
    (L11 : getr R 11 = Z_to_bv 64 (2 ^ 64 - 4))
    (L12 : getr R 12 = Z_to_bv 64 10) (L13 : getr R 13 = aG)
    (L14 : getr R 14 = nat_to_word n) (L15 : getr R 15 = aG + nat_to_word k)
    (HSk : ¬ k + 1 < 8) :
    ∃ R', getr R' 1 = (0x1001168 : word) ∧
      (k + 1 < 8 → getr R' 10 = Z_to_bv 64 (4 * (7 - (k + 1) : Nat))) ∧
      getr R' 11 = Z_to_bv 64 (2 ^ 64 - 4) ∧ getr R' 12 = Z_to_bv 64 10 ∧
      getr R' 13 = aG ∧ getr R' 14 = nat_to_word n ∧
      getr R' 15 = aG + nat_to_word (k + 1) ∧
      msteps target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 8 then 0x10011ec else 0x1001214))
          (wbytes mem (aG + nat_to_word k) [hex_digit (nib n (7 - k))]) trom) := by
  have Hceil := tgrant_below_stack asp aG Hb
  have Hsp := asp_hi_num asp Hsp_hi
  have Ha := u64_range aG
  have Hso : store_ok target_segs mem (aG + nat_to_word k) 1 = true := by
    apply tgrant_store_ok inp asp arnd Hsp_hi aG mem _ _ Hmok Hb
    · rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]; omega
    · rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]; omega
  have Har := u64_range (aG + nat_to_word k)
  have Hnib := nib_lt16 n (7 - k)
  have hk7 : k = 7 := by omega
  subst k
  by_cases Hd : nib n (7 - 7) < 10
  · sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
      8 [true, false] []
      [(1, ELit 0x1001168), (10, EVar 32), (11, EVar 33), (12, ELit 10),
       (13, EVar 34), (14, EVar 35), (15, EVar 36)]
      [Z_to_bv 64 (4 * (7 - 7 : Nat)), Z_to_bv 64 (2 ^ 64 - 4), aG,
       nat_to_word n, aG + nat_to_word 7] [] R' HR' Hms
    · repeat' apply And.intro
      all_goals first
        | (rw [show Z_to_bv 64 (bv_unsigned (aG + nat_to_word 7) + 0) = aG + nat_to_word 7 from v_addi_0 _]; exact Hso)
        | (rw [v_and_15, dig_val n (7 - 7) _ Hn (by omega) rfl, bv_ltu_Z]
           u_norm; simp only [decide_eq_true_eq]; omega)
        | (simp only [bv_eqb_Z]
           u_norm; omega)
        | sym_br
        | decide
        | omega
    · rw [L1]; rfl
    · exact L10
    · exact L11
    · exact L12
    · exact L13
    · exact L14
    · exact L15
    · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sym_regs HR' <;> rfl
      · intro h; omega
      · sym_regs HR' <;> rfl
      · sym_regs HR' <;> rfl
      · sym_regs HR'
      · sym_regs HR'
      · sym_regs HR'; exact word_add_nat_1 aG 7
      · try simp only [ite_eq_right (by omega)]
        revert Hms
        sym_mem_norm
        intro Hms
        rw [dig_byte_lo n (7 - 7) Hn (by omega) Hd] at Hms
        simp only [← v_addi_Z, v_addi_0] at Hms
        exact Hms
  · sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
      9 [false, false] []
      [(1, ELit 0x1001168), (10, EVar 32), (11, EVar 33), (12, ELit 10),
       (13, EVar 34), (14, EVar 35), (15, EVar 36)]
      [Z_to_bv 64 (4 * (7 - 7 : Nat)), Z_to_bv 64 (2 ^ 64 - 4), aG,
       nat_to_word n, aG + nat_to_word 7] [] R' HR' Hms
    · repeat' apply And.intro
      all_goals first
        | (rw [show Z_to_bv 64 (bv_unsigned (aG + nat_to_word 7) + 0) = aG + nat_to_word 7 from v_addi_0 _]; exact Hso)
        | (rw [v_and_15, dig_val n (7 - 7) _ Hn (by omega) rfl, bv_ltu_Z]
           u_norm; simp only [decide_eq_false_iff_not]; omega)
        | (simp only [bv_eqb_Z]
           u_norm; omega)
        | sym_br
        | decide
        | omega
    · rw [L1]; rfl
    · exact L10
    · exact L11
    · exact L12
    · exact L13
    · exact L14
    · exact L15
    · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sym_regs HR' <;> rfl
      · intro h; omega
      · sym_regs HR' <;> rfl
      · sym_regs HR' <;> rfl
      · sym_regs HR'
      · sym_regs HR'
      · sym_regs HR'; exact word_add_nat_1 aG 7
      · try simp only [ite_eq_right (by omega)]
        revert Hms
        sym_mem_norm
        intro Hms
        rw [dig_byte_hi n (7 - 7) Hn (by omega) (by omega)] at Hms
        simp only [← v_addi_Z, v_addi_0] at Hms
        exact Hms

include Hsp_hi in
theorem tgt_dig_iter (aG : word) (R : bvmap 5 word) (mem : word → Option byte) (n k : Nat)
    (Hb : tgbounds asp aG) (Hn : n ≤ cap) (Hk : k < 8) (Hmok : tmem_ok inp asp arnd aG mem)
    (L1 : getr R 1 = (0x1001168 : word))
    (L10 : getr R 10 = Z_to_bv 64 (4 * (7 - k : Nat)))
    (L11 : getr R 11 = Z_to_bv 64 (2 ^ 64 - 4))
    (L12 : getr R 12 = Z_to_bv 64 10) (L13 : getr R 13 = aG)
    (L14 : getr R 14 = nat_to_word n) (L15 : getr R 15 = aG + nat_to_word k) :
    ∃ R', getr R' 1 = (0x1001168 : word) ∧
      (k + 1 < 8 → getr R' 10 = Z_to_bv 64 (4 * (7 - (k + 1) : Nat))) ∧
      getr R' 11 = Z_to_bv 64 (2 ^ 64 - 4) ∧ getr R' 12 = Z_to_bv 64 10 ∧
      getr R' 13 = aG ∧ getr R' 14 = nat_to_word n ∧
      getr R' 15 = aG + nat_to_word (k + 1) ∧
      msteps target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 8 then 0x10011ec else 0x1001214))
          (wbytes mem (aG + nat_to_word k) [hex_digit (nib n (7 - k))]) trom) := by
  by_cases HSk : k + 1 < 8
  · exact arena_tee_tgt_dig_more inp asp arnd Hsp_hi aG R mem n k
      Hb Hn Hk Hmok L1 L10 L11 L12 L13 L14 L15 HSk
  · exact arena_tee_tgt_dig_last inp asp arnd Hsp_hi aG R mem n k
      Hb Hn Hk Hmok L1 L10 L11 L12 L13 L14 L15 HSk

include Hsp_hi in
theorem tgt_hdr_run (aG : word) (regs : bvmap 5 word) (mem : word → Option byte) (n : Nat)
    (Hb : tgbounds asp aG) (Hn : n ≤ cap) (Hmok : tmem_ok inp asp arnd aG mem)
    (H1 : getr regs 1 = (0x1001168 : word)) (H13 : getr regs 13 = aG)
    (H14 : getr regs 14 = nat_to_word n) :
    ∃ R, getr R 1 = (0x1001168 : word) ∧ getr R 13 = aG ∧ getr R 14 = nat_to_word n ∧
      msteps target_segs (mkst regs (Z_to_bv 64 0x10011d8) mem trom)
        (mkst R (Z_to_bv 64 0x1001214) (wbytes mem aG (hdr8 n)) trom) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x10011d8) mem trom)
    5 [false] [] [(1, ELit 0x1001168), (13, EVar 32), (14, EVar 33)]
    [aG, nat_to_word n] [] R0 HR0 Hms0
  · decide
  · rw [H1]; rfl
  · exact H13
  · exact H14
  · have L1 : getr R0 1 = (0x1001168 : word) := by sym_regs HR0 <;> rfl
    have L10 : getr R0 10 = Z_to_bv 64 (4 * (7 - 0 : Nat)) := by sym_regs HR0 <;> rfl
    have L11 : getr R0 11 = Z_to_bv 64 (2 ^ 64 - 4) := by sym_regs HR0 <;> rfl
    have L12 : getr R0 12 = Z_to_bv 64 10 := by sym_regs HR0 <;> rfl
    have L13 : getr R0 13 = aG := by sym_regs HR0
    have L14 : getr R0 14 = nat_to_word n := by sym_regs HR0
    have L15 : getr R0 15 = aG + nat_to_word 0 := by sym_regs HR0; rw [word_add_nat_0]; exact v_addi_0 _
    clear HR0
    obtain ⟨Ra, A1, A10, A11, A12, A13, A14, A15, HmsA⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG R0 mem n 0 Hb Hn (by omega) Hmok
        L1 L10 L11 L12 L13 L14 L15
    let m1 := wbytes mem (aG + nat_to_word 0) [hex_digit (nib n (7 - 0))]
    have Hmok1 : tmem_ok inp asp arnd aG m1 :=
      tmem_ok_grant inp asp arnd aG mem _ _ Hmok
    obtain ⟨Rb, B1, B10, B11, B12, B13, B14, B15, HmsB⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG Ra m1 n 1 Hb Hn (by omega) Hmok1
        A1 (A10 (by omega)) A11 A12 A13 A14 A15
    let m2 := wbytes m1 (aG + nat_to_word 1) [hex_digit (nib n (7 - 1))]
    have Hmok2 : tmem_ok inp asp arnd aG m2 :=
      tmem_ok_grant inp asp arnd aG m1 _ _ Hmok1
    obtain ⟨Rc, C1, C10, C11, C12, C13, C14, C15, HmsC⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG Rb m2 n 2 Hb Hn (by omega) Hmok2
        B1 (B10 (by omega)) B11 B12 B13 B14 B15
    let m3 := wbytes m2 (aG + nat_to_word 2) [hex_digit (nib n (7 - 2))]
    have Hmok3 : tmem_ok inp asp arnd aG m3 :=
      tmem_ok_grant inp asp arnd aG m2 _ _ Hmok2
    obtain ⟨Rd, D1, D10, D11, D12, D13, D14, D15, HmsD⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG Rc m3 n 3 Hb Hn (by omega) Hmok3
        C1 (C10 (by omega)) C11 C12 C13 C14 C15
    let m4 := wbytes m3 (aG + nat_to_word 3) [hex_digit (nib n (7 - 3))]
    have Hmok4 : tmem_ok inp asp arnd aG m4 :=
      tmem_ok_grant inp asp arnd aG m3 _ _ Hmok3
    obtain ⟨Re, E1, E10, E11, E12, E13, E14, E15, HmsE⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG Rd m4 n 4 Hb Hn (by omega) Hmok4
        D1 (D10 (by omega)) D11 D12 D13 D14 D15
    let m5 := wbytes m4 (aG + nat_to_word 4) [hex_digit (nib n (7 - 4))]
    have Hmok5 : tmem_ok inp asp arnd aG m5 :=
      tmem_ok_grant inp asp arnd aG m4 _ _ Hmok4
    obtain ⟨Rf, F1, F10, F11, F12, F13, F14, F15, HmsF⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG Re m5 n 5 Hb Hn (by omega) Hmok5
        E1 (E10 (by omega)) E11 E12 E13 E14 E15
    let m6 := wbytes m5 (aG + nat_to_word 5) [hex_digit (nib n (7 - 5))]
    have Hmok6 : tmem_ok inp asp arnd aG m6 :=
      tmem_ok_grant inp asp arnd aG m5 _ _ Hmok5
    obtain ⟨Rg, G1, G10, G11, G12, G13, G14, G15, HmsG⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG Rf m6 n 6 Hb Hn (by omega) Hmok6
        F1 (F10 (by omega)) F11 F12 F13 F14 F15
    let m7 := wbytes m6 (aG + nat_to_word 6) [hex_digit (nib n (7 - 6))]
    have Hmok7 : tmem_ok inp asp arnd aG m7 :=
      tmem_ok_grant inp asp arnd aG m6 _ _ Hmok6
    obtain ⟨Rh, H1, H10, H11, H12, H13, H14, H15, HmsH⟩ :=
      tgt_dig_iter inp asp arnd Hsp_hi aG Rg m7 n 7 Hb Hn (by omega) Hmok7
        G1 (G10 (by omega)) G11 G12 G13 G14 G15
    let m8 := wbytes m7 (aG + nat_to_word 7) [hex_digit (nib n (7 - 7))]
    have Hfold : m8 = wbytes mem aG (hdr8 n) := by
      unfold m8 m7 m6 m5 m4 m3 m2 m1 hdr8
      change _ = wbytes mem aG
        (((((((([] ++ [hex_digit (nib n 7)]) ++ [hex_digit (nib n 6)]) ++
          [hex_digit (nib n 5)]) ++ [hex_digit (nib n 4)]) ++ [hex_digit (nib n 3)]) ++
          [hex_digit (nib n 2)]) ++ [hex_digit (nib n 1)]) ++ [hex_digit (nib n 0)])
      simp only [wbytes_snoc, List.length_append, List.length_cons, List.length_nil]
      rfl
    refine ⟨Rh, H1, H13, H14, ?_⟩
    rw [← Hfold]
    exact msteps_trans _ _ _ _ Hms0
      (msteps_trans _ _ _ _ HmsA (msteps_trans _ _ _ _ HmsB
        (msteps_trans _ _ _ _ HmsC (msteps_trans _ _ _ _ HmsD
          (msteps_trans _ _ _ _ HmsE (msteps_trans _ _ _ _ HmsF
            (msteps_trans _ _ _ _ HmsG HmsH)))))))

theorem tgt_put_wall (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 4096) (Hplo : 0 < bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) < 2 ^ 64)
    (H1 : getr regs 1 = (0x1001168 : word))
    (H10 : getr regs 10 = len_word (rest.take n)) (H12 : getr regs 12 = len_word rest)
    (H13 : getr regs 13 = p) (H17 : getr regs 17 = Z_to_bv 64 64)
    (Hread : rdn target_segs mem p rest.length = some rest) :
    to_wall_tail target_segs (Z_to_bv 64 2)
      (mkst regs (Z_to_bv 64 0x100122c) mem trom) (rest.drop n)
      (fun ms => to_wexit target_segs ms [] (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n regs with
  | zero => omega
  | succ fuel IH =>
    rw [getr_nz _ _ (by decide)] at H1 H10 H12 H13 H17
    have hul := u_len_word_firstn n rest Hn2 (by omega)
    refine to_wall_tail.twt_step _ _ _ _ rfl
      (step_bge_ft _ _ _ _ _ _ _ _ _ TF_100122c (by decide) TD_100122c
        (by getr_resolve; regupd_resolve; rw [H10]; apply c_lts_0_pos <;> omega)) ?_
    norm_pc
    stepiv TF_1001230 TD_1001230 (p + nat_to_word n)
      (getr_resolve; regupd_resolve; rw [H13, H10]; exact v_add_len_firstn p n rest Hn2)
    stepiv TF_1001234 TD_1001234 (len_word (rest.drop n))
      (getr_resolve; regupd_resolve; rw [H12, H10]; exact v_sub_len_firstn n rest Hn2 (by omega))
    by_cases Hfull : n = rest.length
    · subst n
      rw [List.drop_length]
      refine to_wall_tail.twt_step _ _ _ _ rfl
        (step_bne_ft _ _ _ _ _ _ _ _ _ TF_1001238 (by decide) TD_1001238
          (by getr_resolve; regupd_resolve; exact c_eq_0_true)) ?_
      norm_pc
      apply to_wall_tail.twt_done
      stepi TF_100123c TD_100123c
      stepjr TF_1001240 TD_1001240 (0x1001168 : word)
        (getr_resolve; regupd_resolve; exact H1)
      stepi TF_1001168 TD_1001168
      refine to_wexit.tw_step _ _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_100116c (by decide)) ?_
      apply tw_exit_coden
      · getr_resolve; regupd_resolve; rfl
      · getr_resolve; regupd_resolve; rfl
      · decide
    · have Hlt : n < rest.length := by omega
      have hdlen : ((rest.drop n).length : Int) < 2 ^ 64 := by rw [List.length_drop]; omega
      have hdu := u_len_word (rest.drop n) hdlen
      have Hsk : rdn target_segs mem (p + nat_to_word n) (rest.drop n).length =
          some (rest.drop n) := by
        rw [List.length_drop]
        exact LinuxProcessSemantics.Common.SeqExec.rdn_skipn target_segs mem rest.length p rest n Hread Hn2
      have HuP : bv_unsigned (p + nat_to_word n) = bv_unsigned p + (n : Int) := by
        rw [word_add_nat_Z p n (by omega), u_Z2bv _ (by omega) (by omega)]
      refine to_wall_tail.twt_step _ _ _ _ rfl
        (step_bne_tk _ _ _ _ _ _ _ _ _ TF_1001238 (by decide) TD_1001238
          (by getr_resolve; regupd_resolve; apply c_eq_0_false; rw [hdu, List.length_drop]; omega)) ?_
      norm_pc
      stepi TF_1001220 TD_1001220
      stepiv TF_1001224 TD_1001224 (p + nat_to_word n) (getr_resolve; regupd_resolve; exact v_addi_0 _)
      refine to_wall_tail.twt_step _ _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_1001228 (by decide)) ?_
      apply to_wall_tail.twt_more
      · rw [List.length_drop]; omega
      · apply twl_write_rec
        · getr_resolve; regupd_resolve; rw [H17]; rfl
        · getr_resolve; regupd_resolve; rfl
        · getr_resolve; regupd_resolve
          rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
          change rdn target_segs mem (p + nat_to_word n)
            (word_to_nat (len_word (rest.drop n))) = _
          change rdn target_segs mem (p + nat_to_word n) (word_to_nat (nat_to_word (rest.drop n).length)) = _
          rw [word_to_nat_ntw _ hdlen]
          exact Hsk
        · rw [List.length_drop]; omega
        · intro m Hm1 Hm2
          norm_pc
          apply IH (rest.drop n) (p + nat_to_word n) m
          · rw [List.length_drop]; omega
          · exact Hm1
          · exact Hm2
          · rw [List.length_drop]; omega
          · rw [HuP]; omega
          · rw [HuP, List.length_drop]; omega
          · getr_resolve; regupd_resolve; exact H1
          · getr_resolve; regupd_resolve; rfl
          · getr_resolve; regupd_resolve; rfl
          · getr_resolve; regupd_resolve; rfl
          · getr_resolve; regupd_resolve; exact H17
          · exact Hsk

include Hsp_hi in
theorem tgt_tail (fs0 : Fs.Fs) (acc : List byte) (c : config)
    (HTH : tgt_TH inp asp arnd fs0 acc c) : realizes target_segs c (arena_tail fs0 acc) := by
  obtain ⟨aG, regs, mem, Hb, Hh, Hlazy, Hfs, Hfd2, Hms0, K1, K13, K14, Hle, Hmok, Hrdn⟩ := HTH
  cases c with
  | mkCfg ms0 model =>
    have Hceil := tgrant_below_stack asp aG Hb
    have Hsp := asp_hi_num asp Hsp_hi
    have Ha := u64_range aG
    have Hpos := Hb.1
    unfold arena_tail
    rw [← Hfs]
    apply wall_realizes_ch target_segs (Z_to_bv 64 2) ch2 ms0 model
      [arena_out acc] (Z_to_bv 64 0) Hh Hlazy Hfd2 fd32_2
    · refine ⟨by rw [arena_out_length]; omega, ?_⟩
      apply msteps_to_wall_tail _ _ _ _ _ _ Hms0
      obtain ⟨R, L1, L13, L14, HmsH⟩ :=
        tgt_hdr_run inp asp arnd Hsp_hi aG regs mem acc.length Hb Hle Hmok K1 K13 K14
      apply msteps_to_wall_tail _ _ _ _ _ _ HmsH
      let mem8 := wbytes mem aG (hdr8 acc.length)
      sym_block_ex target_segs (mkst R (Z_to_bv 64 0x1001214) mem8 trom)
        5 [false] [] [(1, ELit 0x1001168), (13, EVar 32), (14, EVar 33)]
        [aG, nat_to_word acc.length] [] R2 HR2 Hms2
      · rw [bv_eqb_Z, u_ntw _ (by unfold cap at Hle; omega)]
        change decide (bv_unsigned (Z_to_bv 64 ((acc.length : Int) + 8)) = 0) = false
        rw [u_Z2bv _ (by omega) (by unfold cap at Hle; omega)]
        simp only [decide_eq_false_iff_not]
        omega
      · rw [L1]; rfl
      · exact L13
      · exact L14
      · apply msteps_to_wall_tail _ _ _ _ _ _ Hms2
        have K1' : getr R2 1 = (0x1001168 : word) := by sym_regs HR2 <;> rfl
        have K17' : getr R2 17 = Z_to_bv 64 64 := by sym_regs HR2 <;> rfl
        have K10' : getr R2 10 = Z_to_bv 64 2 := by sym_regs HR2 <;> rfl
        have K11' : getr R2 11 = aG := by sym_regs HR2; exact v_addi_0 _
        have K13' : getr R2 13 = aG := by sym_regs HR2
        have K12' : getr R2 12 = nat_to_word (8 + acc.length) := by
          sym_regs HR2
          rw [u_ntw _ (by unfold cap at Hle; omega)]
          change Z_to_bv 64 ((acc.length : Int) + 8) = nat_to_word (8 + acc.length)
          unfold nat_to_word
          congr 1
          omega
        clear HR2
        have Hbuf : rdn target_segs mem8 aG (8 + acc.length) = some (arena_out acc) := by
          unfold arena_out mem8
          apply rdn_app
          · exact rdn_wbytes_hit target_segs (hdr8 acc.length) mem aG
              (by rw [hdr8_length]; omega)
          · rw [rdn_wbytes_out _ _ _ _ _ _
              (by right; rw [hdr8_length, word_add_nat]; u_norm; omega)
              (by rw [word_add_nat]; u_norm; unfold cap at Hle; omega)
              (by rw [hdr8_length]; omega)]
            rw [word_add_nat]
            exact Hrdn
        refine to_wall_tail.twt_step _ _ _ _ rfl
          (step_ecall _ _ _ _ _ _ TF_1001228 (by decide)) ?_
        apply to_wall_tail.twt_more
        · rw [arena_out_length]; omega
        · apply twl_write_rec
          · rw [K17']; rfl
          · rw [← getr_nz _ _ (by decide)]; exact K10'
          · rw [← getr_nz _ 11 (by decide), ← getr_nz _ 12 (by decide), K11', K12']
            rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
            change rdn target_segs mem8 aG (word_to_nat (nat_to_word (8 + acc.length))) = _
            rw [word_to_nat_ntw _ (by unfold cap at Hle; omega)]
            exact Hbuf
          · rw [arena_out_length]; omega
          · intro n Hn1 Hn2
            norm_pc
            apply tgt_put_wall (arena_out acc).length (arena_out acc) aG n
            · omega
            · exact Hn1
            · exact Hn2
            · rw [arena_out_length]; unfold cap at Hle; omega
            · exact Hpos
            · rw [arena_out_length]; unfold cap at Hle; omega
            · getr_resolve; exact K1'
            · getr_resolve; rfl
            · getr_resolve; rw [← getr_nz _ _ (by decide), K12']; unfold len_word; rw [arena_out_length]; rfl
            · getr_resolve; exact K13'
            · getr_resolve; exact K17'
            · rw [arena_out_length]; exact Hbuf
    · exact arena_out_modeled acc Hle

include Hsp_hi in
theorem tgt_grant_LH (regs : bvmap 5 word) (hint a : word)
    (Hr1 : getr regs 1 = (0x1001168 : word)) (Hr5 : getr regs 5 = Z_to_bv 64 4096)
    (H11 : getr regs 11 = Z_to_bv 64 4096)
    (Hg : grant_ok hint (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) a
      (page_round_up_Z (bv_unsigned (ms_gpr (tgt_mmap_ms inp asp arnd regs) 1))) = true) :
    tgt_LH inp asp arnd inp.in_fs []
      (mkCfg (advance_past_svc (apply_effect (tgt_mmap_ms inp asp arnd regs)
          (mkEffect a [] [(a, page_round_up (ms_gpr (tgt_mmap_ms inp asp arnd regs) 1))])))
        (mmap_model a (page_round_up (ms_gpr (tgt_mmap_ms inp asp arnd regs) 1))
          (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))) := by
  have Hsp := asp_hi_num asp Hsp_hi
  have Hga : ms_gpr (tgt_mmap_ms inp asp arnd regs) 1 = Z_to_bv 64 4096 := by
    change reg_get regs 11 = _
    rw [← getr_nz _ _ (by decide)]
    exact H11
  rw [Hga] at Hg ⊢
  change grant_ok hint _ a 4096 = true at Hg
  have Hb : tgbounds asp a := target_grant_unpack inp hint abrk amb asp a Hg
  have Hceil := tgrant_below_stack asp a Hb
  have Ha := u64_range a
  rw [pru_4096]
  unfold tgt_mmap_ms
  rw [adv_apply]
  sym_block_ex target_segs
    (mkst (regupd regs 10 a) (Z_to_bv 64 0x1001194)
      (zfill a (Z_to_bv 64 4096) (tfmem inp asp arnd)) trom)
    7 [false] [] [(1, ELit 0x1001168), (5, ELit 4096), (10, EVar 32)] [a] [] RA HRA Hms
  · apply c_lts_pos_0; omega
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide), Hr1]; rfl
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide), Hr5]
  · getr_resolve; regupd_resolve; rfl
  · refine ⟨a, RA, zfill a (Z_to_bv 64 4096) (tfmem inp asp arnd), Hb, rfl, ?_, rfl,
      rfl, ⟨rfl, rfl⟩, Hms, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · rw [mmap_model_lazy]; rfl
    · sym_regs HRA <;> rfl
    · sym_regs HRA <;> rfl
    · sym_regs HRA <;> rfl
    · sym_regs HRA; exact v_addi_0 _
    · sym_regs HRA; rfl
    · sym_regs HRA <;> rfl
    · sym_regs HRA <;> rfl
    · decide
    · exact mem_grows_refl _

include Hsp_hi in
theorem tgt_Hfull (fs0 : Fs.Fs) (acc : List byte) (c : config)
    (HLH : tgt_LH inp asp arnd fs0 acc c) (Hfull : cap ≤ acc.length) :
    realizes target_segs c (arena_tail fs0 acc) := by
  obtain ⟨aG, regs, mem, Hb, Hh, Hlazy, Hfs, Hfd0, Hfd2, Hms0,
    K1, K5, K11, K13, K15, K16, K17, Hle, Hmok, Hrdn⟩ := HLH
  have Hn : acc.length = cap := by omega
  have Huk := u_ntw acc.length (by unfold cap at Hle; omega)
  apply tgt_tail inp asp arnd Hsp_hi
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x10011b0) mem trom)
    3 [true] [] [(1, ELit 0x1001168), (11, EVar 32), (13, EVar 33), (16, ELit 510)]
    [nat_to_word acc.length, aG] [] RA HRA Hms
  · rw [v_srl_3, bv_ltu_Z, v_srli_div _ 3 (by omega), Huk]
    rw [Hn]
    decide
  · rw [K1]; rfl
  · exact K11
  · exact K13
  · exact K16
  · refine ⟨aG, RA, mem, Hb, Hh, Hlazy, Hfs, Hfd2,
      msteps_trans _ _ _ _ Hms0 Hms, ?_, ?_, ?_, Hle, Hmok, Hrdn⟩
    · sym_regs HRA <;> rfl
    · sym_regs HRA
    · sym_regs HRA; exact v_addi_0 _

theorem tgt_read_block (aG : word) (regs : bvmap 5 word) (mem : word → Option byte) (k : Nat)
    (Hb : tgbounds asp aG) (Hk : k < cap)
    (H1 : getr regs 1 = (0x1001168 : word)) (H5 : getr regs 5 = Z_to_bv 64 4088)
    (H11 : getr regs 11 = nat_to_word k) (H13 : getr regs 13 = aG)
    (H15 : getr regs 15 = Z_to_bv 64 (bv_unsigned aG + 8))
    (H16 : getr regs 16 = Z_to_bv 64 510) (H17 : getr regs 17 = Z_to_bv 64 63) :
    ∃ R1, getr R1 1 = (0x1001168 : word) ∧ getr R1 5 = Z_to_bv 64 4088 ∧
      getr R1 13 = aG ∧ getr R1 14 = nat_to_word k ∧
      getr R1 15 = Z_to_bv 64 (bv_unsigned aG + 8) ∧
      getr R1 16 = Z_to_bv 64 510 ∧ getr R1 17 = Z_to_bv 64 63 ∧
      getr R1 10 = Z_to_bv 64 0 ∧ getr R1 11 = tbufA aG k ∧
      getr R1 12 = Z_to_bv 64 (cap - k : Nat) ∧
      msteps target_segs (mkst regs (Z_to_bv 64 0x10011b0) mem trom)
        (mkst R1 (Z_to_bv 64 0x10011c8) mem trom) := by
  have Huk := u_ntw k (by unfold cap at Hk; omega)
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x10011b0) mem trom)
    6 [false] [] [(1, ELit 0x1001168), (5, ELit 4088), (11, EVar 32),
      (13, EVar 33), (15, EVar 34), (16, ELit 510), (17, ELit 63)]
    [nat_to_word k, aG, Z_to_bv 64 (bv_unsigned aG + 8)] [] R1 HR1 Hms
  · rw [v_srl_3, bv_ltu_Z, v_srli_div _ 3 (by omega), Huk]
    change decide (510 < (k : Int) / 8) = false
    unfold cap at Hk
    u_norm
    simp only [decide_eq_false_iff_not]
    omega
  · rw [H1]; rfl
  · exact H5
  · exact H11
  · exact H13
  · exact H15
  · exact H16
  · exact H17
  · refine ⟨R1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1
    · sym_regs HR1; exact v_addi_0 _
    · sym_regs HR1
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1; exact tbufA_calc asp aG k Hb (by omega)
    · sym_regs HR1; exact tdcnt k (by omega)

def tgt_rd_ms (R1 : bvmap 5 word) (mem : word → Option byte) : machine_state :=
  { ms_regs := R1, ms_fregs := bvmap_empty, ms_pc_val := 0x10011c8,
    ms_svc_pending := some (getr R1 17), ms_resv := none,
    ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom }

theorem tgt_ret_eof (aG : word) (R1 : bvmap 5 word) (mem : word → Option byte) (k : Nat)
    (H1 : getr R1 1 = (0x1001168 : word)) (H13 : getr R1 13 = aG)
    (H14 : getr R1 14 = nat_to_word k) :
    ∃ R2, getr R2 1 = (0x1001168 : word) ∧ getr R2 13 = aG ∧
      getr R2 14 = nat_to_word k ∧
      msteps target_segs
        (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x10011cc) mem trom)
        (mkst R2 (Z_to_bv 64 0x10011d8) mem trom) := by
  sym_block_ex target_segs
    (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x10011cc) mem trom)
    3 [false, false] [] [(1, ELit 0x1001168), (10, ELit 0), (13, EVar 32), (14, EVar 33)]
    [aG, nat_to_word k] [] R2 HR2 Hms
  · decide
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide), H1]; rfl
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H13
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H14
  · refine ⟨R2, ?_, ?_, ?_, Hms⟩
    · sym_regs HR2 <;> rfl
    · sym_regs HR2
    · sym_regs HR2

theorem tgt_ret_blk (aG : word) (R1 : bvmap 5 word) (mem : word → Option byte) (k : Nat)
    (bs : List byte) (H1 : getr R1 1 = (0x1001168 : word))
    (H5 : getr R1 5 = Z_to_bv 64 4088) (H13 : getr R1 13 = aG)
    (H14 : getr R1 14 = nat_to_word k)
    (H15 : getr R1 15 = Z_to_bv 64 (bv_unsigned aG + 8))
    (H16 : getr R1 16 = Z_to_bv 64 510) (H17 : getr R1 17 = Z_to_bv 64 63)
    (Hlo : 1 ≤ bs.length) (Hhi : k + bs.length ≤ cap) :
    ∃ R2, getr R2 1 = (0x1001168 : word) ∧ getr R2 5 = Z_to_bv 64 4088 ∧
      getr R2 11 = nat_to_word (k + bs.length) ∧ getr R2 13 = aG ∧
      getr R2 15 = Z_to_bv 64 (bv_unsigned aG + 8) ∧
      getr R2 16 = Z_to_bv 64 510 ∧ getr R2 17 = Z_to_bv 64 63 ∧
      msteps target_segs (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x10011cc) mem trom)
        (mkst R2 (Z_to_bv 64 0x10011b0) mem trom) := by
  have Hul := u_len_word bs (by unfold cap at Hhi; omega)
  sym_block_ex target_segs
    (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x10011cc) mem trom)
    3 [false, true] [] [(1, ELit 0x1001168), (5, ELit 4088), (10, EVar 32),
      (13, EVar 33), (14, EVar 34), (15, EVar 35), (16, ELit 510), (17, ELit 63)]
    [len_word bs, aG, nat_to_word k, Z_to_bv 64 (bv_unsigned aG + 8)] [] R2 HR2 Hms
  · repeat' apply And.intro
    all_goals first
      | (simp only [Bool.not_eq_true']; apply c_eq_0_false; rw [Hul]; omega)
      | (apply c_lts_pos_0; rw [Hul]; unfold cap at Hhi; omega)
      | (rw [bv_lts_small _ _ (by rw [Hul]; unfold cap at Hhi; omega) (by decide)]
         rw [Hul]; simp only [decide_eq_false_iff_not]; change ¬ (bs.length : Int) < 0; omega)
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide), H1]; rfl
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H5
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H13
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H14
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H15
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H16
  · getr_resolve; regupd_resolve; rw [← getr_nz _ _ (by decide)]; exact H17
  · refine ⟨R2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    · sym_regs HR2 <;> rfl
    · sym_regs HR2 <;> rfl
    · sym_regs HR2; exact tntw_add k bs Hhi
    · sym_regs HR2
    · sym_regs HR2
    · sym_regs HR2 <;> rfl
    · sym_regs HR2 <;> rfl

include Hsp_hi in
theorem tgt_Hread (fs0 : Fs.Fs) (acc : List byte) (c : config)
    (HLH : tgt_LH inp asp arnd fs0 acc c) (Hlt : acc.length < cap) :
    ∃ ms1 buf x8 w,
      m_halted (cfg_model c) = none ∧ m_vm_lazy (cfg_model c) = [] ∧
      fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)) ∧
      msteps target_segs (cfg_ms c) ms1 ∧
      ms1.ms_svc_pending = some x8 ∧ bv_unsigned x8 = 63 ∧
      ms_gpr ms1 0 = Z_to_bv 64 0 ∧ ms_gpr ms1 1 = buf ∧ ms_gpr ms1 2 = dcnt cap acc ∧
      read_bytes_map (ms_writable_byte target_segs ms1) buf (dcnt cap acc) = some w ∧
      access_okb buf (bv_unsigned (dcnt cap acc)) = true ∧
      realizes target_segs (rd_next ms1 (cfg_model c) buf []) (arena_tail fs0 acc) ∧
      (∀ bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs → bs ≠ [] →
        tgt_LH inp asp arnd fs0 (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)) := by
  obtain ⟨aG, regs, mem, Hb, Hh, Hlazy, Hfs, Hfd0, Hfd2, Hms0,
    K1, K5, K11, K13, K15, K16, K17, Hle, Hmok, Hrdn⟩ := HLH
  have Hceil := tgrant_below_stack asp aG Hb
  have Hsp := asp_hi_num asp Hsp_hi
  have Ha := u64_range aG
  obtain ⟨R1, L1, L5, L13, L14, L15, L16, L17, L10, L11, L12, Hms1⟩ :=
    tgt_read_block asp aG regs mem acc.length Hb Hlt K1 K5 K11 K13 K15 K16 K17
  have Hbufval : bv_unsigned (tbufA aG acc.length) = bv_unsigned aG + 8 + (acc.length : Int) := by
    unfold tbufA
    exact u_Z2bv _ (by omega) (by unfold cap at Hle; omega)
  have Hcnt := dcnt_val cap Hcap_lt acc Hle
  obtain ⟨w, Hwb⟩ := zmem_wbuf target_segs (tgt_rd_ms R1 mem) (tfmem inp asp arnd)
    aG (Z_to_bv 64 4096) (tbufA aG acc.length) (dcnt cap acc) Hmok
    (by change bv_unsigned aG + 4096 ≤ 2 ^ 64; omega)
    (by rw [Hbufval]; omega)
    (by rw [Hbufval, Hcnt]; change _ ≤ bv_unsigned aG + 4096; unfold cap at *; omega)
  refine ⟨tgt_rd_ms R1 mem, tbufA aG acc.length, getr R1 17, w,
    Hh, Hlazy, Hfd0, ?_, rfl, ?_, ?_, ?_, ?_, Hwb, ?_, ?_, ?_⟩
  · apply msteps_trans _ _ _ _ Hms0
    apply msteps_trans _ _ _ _ Hms1
    exact msteps.mst_step _ _ _ rfl
      (step_ecall _ _ _ _ _ _ TF_10011c8 (by decide)) (msteps.mst_refl _)
  · rw [L17]; rfl
  · change reg_get R1 10 = _
    rw [← getr_nz _ _ (by decide)]; exact L10
  · change reg_get R1 11 = _
    rw [← getr_nz _ _ (by decide)]; exact L11
  · change reg_get R1 12 = _
    rw [← getr_nz _ _ (by decide)]; exact L12
  · apply access_okb_intro
    rw [Hbufval, Hcnt]
    unfold TASK_SIZE cap at *
    omega
  · simp only [rd_next]
    unfold tgt_rd_ms
    rw [adv_set]
    apply tgt_tail inp asp arnd Hsp_hi
    obtain ⟨R2, M1, M13, M14, Hms2⟩ := tgt_ret_eof aG R1 mem acc.length L1 L13 L14
    exact ⟨aG, R2, mem, Hb, Hh, Hlazy, Hfs, Hfd2, Hms2, M1, M13, M14, Hle, Hmok, Hrdn⟩
  · intro bs Hadm Hne
    have Hbl : acc.length + bs.length ≤ cap := by
      rcases Hadm with ⟨he, _⟩ | ⟨_, hhi, _⟩
      · exact False.elim (Hne he)
      · rw [Hcnt] at hhi; omega
    have Hb1 : 1 ≤ bs.length := by cases bs with
      | nil => exact False.elim (Hne rfl)
      | cons _ _ => simp only [List.length_cons]; omega
    cases bs with
    | nil => exact False.elim (Hne rfl)
    | cons b0 bs0 =>
      simp only [rd_next]
      unfold tgt_rd_ms
      rw [adv_write]
      let bs := b0 :: bs0
      let mem2 := write_to_mem mem (tbufA aG acc.length) bs
      have Hrdn2 : rdn target_segs mem2 (Z_to_bv 64 (bv_unsigned aG + 8))
          (acc.length + bs.length) = some (acc ++ bs) := by
        apply rdn_app
        · unfold mem2
          rw [write_to_mem_wbytes, rdn_wbytes_below _ _ _ _ _ _
            (by rw [Hbufval, u_Z2bv _ (by omega) (by omega)]; omega)
            (by rw [Hbufval]; unfold bs cap at *; simp only [List.length_cons] at *; omega)]
          exact Hrdn
        · rw [tbufA_split asp aG acc.length Hb Hle]
          unfold mem2
          apply rdn_write_to_mem
          rw [Hbufval]
          unfold bs cap at *
          simp only [List.length_cons] at *
          omega
      obtain ⟨R2, M1, M5, M11, M13, M15, M16, M17, Hms2⟩ :=
        tgt_ret_blk aG R1 mem2 acc.length bs L1 L5 L13 L14 L15 L16 L17 Hb1 Hbl
      unfold tgt_LH
      rw [List.length_append]
      refine ⟨aG, R2, mem2, Hb, ?_, ?_, ?_, ?_, ?_, Hms2,
        M1, M5, M11, M13, M15, M16, M17, Hbl, ?_, Hrdn2⟩
      · rw [m_halted_with_stdin]; exact Hh
      · rw [m_vm_lazy_with_stdin]; exact Hlazy
      · rw [m_fs_with_stdin]; exact Hfs
      · rw [m_fds_with_stdin]; exact Hfd0
      · unfold fdchan at *
        rw [m_fds_with_stdin]; exact Hfd2
      · exact tmem_ok_buf inp asp arnd aG mem _ bs Hmok

include Hsp_lo Hsp_hi in
theorem target_realizes :
    realizes target_segs
      (init_config target_segs TargetMemImage_init_pc target_phdrs asp abrk amb arnd target_alloc_limit inp)
      (arena_outcomes inp.in_fs inp.in_stdin) := by
  obtain ⟨regs, Hra, Hsp, H5, H11, H12, H13, H14, H15, Hno, Hms⟩ :=
    tgt_to_mmap inp asp arnd Hsp_lo Hsp_hi
  unfold init_config arena_outcomes arena_fail
  apply rz_mmap_drain target_segs cap Hcap_lt Hcap_mod
    (tgt_LH inp asp arnd inp.in_fs) (arena_tail inp.in_fs)
    (tgt_Hfull inp asp arnd Hsp_hi inp.in_fs) (tgt_Hread inp asp arnd Hsp_hi inp.in_fs)
    _ (tgt_mmap_ms inp asp arnd regs)
    (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
    (getr regs 17) [] (Z_to_bv 64 1)
  · rfl
  · rfl
  · apply init_model_fd1chan
  · exact Hms
  · rfl
  · exact Hno
  · change (reg_get regs 11 ≠ Z_to_bv 64 0 ∧ reg_get regs 12 = Z_to_bv 64 3 ∧
      reg_get regs 13 = Z_to_bv 64 34 ∧ reg_get regs 14 = Z_to_bv 64 (-1) ∧
      reg_get regs 15 = Z_to_bv 64 0)
    rw [← getr_nz _ 11 (by decide), ← getr_nz _ 12 (by decide),
      ← getr_nz _ 13 (by decide), ← getr_nz _ 14 (by decide), ← getr_nz _ 15 (by decide)]
    refine ⟨?_, H12, H13, ?_, H15⟩
    · rw [H11]; decide
    · rw [H14]; rfl
  · intro e He
    obtain ⟨He1, He2⟩ := mmap_errno_range e He
    exact tgt_fail_wexit inp asp arnd regs e He1 He2 Hra
  · intro a Ha
    exact tgt_grant_LH inp asp arnd Hsp_hi abrk amb regs _ a Hra H5 H11 Ha
  · refine ⟨Z_to_bv 64 0x2aaaaab000, ?_⟩
    have Hlen : ms_gpr (tgt_mmap_ms inp asp arnd regs) 1 = Z_to_bv 64 4096 := by
      change reg_get regs 11 = _
      rw [← getr_nz _ _ (by decide)]; exact H11
    rw [Hlen]
    exact target_grant_witness inp _ abrk amb asp Hsp_lo
  · intro b Hb
    cases Hb

end TargetProof
end LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_target
