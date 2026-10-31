import LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_defs
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.WallSim

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
-/

/-! # mmap-upper-ns source binary

Proof-side twin of `theories/Examples/mmap_upper_ns/mmap_upper_ns_source.v`.
Rocq section parameters become Lean section variables; `Z` becomes `Int`,
`nat` and `N` become `Nat`, and `firstn`/`skipn` become `List.take`/`List.drop`.
The proof follows the crt entry, inline string scan, mmap branch, uppercase
copy, short-write retry loop, munmap, and exit. Instruction and memory facts
come from the existing Common library and this binary's image.
-/

namespace LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.State.ProcInput
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.Footprint
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Examples.mmap_upper_ns.SourceMemImage
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_code
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem source_init_pc_val : SourceMemImage_init_pc = 0x11128 := by rfl


theorem source_avoids_data (a n : Int) (ha : 0x13000 ≤ a) :
    range_avoids_ro_segs source_segs a n = true :=
  range_avoids_ro_above source_segs 0x13000 a n (by decide) ha

theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  have hlen : SourceMemImage_seg_bytes_003_chars.length = 8192 := by
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  have hbyte (i : Nat) (hi : i < 4096) :
      (segment_byte_at SourceMemImage_segment_003.seg_bytes i).isSome = true := by
    rw [SourceMemImage_segment_003_byte_ascii]
    simp only [LinuxProcessSemantics.Common.ImageBytes.ascii_segment_byte_at,
      hlen, show 8192 / 2 = (4096 : Nat) from rfl, ite_eq_left hi]
    exact LinuxProcessSemantics.Common.ImageBytes.hex_chars_byte_at_isSome
      _ i SourceMemImage_seg_bytes_003_hex (by omega)
  have window (n : Nat) (a : word) (hlo : 0x13000 ≤ bv_unsigned a)
      (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
      wseg_ok source_segs a n = true := by
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      have hf : find_segment source_segs (bv_unsigned a) 1 =
          some SourceMemImage_segment_003 := by
        change (if decide (0x10000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x11000)
          then some SourceMemImage_segment_000 else
          if decide (0x11000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x12000)
          then some SourceMemImage_segment_001 else
          if decide (0x12000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x13000)
          then some SourceMemImage_segment_002 else
          if decide (0x13000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x14000)
          then some SourceMemImage_segment_003 else none) = _
        simp only [show ¬ bv_unsigned a + 1 ≤ 0x11000 by omega,
          show ¬ bv_unsigned a + 1 ≤ 0x12000 by omega,
          show ¬ bv_unsigned a + 1 ≤ 0x13000 by omega,
          show bv_unsigned a + 1 ≤ 0x14000 by omega,
          hlo, decide_false, decide_true, Bool.and_false, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte]
      have hb := hbyte (bv_unsigned a - 0x13000).toNat (by omega)
      have ha : bv_unsigned (a + 1) = bv_unsigned a + 1 :=
        u_add1 a (by omega)
      have ht := ih (a + 1) (by omega) (by omega)
      simp only [wseg_ok, hf]
      change (true && (match segment_byte_at SourceMemImage_segment_003.seg_bytes
        (bv_unsigned a - 0x13000).toNat with
        | some _ => true | none => false) && wseg_ok source_segs (a + 1) n) = true
      cases he : segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - 0x13000).toNat with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb
      | some b => exact ht
  exact window 4096 0x13000 (by decide) (by decide)


theorem source_store_ok (m : word → Option byte) (a : word) (k : Nat)
    (hlo : 0x13000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (k : Int) ≤ 0x14000) :
    store_ok source_segs m a k = true :=
  store_ok_window source_segs m 0x13000 a 4096 k 0x13000 0x14000
    rfl rfl (by decide) source_data_wseg hlo hhi

theorem source_reserved_val : segments_reserved source_segs =
    [(Z_to_bv 64 0x10000, Z_to_bv 64 0x1000), (Z_to_bv 64 0x11000, Z_to_bv 64 0x1000),
     (Z_to_bv 64 0x12000, Z_to_bv 64 0x1000), (Z_to_bv 64 0x13000, Z_to_bv 64 0x1000)] := by
  decide +kernel

theorem source_grant_witness (inp : ProcInput) (hint brk0 mb sp : word)
    (hsp : sp_window_lo ≤ bv_unsigned sp) :
    grant_ok hint (init_model (segments_reserved source_segs) brk0 mb sp source_alloc_limit inp)
      (Z_to_bv 64 0x2aaaaab000) 4096 = true := by
  rw [source_reserved_val]
  unfold grant_ok
  have he : decide (0x2aaaaab000 + 4096 ≤ bv_unsigned sp - stack_max_size) = true := by
    apply decide_eq_true
    unfold sp_window_lo at hsp
    unfold stack_max_size
    omega
  change ((((true && true) && decide (0x2aaaaab000 + 4096 ≤ bv_unsigned sp - stack_max_size)) && true) && _) = true
  rw [he]
  simp only [Bool.true_and, decide_eq_true_eq]
  change (0 : Int) + 4096 ≤ 0x400000000
  omega

theorem source_grant_unpack (inp : ProcInput) (hint brk0 mb sp aG : word)
    (hg : grant_ok hint (init_model (segments_reserved source_segs) brk0 mb sp source_alloc_limit inp) aG 4096 = true) :
    0 < bv_unsigned aG ∧ bv_unsigned aG % page_size = 0 ∧
    bv_unsigned aG + 4096 ≤ bv_unsigned sp - stack_max_size ∧
    (bv_unsigned aG + 4096 ≤ 0x10000 ∨ 0x11000 ≤ bv_unsigned aG) ∧
    (bv_unsigned aG + 4096 ≤ 0x11000 ∨ 0x12000 ≤ bv_unsigned aG) ∧
    (bv_unsigned aG + 4096 ≤ 0x12000 ∨ 0x13000 ≤ bv_unsigned aG) := by
  obtain ⟨hal, hpos, hceil, hfree, _⟩ := grant_ok_unpack _ _ _ _ hg
  change bv_unsigned aG + 4096 ≤ bv_unsigned sp - stack_max_size at hceil
  change region_free (segments_reserved source_segs ++ []) aG (Z_to_bv 64 4096) = true at hfree
  rw [List.append_nil, source_reserved_val] at hfree
  obtain ⟨ha, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨hb, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨hc, _⟩ := region_free_cons _ _ _ _ _ hfree
  exact ⟨hpos, hal, hceil, ha, hb, hc⟩

theorem source_grant_avoids (aGZ x k : Int)
    (hd1 : aGZ + 4096 ≤ 0x10000 ∨ 0x11000 ≤ aGZ)
    (hd2 : aGZ + 4096 ≤ 0x11000 ∨ 0x12000 ≤ aGZ)
    (hd3 : aGZ + 4096 ≤ 0x12000 ∨ 0x13000 ≤ aGZ)
    (hx1 : aGZ ≤ x) (hx2 : x + k ≤ aGZ + 4096) :
    range_avoids_ro_segs source_segs x k = true := by
  have hc : x + k ≤ 0x10000 ∨ 0x13000 ≤ x := by omega
  rcases hc with hb | ha
  · have h0 : decide (0x10000 < x + k) = false := decide_eq_false (by omega)
    have h1 : decide (0x11000 < x + k) = false := decide_eq_false (by omega)
    have h2 : decide (0x12000 < x + k) = false := decide_eq_false (by omega)
    change ((false || !(decide (0x10000 < x + k) && _)) &&
      ((false || !(decide (0x11000 < x + k) && _)) &&
      ((false || !(decide (0x12000 < x + k) && _)) && (true && true)))) = true
    rw [h0, h1, h2]
    rfl
  · exact source_avoids_data x k ha

section SourceProof
variable (inp : ProcInput) (rsp : word) (rrnd : EntryDraw)
variable (Hva : valid_argv (in_argv inp)) (Hve : valid_envp (in_envp inp))
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)

local notation "av" => in_argv inp
local notation "ev" => in_envp inp
local notation "s" => List.getD av 1 []
local notation "n" => List.length s

include Hsp_lo in
theorem rsp_lo_num : 0x7fff80000000 ≤ bv_unsigned rsp := Hsp_lo
include Hsp_hi in
theorem rsp_hi_num : bv_unsigned rsp ≤ 0x800000000000 := Hsp_hi

def argcN : word := len_word av
def rwmem : word → Option byte := wrap_mem source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd
def rrom : word → Option byte := seg_rom source_segs

include Hva in
theorem u_argcN : bv_unsigned (argcN inp) = ((av).length : Int) := by
  have h := valid_argv_len av Hva
  exact u_len_word av (by omega)

include Hva Hve Hsp_hi in
theorem source_bsb_nw :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd).length : Int) < 2 ^ 64 := by
  have hb := bsb_bound source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd Hva Hve
  have hh := rsp_hi_num rsp Hsp_hi
  omega

theorem v_sll_3 (x : word) : v_sll x (Z_to_bv 64 3) = v_slli x 3 := by rfl

def envval : word := Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * ((av).length : Int))

include Hva Hsp_lo Hsp_hi in
theorem envval_eq : v_addi (v_add (v_addi rsp 8) (v_slli (argcN inp) 3)) 8 = envval inp rsp := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hl := valid_argv_len av Hva
  have hu := u_argcN inp Hva
  have hs := v_slli_3 (argcN inp) (by omega)
  have hp := u_Z2bv (bv_unsigned rsp + 8) (by omega) (by omega)
  have ha := v_add_small (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp) 3)
    (by rw [hp, hs, hu]; omega)
  unfold v_addi envval
  rw [ha, hp, hs, hu]
  congr 1
  omega

include Hva Hsp_lo Hsp_hi in
theorem envval_sym :
    Z_to_bv 64 (bv_unsigned (alu64 .ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (argcN inp) (Z_to_bv 64 3))) + 8) = envval inp rsp := by
  rw [alu_add, v_sll_3]
  exact envval_eq inp rsp Hva Hsp_lo Hsp_hi

def emem : word → Option byte := wbytes (rwmem inp rsp rrnd) 0x13000 (word_to_le_bytes 8 (envval inp rsp))
def fmem : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (emem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x8)) (word_to_le_bytes 8 (0x11154 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (word_to_le_bytes 8 (Z_to_bv 64 0))

def nN : word := nat_to_word n
def P : word := cat_argv_ptr rsp av ev 1

theorem rdn_rwmem_stack (a : word) (k : Nat)
    (ha : bv_unsigned rsp ≤ bv_unsigned a) (hnw : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn source_segs (rwmem inp rsp rrnd) a k =
    rdn source_segs (stack_to_mem rsp (entry_stack_image source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd)) a k :=
  rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ ha hnw

include Hsp_lo in
theorem rdn_emem_above (a : word) (k : Nat)
    (ha : bv_unsigned rsp ≤ bv_unsigned a) (hnw : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn source_segs (emem inp rsp rrnd) a k = rdn source_segs (rwmem inp rsp rrnd) a k := by
  have hlo := rsp_lo_num rsp Hsp_lo
  unfold emem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; change 0x13000 + 8 ≤ _; omega) hnw]

include Hsp_lo Hsp_hi in
theorem rdn_fmem_above (a : word) (k : Nat)
    (ha : bv_unsigned rsp ≤ bv_unsigned a) (hnw : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn source_segs (fmem inp rsp rrnd) a k = rdn source_segs (rwmem inp rsp rrnd) a k := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) hnw]
  exact rdn_emem_above inp rsp rrnd Hsp_lo a k ha hnw

include Hva Hve Hsp_hi in
theorem source_ptr_bounds (h2 : 2 ≤ (av).length) :
    bv_unsigned rsp ≤ bv_unsigned (P inp rsp) ∧
    bv_unsigned (P inp rsp) + (n : Int) + 1 < 2 ^ 64 := by
  have hh := rsp_hi_num rsp Hsp_hi
  exact argv_ptr_bounds rsp av ev 1 Hva Hve (by omega) (by unfold argv_layout_slack; omega)

include Hva Hve Hsp_lo Hsp_hi in
theorem fread_str_byte (j : Nat) (h2 : 2 ≤ (av).length) (hj : j ≤ n) :
    rdn source_segs (fmem inp rsp rrnd) (P inp rsp + nat_to_word j) 1 = some [byte_at s j] := by
  obtain ⟨hge, hup⟩ := source_ptr_bounds inp rsp Hva Hve Hsp_hi h2
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_rwmem_stack inp rsp rrnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_byte_k _ _ _ _ _ _ _ _ _ _ (by omega) hj (source_bsb_nw inp rsp rrnd Hva Hve Hsp_hi)

include Hsp_lo Hsp_hi in
theorem fread_slot_ra :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8 =
    some (word_to_le_bytes 8 (0x11154 : word)) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _ (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

include Hsp_lo Hsp_hi in
theorem fread_slot_0 (a : word)
    (ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18),
      Z_to_bv 64 (bv_unsigned rsp - 0x10)]) :
    rdn source_segs (fmem inp rsp rrnd) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> unfold fmem
  all_goals repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _ (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]


include Hsp_lo Hsp_hi in
theorem source_epilogue (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (h10 : reg_get regs 10 = code)
    (hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8 = some (word_to_le_bytes 8 (0x11154 : word)))
    (hz : ∀ a, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18),
      Z_to_bv 64 (bv_unsigned rsp - 0x10)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    ∃ regs', bv_unsigned (getr regs' 17) = 93 ∧ reg_get regs' 10 = code ∧
      msteps source_segs (mkst regs 0x11110 mem rrom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := 0x11158,
        ms_svc_pending := some (getr regs' 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rrom } := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 0x11110) mem rrom)
    8 [] [ELit 0x11154, ELit 0, ELit 0, ELit 0]
    [(2, EVar 32)] [Z_to_bv 64 (bv_unsigned rsp - 0x30)] [] R HR Hms
  · repeat' apply And.intro
    all_goals first
      | omega
      | rfl
      | (refine ⟨word_to_le_bytes 8 (Z_to_bv 64 0), ?_, bytes_le_to_Z_8 _⟩
         apply hz
         simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])
      | exact ⟨word_to_le_bytes 8 (0x11154 : word), hra, bytes_le_to_Z_8 _⟩
  · exact h2
  · refine ⟨R, ?_, ?_, ?_⟩
    · sym_regs HR; rfl
    · sym_regs HR; exact h10
    · apply msteps_trans _ _ _ _ Hms
      sym_pc_lit
      exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11158 rfl) (msteps.mst_refl _)

include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_lt2 (hlt2 : (av).length < 2) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11128 source_phdrs rsp rrnd av ev (in_uid inp) (in_hwcap inp))
      [] (Z_to_bv 64 2) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hlen := valid_argv_len av Hva
  have hu := u_argcN inp Hva
  rw [init_mkst]
  sym_block source_segs 16 [true] [] [(2, EVar 32)] [rsp] [argcN inp] RA HRA
  · repeat' apply And.intro
    all_goals first
      | sym_br
      | (apply source_store_ok <;> (u_norm; omega))
      | (have he : Z_to_bv 64 (bv_unsigned rsp + 0) = rsp := by
           apply bv_eq_of_unsigned; u_norm; omega
         rw [he]
         refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
         rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
         exact read_argc _ _ _ _ _ _ _ _ (source_bsb_nw inp rsp rrnd Hva Hve Hsp_hi))
  · getr_resolve; rfl
  · refine to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11158 rfl) ?_
    apply tw_exit_coden
    · sym_regs HRA; rfl
    · sym_regs HRA; rfl
    · decide


include Hva Hve Hsp_lo Hsp_hi in
theorem source_prologue (h2 : 2 ≤ (av).length) :
    ∃ regsP,
      (reg_get regsP 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧
       reg_get regsP 18 = P inp rsp ∧ reg_get regsP 8 = nat_to_word 0 ∧
       reg_get regsP 9 = Z_to_bv 64 0) ∧
      msteps source_segs
        (init_machine_state source_segs 0x11128 source_phdrs rsp rrnd av ev (in_uid inp) (in_hwcap inp))
        (mkst regsP 0x11024 (fmem inp rsp rrnd) rrom) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have hlen := valid_argv_len av Hva
  have hu := u_argcN inp Hva
  obtain ⟨hpge, hplt⟩ := source_ptr_bounds inp rsp Hva Hve Hsp_hi h2
  rw [init_mkst]
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
      (Z_to_bv 64 0x11128)
      (wrap_mem source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd) (seg_rom source_segs))
    20 [false] [] [(2, EVar 32), (9, ELit 0), (18, ELit 0), (8, ELit 0)]
    [rsp] [argcN inp, P inp rsp] RA HRA Hms
  · repeat' apply And.intro
    all_goals first
      | omega
      | rfl
      | sym_br
      | solve_store_ok
      | (apply source_store_ok <;> (u_norm; omega))
      | (have he : Z_to_bv 64 (bv_unsigned rsp + 16) = rsp + nat_to_word (8 + 8 * 1) := by
           rw [word_add_nat]; rfl
         rw [he]
         refine ⟨word_le8 (P inp rsp), ?_, bytes_le_n_to_le_8 _⟩
         rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _
           (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
         exact read_argv_ptr_k _ _ _ _ _ _ _ _ _ (by omega) (source_bsb_nw inp rsp rrnd Hva Hve Hsp_hi))
      | (have he : Z_to_bv 64 (bv_unsigned rsp + 0) = rsp := by
           apply bv_eq_of_unsigned; u_norm; omega
         rw [he]
         refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
         rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
         exact read_argc _ _ _ _ _ _ _ _ (source_bsb_nw inp rsp rrnd Hva Hve Hsp_hi))
  all_goals try (getr_resolve; rfl)
  refine ⟨RA, ?_, ?_⟩
  · repeat' apply And.intro
    all_goals sym_regs HRA <;> sym_close
  · unfold fmem emem rwmem rrom
    revert Hms
    sym_mem_norm
    rw [v_sll_3, ← envval_eq inp rsp Hva Hsp_lo Hsp_hi]
    exact fun h => h


include Hva Hve Hsp_lo Hsp_hi in
theorem source_slen (h2 : 2 ≤ (av).length) (d i : Nat) (regs : bvmap 5 word)
    (hid : i + d = n) (h8 : reg_get regs 8 = nat_to_word i)
    (h18 : reg_get regs 18 = P inp rsp) :
    ∃ regs', (∀ r : reg, r ≠ 8 → r ≠ 15 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 8 = nN inp ∧ reg_get regs' 18 = P inp rsp ∧
      msteps source_segs (mkst regs 0x11024 (fmem inp rsp rrnd) rrom)
        (mkst regs' 0x11030 (fmem inp rsp rrnd) rrom) := by
  have hnz := valid_argv_str_nz av 1 Hva (by omega)
  have hslen := valid_argv_str_len av 1 Hva (by omega)
  induction d generalizing i regs with
  | zero =>
    have hi : i = n := by omega
    have hb0 : byte_at s i = Z_to_bv 8 0 := by rw [hi]; exact byte_at_len _
    let q := regupd regs 15 (P inp rsp + nat_to_word i)
    let q1 := regupd q 15 (Z_to_bv 64 0)
    have e1 : step source_segs (mkst regs 0x11024 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q 0x11028 (fmem inp rsp rrnd) rrom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ SF_11024 rfl SD_11024 (by decide)
      getr_resolve; rw [h8, h18]; rfl
    have e2 : step source_segs (mkst q 0x11028 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q1 0x1102c (fmem inp rsp rrnd) rrom) := by
      apply step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) SF_11028 rfl SD_11028
      dsimp only [q]
      getr_resolve
      imm_norm
      rw [v_addi_0]
      rw [← hb0]
      exact fread_str_byte inp rsp rrnd Hva Hve Hsp_lo Hsp_hi i h2 (by omega)
    have e3 : step source_segs (mkst q1 0x1102c (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q1 0x11030 (fmem inp rsp rrnd) rrom) := by
      apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_1102c rfl SD_1102c
      dsimp only [q1]; getr_resolve; rfl
    refine ⟨q1, ?_, ?_, ?_, ?_⟩
    · intro r hr8 hr15
      dsimp only [q1, q]
      rw [regupd_other _ _ _ _ hr15, regupd_other _ _ _ _ hr15]
    · dsimp only [q1, q]
      regupd_resolve
      rw [h8, hi]
      rfl
    · dsimp only [q1, q]; regupd_resolve; exact h18
    · exact msteps.mst_step _ _ _ rfl e1
        (msteps.mst_step _ _ _ rfl e2 (msteps.mst_step _ _ _ rfl e3 (msteps.mst_refl _)))
  | succ d ih =>
    have hilt : i < n := by omega
    let b := byte_at s i
    have hbnz : b ≠ Z_to_bv 8 0 := byte_at_nz _ _ hnz hilt
    let q := regupd regs 15 (P inp rsp + nat_to_word i)
    let q1 := regupd q 15 (Z_to_bv 64 (bv_unsigned b))
    let q2 := regupd q1 8 (nat_to_word (i + 1))
    have e1 : step source_segs (mkst regs 0x11024 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q 0x11028 (fmem inp rsp rrnd) rrom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ SF_11024 rfl SD_11024 (by decide)
      getr_resolve; rw [h8, h18]; rfl
    have e2 : step source_segs (mkst q 0x11028 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q1 0x1102c (fmem inp rsp rrnd) rrom) := by
      apply step_lbu _ _ _ _ _ _ _ _ _ b SF_11028 rfl SD_11028
      dsimp only [q]; getr_resolve; imm_norm; rw [v_addi_0]
      exact fread_str_byte inp rsp rrnd Hva Hve Hsp_lo Hsp_hi i h2 (by omega)
    have e3 : step source_segs (mkst q1 0x1102c (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q1 0x110d4 (fmem inp rsp rrnd) rrom) := by
      apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_1102c rfl SD_1102c
      dsimp only [q1]; getr_resolve
      apply c_eq_0_false
      rw [u_zext8]
      exact byte_nz_u b hbnz
    have e4 : step source_segs (mkst q1 0x110d4 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q2 0x110d8 (fmem inp rsp rrnd) rrom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ SF_110d4 rfl SD_110d4 (by decide)
      dsimp only [q1, q]; getr_resolve
      rw [h8]
      exact v_addi_Sj i (by omega)
    have e5 : step source_segs (mkst q2 0x110d8 (fmem inp rsp rrnd) rrom) =
        MachineOk (mkst q2 0x11024 (fmem inp rsp rrnd) rrom) :=
      step_jal_x0 _ _ _ _ _ _ _ SF_110d8 rfl SD_110d8
    obtain ⟨regs', hag, h8f, h18f, hms⟩ := ih (i + 1) q2 (by omega)
      (by dsimp only [q2]; exact regupd_same _ _ _)
      (by dsimp only [q2, q1, q]; regupd_resolve; exact h18)
    refine ⟨regs', ?_, h8f, h18f, ?_⟩
    · intro r hr8 hr15
      rw [hag r hr8 hr15]
      dsimp only [q2, q1, q]
      rw [regupd_other _ _ _ _ hr8, regupd_other _ _ _ _ hr15, regupd_other _ _ _ _ hr15]
    · exact msteps.mst_step _ _ _ rfl e1
        (msteps.mst_step _ _ _ rfl e2 (msteps.mst_step _ _ _ rfl e3
          (msteps.mst_step _ _ _ rfl e4 (msteps.mst_step _ _ _ rfl e5 hms))))


include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_len3 (h2 : 2 ≤ (av).length) (hn : 4095 < n) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11128 source_phdrs rsp rrnd av ev (in_uid inp) (in_hwcap inp))
      [] (Z_to_bv 64 3) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hnl := valid_argv_str_len av 1 Hva (by omega)
  have hun : bv_unsigned (nN inp) = (n : Int) := u_ntw n (by omega)
  obtain ⟨regsP, ⟨hp2, hp18, hp8, hp9⟩, hmsP⟩ := source_prologue inp rsp rrnd Hva Hve Hsp_lo Hsp_hi h2
  apply msteps_to_wexit _ _ _ _ _ hmsP
  obtain ⟨regsL, hfrL, h8L, h18L, hmsL⟩ := source_slen inp rsp rrnd Hva Hve Hsp_lo Hsp_hi h2 n 0 regsP (by omega) hp8 hp18
  apply msteps_to_wexit _ _ _ _ _ hmsL
  sym_block source_segs 3 [true] [] [(8, EVar 32)] [nN inp] [] RA HRA
  · sym_br
  · getr_resolve; exact h8L
  · obtain ⟨regsE, he17, he10, hmsE⟩ := source_epilogue rsp Hsp_lo Hsp_hi RA (fmem inp rsp rrnd) (Z_to_bv 64 3)
      (by sym_regs HRA; getr_resolve; rw [hfrL 2 (by decide) (by decide)]; exact hp2)
      (by sym_regs HRA; rfl)
      (fread_slot_ra inp rsp rrnd Hsp_lo Hsp_hi)
      (fread_slot_0 inp rsp rrnd Hsp_lo Hsp_hi)
    apply msteps_to_wexit _ _ _ _ _ hmsE
    exact tw_exit_coden _ _ _ _ _ _ he17 he10 (by decide)

include Hva Hve Hsp_lo Hsp_hi in
theorem source_to_mmap (h2 : 2 ≤ (av).length) (hn : n ≤ 4095) :
    ∃ regsE,
      reg_get regsE 1 = (0x11058 : word) ∧
      reg_get regsE 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧
      reg_get regsE 8 = nN inp ∧ reg_get regsE 18 = P inp rsp ∧
      reg_get regsE 11 = Z_to_bv 64 4096 ∧ reg_get regsE 12 = Z_to_bv 64 3 ∧
      reg_get regsE 13 = Z_to_bv 64 34 ∧ reg_get regsE 14 = Z_to_bv 64 (2^64 - 1) ∧
      reg_get regsE 15 = Z_to_bv 64 0 ∧ bv_unsigned (getr regsE 17) = 222 ∧
      msteps source_segs
        (init_machine_state source_segs 0x11128 source_phdrs rsp rrnd av ev (in_uid inp) (in_hwcap inp))
        { ms_regs := regsE, ms_fregs := bvmap_empty, ms_pc_val := 0x11178,
          ms_svc_pending := some (getr regsE 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := fmem inp rsp rrnd, ms_rom := rrom } := by
  have hun : bv_unsigned (nN inp) = (n : Int) := u_ntw n (by omega)
  obtain ⟨regsP, ⟨hp2, hp18, hp8, hp9⟩, hmsP⟩ := source_prologue inp rsp rrnd Hva Hve Hsp_lo Hsp_hi h2
  obtain ⟨regsL, hfrL, h8L, h18L, hmsL⟩ := source_slen inp rsp rrnd Hva Hve Hsp_lo Hsp_hi h2 n 0 regsP (by omega) hp8 hp18
  have hl2 : getr regsL 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) := by
    getr_resolve; rw [hfrL 2 (by decide) (by decide)]; exact hp2
  have hl18 : getr regsL 18 = P inp rsp := by getr_resolve; exact h18L
  sym_block_ex source_segs (mkst regsL (Z_to_bv 64 0x11030) (fmem inp rsp rrnd) rrom)
    17 [false] [] [(0, ELit 0), (8, EVar 32)] [nN inp] [] RA HRA Hms
  · sym_br
  all_goals try (getr_resolve; first | rfl | exact h8L)
  refine ⟨RA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try
    (sym_regs HRA <;> first | rfl | assumption | (getr_resolve; assumption))
  apply msteps_trans _ _ _ _ hmsP
  apply msteps_trans _ _ _ _ hmsL
  apply msteps_trans _ _ _ _ Hms
  exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11178 rfl) (msteps.mst_refl _)

include Hsp_lo Hsp_hi in
theorem source_fail_twm (model : Model) (regs : bvmap 5 word) (e : Int)
    (he1 : 1 ≤ e) (he2 : e ≤ 4095)
    (hr1 : reg_get regs 1 = (0x11058 : word))
    (hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30)) :
    twm source_segs (mkst (regupd regs 10 (errno_ret e)) 0x1117c (fmem inp rsp rrnd) rrom)
      model [] (Z_to_bv 64 4) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨her1, her2⟩ := errno_ret_range e he1 he2
  sym_block source_segs 4 [true] [] [(0, ELit 0), (1, ELit 0x11058), (10, EVar 32)]
    [errno_ret e] [] RA HRA
  · exact c_lts_neg_0 _ (by omega)
  · getr_resolve; rfl
  · getr_resolve; regupd_resolve; exact hr1
  · getr_resolve; regupd_resolve; rfl
  · obtain ⟨regsE, he17, he10, hmsE⟩ := source_epilogue rsp Hsp_lo Hsp_hi RA (fmem inp rsp rrnd) (Z_to_bv 64 4)
      (by sym_regs HRA; getr_resolve; regupd_resolve; exact hr2)
      (by sym_regs HRA; rfl)
      (fread_slot_ra inp rsp rrnd Hsp_lo Hsp_hi)
      (fread_slot_0 inp rsp rrnd Hsp_lo Hsp_hi)
    apply msteps_twm _ _ _ _ _ _ hmsE
    exact twm_exit_coden _ _ _ _ _ _ _ he17 he10 (by decide)


section SourceSucc
variable (aG : word)
variable (HaPos : 0 < bv_unsigned aG) (HaAl : bv_unsigned aG % page_size = 0)
variable (HaCeil : bv_unsigned aG + 4096 ≤ bv_unsigned rsp - stack_max_size)
variable (Hda : bv_unsigned aG + 4096 ≤ 0x10000 ∨ 0x11000 ≤ bv_unsigned aG)
variable (Hdb : bv_unsigned aG + 4096 ≤ 0x11000 ∨ 0x12000 ≤ bv_unsigned aG)
variable (Hdc : bv_unsigned aG + 4096 ≤ 0x12000 ∨ 0x13000 ≤ bv_unsigned aG)
variable (H2av : 2 ≤ inp.in_argv.length) (Hnle : (inp.in_argv.getD 1 []).length ≤ 4095)

include Hnle in
theorem nN_le : (n : Int) ≤ 4095 := by omega


def zmem : word → Option byte := zfill aG (Z_to_bv 64 4096) (fmem inp rsp rrnd)
def cmem (i : Nat) : word → Option byte := wbytes (zmem inp rsp rrnd aG) aG (upperv ((s).take i))

theorem grows_zmem : mem_grows (rwmem inp rsp rrnd) (zmem inp rsp rrnd aG) := by
  unfold zmem zfill fmem emem
  apply mem_grows_trans _ _ _ ?_ (zmem_grows _ _ _)
  repeat first
    | exact mem_grows_refl _
    | refine mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)

theorem cmem_S (i : Nat) (hi : i < n) :
    cmem inp rsp rrnd aG (i + 1) =
      wbytes (cmem inp rsp rrnd aG i) (aG + nat_to_word i) [upperb (byte_at s i)] := by
  unfold cmem
  rw [upperv_firstn_S s i hi, wbytes_snoc, length_upperv_firstn s i (by omega)]

include Hva Hve Hsp_lo Hsp_hi HaCeil H2av Hnle in
theorem cread_str_byte (i j : Nat) (hi : i ≤ n) (hj : j ≤ n) :
    rdn source_segs (cmem inp rsp rrnd aG i) (P inp rsp + nat_to_word j) 1 = some [byte_at s j] := by
  obtain ⟨hge, hup⟩ := source_ptr_bounds inp rsp Hva Hve Hsp_hi H2av
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have hnn := nN_le inp Hnle
  unfold cmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_upperv_firstn s i hi, word_add_nat]; u_norm; omega)
    (by rw [word_add_nat]; u_norm; omega)]
  unfold zmem
  rw [rdn_zfill_out _ _ _ _ _ _ (by rw [word_add_nat]; u_norm; omega)
    (by right; rw [word_add_nat]; u_norm; omega)]
  exact fread_str_byte inp rsp rrnd Hva Hve Hsp_lo Hsp_hi j H2av hj

include Hsp_hi HaCeil in
theorem grant_store_ok (m : word → Option byte) (a : word) (k : Nat)
    (hx1 : bv_unsigned aG ≤ bv_unsigned a)
    (hx2 : bv_unsigned a + (k : Int) ≤ bv_unsigned aG + 4096) :
    store_ok source_segs (zfill aG (Z_to_bv 64 4096) m) a k = true := by
  have hh := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  exact store_ok_zmem _ _ _ _ _ _ (by omega) hx1 hx2


include Hva Hve Hsp_lo Hsp_hi HaCeil H2av Hnle in
theorem source_copy (f i : Nat) (regs : bvmap 5 word)
    (h18 : reg_get regs 18 = P inp rsp) (h8 : reg_get regs 8 = nN inp)
    (h9 : reg_get regs 9 = aG) (h10 : reg_get regs 10 = Z_to_bv 64 25)
    (h15 : reg_get regs 15 = nat_to_word i) (hi : i ≤ n) (hf : n - i ≤ f) :
    ∃ regs', (∀ r : reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
      reg_get regs' r = reg_get regs r) ∧ reg_get regs' 12 = nat_to_word (n + 1) ∧
      msteps source_segs (mkst regs 0x11070 (cmem inp rsp rrnd aG i) rrom)
        (mkst regs' 0x11084 (wbytes (zmem inp rsp rrnd aG) aG (out_buf s)) rrom) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have hnn := nN_le inp Hnle
  have har := u64_range aG
  have em : wbytes (zmem inp rsp rrnd aG) aG (out_buf s) =
      wbytes (cmem inp rsp rrnd aG n) (aG + nat_to_word n) [Z_to_bv 8 10] := by
    unfold cmem
    rw [List.take_length]
    unfold out_buf
    rw [wbytes_snoc, length_upperv]
  have hexit (regs : bvmap 5 word) (h8 : reg_get regs 8 = nN inp)
      (h9 : reg_get regs 9 = aG) (h15 : reg_get regs 15 = nat_to_word n) :
      ∃ regs', (∀ r : reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg_get regs' r = reg_get regs r) ∧ reg_get regs' 12 = nat_to_word (n + 1) ∧
        msteps source_segs (mkst regs 0x11070 (cmem inp rsp rrnd aG n) rrom)
          (mkst regs' 0x11084 (wbytes (zmem inp rsp rrnd aG) aG (out_buf s)) rrom) := by
    let r1 := regupd regs 13 (aG + nat_to_word n)
    let r2 := regupd r1 12 (nat_to_word (n + 1))
    let r3 := regupd r2 15 (10 : word)
    refine ⟨r3, ?_, ?_, ?_⟩
    · intro r hr12 hr13 hr14 hr15
      dsimp only [r3, r2, r1]
      rw [regupd_other _ _ _ _ hr15, regupd_other _ _ _ _ hr12, regupd_other _ _ _ _ hr13]
    · dsimp only [r3, r2]; regupd_resolve; rfl
    · refine msteps.mst_step _ (mkst r1 0x11074 (cmem inp rsp rrnd aG n) rrom) _ rfl ?_ ?_
      · apply step_add_at _ _ _ _ _ _ _ _ _ _ SF_11070 rfl SD_11070 (by decide)
        getr_resolve; rw [h9, h15]; rfl
      refine msteps.mst_step _ (mkst r2 0x11078 (cmem inp rsp rrnd aG n) rrom) _ rfl ?_ ?_
      · apply step_addi_at _ _ _ _ _ _ _ _ _ _ SF_11074 rfl SD_11074 (by decide)
        dsimp only [r1]; getr_resolve; rw [h15]; exact v_addi_Sj n (by omega)
      refine msteps.mst_step _ (mkst r2 0x1107c (cmem inp rsp rrnd aG n) rrom) _ rfl ?_ ?_
      · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_11078 rfl SD_11078
        dsimp only [r2, r1]; getr_resolve; rw [h15, h8]; exact mmap_upper_ns_defs.c_eq_refl _
      refine msteps.mst_step _ (mkst r3 0x11080 (cmem inp rsp rrnd aG n) rrom) _ rfl ?_ ?_
      · apply step_addi_at _ _ _ _ _ _ _ _ _ _ SF_1107c rfl SD_1107c (by decide)
        getr_resolve; rfl
      refine msteps.mst_step _ _ _ rfl ?_ (msteps.mst_refl _)
      rw [em]
      apply step_sb_at _ _ _ _ _ _ _ _ _ (aG + nat_to_word n) (10 : word) (Z_to_bv 8 10) SF_11080 rfl SD_11080
      · dsimp only [r3, r2, r1]; getr_resolve; exact v_addi_0 _
      · dsimp only [r3]; getr_resolve; rfl
      · rfl
      · unfold cmem
        store_ok_peel
        apply grant_store_ok rsp Hsp_hi aG HaCeil <;> (rw [word_add_nat]; u_norm; omega)
  induction f generalizing i regs with
  | zero =>
    have he : i = n := by omega
    subst i
    exact hexit regs h8 h9 h15
  | succ f ih =>
    by_cases he : i = n
    · subst i; exact hexit regs h8 h9 h15
    have hilt : i < n := by omega
    let b := byte_at s i
    let r1 := regupd regs 13 (aG + nat_to_word i)
    let r2 := regupd r1 12 (nat_to_word (i + 1))
    let r3 := regupd r2 15 (P inp rsp + nat_to_word i)
    let r4 := regupd r3 15 (Z_to_bv 64 (bv_unsigned b))
    let r5 := regupd r4 14 (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-97))
    let r6 := regupd r5 14 (usub97 b)
    have e1 : step source_segs (mkst regs 0x11070 (cmem inp rsp rrnd aG i) rrom) =
        MachineOk (mkst r1 0x11074 (cmem inp rsp rrnd aG i) rrom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ SF_11070 rfl SD_11070 (by decide)
      getr_resolve; rw [h9, h15]; rfl
    have e2 : step source_segs (mkst r1 0x11074 (cmem inp rsp rrnd aG i) rrom) =
        MachineOk (mkst r2 0x11078 (cmem inp rsp rrnd aG i) rrom) := by
      apply step_addi_at _ _ _ _ _ _ _ _ _ _ SF_11074 rfl SD_11074 (by decide)
      dsimp only [r1]; getr_resolve; rw [h15]; exact v_addi_Sj i (by omega)
    have e3 : step source_segs (mkst r2 0x11078 (cmem inp rsp rrnd aG i) rrom) =
        MachineOk (mkst r2 0x110dc (cmem inp rsp rrnd aG i) rrom) := by
      apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_11078 rfl SD_11078
      dsimp only [r2, r1]; getr_resolve; rw [h15, h8]
      apply c_eq_neq
      unfold nN
      rw [u_ntw _ (by omega), u_ntw _ (by omega)]
      omega
    have e4 : step source_segs (mkst r2 0x110dc (cmem inp rsp rrnd aG i) rrom) =
        MachineOk (mkst r3 0x110e0 (cmem inp rsp rrnd aG i) rrom) := by
      apply step_add_at _ _ _ _ _ _ _ _ _ _ SF_110dc rfl SD_110dc (by decide)
      dsimp only [r2, r1]; getr_resolve; rw [h18, h15]; rfl
    have e5 : step source_segs (mkst r3 0x110e0 (cmem inp rsp rrnd aG i) rrom) =
        MachineOk (mkst r4 0x110e4 (cmem inp rsp rrnd aG i) rrom) := by
      apply step_lbu _ _ _ _ _ _ _ _ _ b SF_110e0 rfl SD_110e0
      dsimp only [r3]; getr_resolve; imm_norm; rw [v_addi_0]
      exact cread_str_byte inp rsp rrnd Hva Hve Hsp_lo Hsp_hi aG HaCeil H2av Hnle i i (by omega) (by omega)
    have e6 : step source_segs (mkst r4 0x110e4 (cmem inp rsp rrnd aG i) rrom) =
        MachineOk (mkst r5 0x110e8 (cmem inp rsp rrnd aG i) rrom) := by
      apply step_addiw_at _ _ _ _ _ _ _ _ _ _ SF_110e4 rfl SD_110e4 (by decide)
      dsimp only [r4]; getr_resolve; rfl
    have e7 : step source_segs (mkst r5 0x110e8 (cmem inp rsp rrnd aG i) rrom) =
        MachineOk (mkst r6 0x110ec (cmem inp rsp rrnd aG i) rrom) := by
      apply step_andi_at _ _ _ _ _ _ _ _ _ _ SF_110e8 rfl SD_110e8 (by decide)
      dsimp only [r5]; getr_resolve; exact usub97_addiw b
    have hstore : store_ok source_segs (cmem inp rsp rrnd aG i) (aG + nat_to_word i) 1 = true := by
      unfold cmem
      store_ok_peel
      apply grant_store_ok rsp Hsp_hi aG HaCeil <;> (rw [word_add_nat]; u_norm; omega)
    have hcm := cmem_S inp rsp rrnd aG i hilt
    have tail : ∃ rT, (∀ r : reg, r ≠ 15 → reg_get rT r = reg_get r6 r) ∧
        msteps source_segs (mkst r6 0x110ec (cmem inp rsp rrnd aG i) rrom)
          (mkst rT 0x110fc (cmem inp rsp rrnd aG (i + 1)) rrom) := by
      cases el : islower b with
      | false =>
        refine ⟨r6, ?_, ?_⟩
        · intro r hr; rfl
        · refine msteps.mst_step _ (mkst r6 0x110f8 (cmem inp rsp rrnd aG i) rrom) _ rfl ?_ ?_
          · apply step_bltu_tk _ _ _ _ _ _ _ _ _ SF_110ec rfl SD_110ec
            dsimp only [r6, r5, r4, r3, r2, r1]; getr_resolve; rw [h10, c_ltu_ltb]
            exact decide_eq_true (usub97_gt25 b el)
          refine msteps.mst_step _ _ _ rfl ?_ (msteps.mst_refl _)
          rw [hcm]
          apply step_sb_at _ _ _ _ _ _ _ _ _ (aG + nat_to_word i) (Z_to_bv 64 (bv_unsigned b)) (upperb b) SF_110f8 rfl SD_110f8
          · dsimp only [r6, r5, r4, r3, r2, r1]; getr_resolve; exact v_addi_0 _
          · dsimp only [r6, r5, r4]; getr_resolve; rfl
          · exact sb_upper_hi b el
          · exact hstore
      | true =>
        let r7 := regupd r6 15 (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-32))
        let r8 := regupd r7 15 (Z_to_bv 64 (bv_unsigned b - 32))
        refine ⟨r8, ?_, ?_⟩
        · intro r hr
          dsimp only [r8, r7]
          rw [regupd_other _ _ _ _ hr, regupd_other _ _ _ _ hr]
        · refine msteps.mst_step _ (mkst r6 0x110f0 (cmem inp rsp rrnd aG i) rrom) _ rfl ?_ ?_
          · apply step_bltu_ft _ _ _ _ _ _ _ _ _ SF_110ec rfl SD_110ec
            dsimp only [r6, r5, r4, r3, r2, r1]; getr_resolve; rw [h10, c_ltu_ltb]
            exact decide_eq_false (by have := usub97_le25 b el; change ¬ (25 : Int) < _; omega)
          refine msteps.mst_step _ (mkst r7 0x110f4 (cmem inp rsp rrnd aG i) rrom) _ rfl ?_ ?_
          · apply step_addiw_at _ _ _ _ _ _ _ _ _ _ SF_110f0 rfl SD_110f0 (by decide)
            dsimp only [r6, r5, r4]; getr_resolve; rfl
          refine msteps.mst_step _ (mkst r8 0x110f8 (cmem inp rsp rrnd aG i) rrom) _ rfl ?_ ?_
          · apply step_andi_at _ _ _ _ _ _ _ _ _ _ SF_110f4 rfl SD_110f4 (by decide)
            dsimp only [r7]; getr_resolve; exact upper_addiw b el
          refine msteps.mst_step _ _ _ rfl ?_ (msteps.mst_refl _)
          rw [hcm]
          apply step_sb_at _ _ _ _ _ _ _ _ _ (aG + nat_to_word i) (Z_to_bv 64 (bv_unsigned b - 32)) (upperb b) SF_110f8 rfl SD_110f8
          · dsimp only [r8, r7, r6, r5, r4, r3, r2, r1]; getr_resolve; exact v_addi_0 _
          · dsimp only [r8]; getr_resolve; rfl
          · exact sb_upper_lo b el
          · exact hstore
    obtain ⟨rT, hfrT, hmsT⟩ := tail
    let r9 := regupd rT 15 (nat_to_word (i + 1))
    have hfr9 (r : reg) (hr12 : r ≠ 12) (hr13 : r ≠ 13) (hr14 : r ≠ 14) (hr15 : r ≠ 15) :
        reg_get r9 r = reg_get regs r := by
      dsimp only [r9]
      rw [regupd_other _ _ _ _ hr15, hfrT r hr15]
      dsimp only [r6, r5, r4, r3, r2, r1]
      simp only [regupd_other _ _ _ _ hr14, regupd_other _ _ _ _ hr15,
        regupd_other _ _ _ _ hr12, regupd_other _ _ _ _ hr13]
    obtain ⟨regs', hfr, h12f, hms⟩ := ih (i + 1) r9
      (by rw [hfr9 18 (by decide) (by decide) (by decide) (by decide)]; exact h18)
      (by rw [hfr9 8 (by decide) (by decide) (by decide) (by decide)]; exact h8)
      (by rw [hfr9 9 (by decide) (by decide) (by decide) (by decide)]; exact h9)
      (by rw [hfr9 10 (by decide) (by decide) (by decide) (by decide)]; exact h10)
      (by dsimp only [r9]; exact regupd_same _ _ _) (by omega) (by omega)
    refine ⟨regs', ?_, h12f, ?_⟩
    · intro r hr12 hr13 hr14 hr15
      rw [hfr r hr12 hr13 hr14 hr15, hfr9 r hr12 hr13 hr14 hr15]
    · refine msteps.mst_step _ _ _ rfl e1 (msteps.mst_step _ _ _ rfl e2
        (msteps.mst_step _ _ _ rfl e3 (msteps.mst_step _ _ _ rfl e4
          (msteps.mst_step _ _ _ rfl e5 (msteps.mst_step _ _ _ rfl e6
            (msteps.mst_step _ _ _ rfl e7 ?_))))))
      apply msteps_trans _ _ _ _ hmsT
      refine msteps.mst_step _ (mkst r9 0x11100 (cmem inp rsp rrnd aG (i + 1)) rrom) _ rfl ?_ ?_
      · apply step_addi_at _ _ _ _ _ _ _ _ _ _ SF_110fc rfl SD_110fc (by decide)
        getr_resolve; rw [hfrT 12 (by decide)]
        dsimp only [r6, r5, r4, r3, r2]; regupd_resolve
        exact v_addi_0 _
      exact msteps.mst_step _ _ _ rfl (step_jal_x0 _ _ _ _ _ _ _ SF_11100 rfl SD_11100) hms

include Hsp_lo Hsp_hi in
theorem mu_sok8 (mem : word → Option byte) (a : word)
    (hg : mem_grows (rwmem inp rsp rrnd) mem)
    (hlo : bv_unsigned rsp - 0x50 ≤ bv_unsigned a)
    (hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp) :
    store_ok source_segs mem a 8 = true := by
  have hl := rsp_lo_num rsp Hsp_lo
  have hh := rsp_hi_num rsp Hsp_hi
  apply store_ok_mono _ _ _ _ _ hg
  unfold rwmem
  apply store_ok_wrap_window <;> (try unfold stack_max_size) <;> omega

local macro "mu_grows" : tactic => `(tactic| solve_mem_grows)
local macro "mu_sok" : tactic => `(tactic| (apply mu_sok8 <;> first | assumption | (solve | mu_grows) | (u_norm; omega)))
local macro "mu_ssd " F:term:max D:term:max a:term:max v:term:max " (" vtac:Lean.Parser.Tactic.tacticSeq ")" : tactic =>
  `(tactic| stepsd $F $D $a $v ($vtac) (mu_sok))
local macro "mu_sld " F:term:max D:term:max a:term:max v:term:max " (" rtac:Lean.Parser.Tactic.tacticSeq ")" : tactic =>
  `(tactic| stepld $F $D $a $v ($rtac))


include Hsp_lo Hsp_hi HaAl HaCeil in
theorem source_out_tail (model : Model) (regs : bvmap 5 word) (mem : word → Option byte)
    (hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (hr9 : reg_get regs 9 = aG)
    (hmap : map_has (m_vmmaps model).vm_maps aG (Z_to_bv 64 4096) = true)
    (hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8 = some (word_to_le_bytes 8 (0x11154 : word)))
    (hsl : ∀ a, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18),
      Z_to_bv 64 (bv_unsigned rsp - 0x10)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    twm source_segs (mkst regs 0x110ac mem rrom) model [] (Z_to_bv 64 0) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have har := u64_range aG
  sym_block source_segs 15 [] [] [(0, ELit 0), (2, EVar 32), (9, EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30), aG] [] RC HRC
  · getr_resolve; rfl
  · exact hr2
  · exact hr9
  · refine twm.twm_step _ _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11178 rfl) ?_
    apply twm_munmap_rec (a := aG) (nlen := Z_to_bv 64 4096)
    · sym_regs HRC; rfl
    · sym_regs HRC; exact v_addi_0 aG
    · sym_regs HRC; rfl
    · exact HaAl
    · decide
    · change bv_unsigned aG + page_round_up_Z 4096 ≤ TASK_SIZE
      rw [page_round_up_Z_4096]
      unfold TASK_SIZE
      omega
    · rw [pru_4096]; exact hmap
    · rw [pru_4096]
      sym_block source_segs 3 [] [] [(1, ELit 0x110cc), (2, EVar 32)]
        [Z_to_bv 64 (bv_unsigned rsp - 0x30)] [] RD HRD
      all_goals try (getr_resolve; regupd_resolve; sym_regs HRC <;> rfl)
      obtain ⟨regsE, he17, he10, hmsE⟩ := source_epilogue rsp Hsp_lo Hsp_hi RD (unfill aG (Z_to_bv 64 4096) mem) (Z_to_bv 64 0)
        (by sym_regs HRD <;> sym_close)
        (by sym_regs HRD; rfl)
        (by rw [rdn_unfill_out _ _ _ _ _ _ (by u_norm; omega)
              (by right; u_norm; omega)]; exact hra)
        (by
          intro aa haa
          have hab : bv_unsigned rsp - 0x20 ≤ bv_unsigned aa ∧ bv_unsigned aa + 8 ≤ bv_unsigned rsp - 8 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at haa
            rcases haa with rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
          rw [rdn_unfill_out _ _ _ _ _ _ (by omega) (by right; u_norm; omega)]
          exact hsl aa haa)
      apply msteps_twm _ _ _ _ _ _ hmsE
      exact twm_exit_coden _ _ _ _ _ _ _ he17 he10 (by decide)


include Hsp_lo Hsp_hi HaAl HaCeil in
theorem src_put_wall (model : Model) (fuel : Nat) (rest : List byte) (p : word) (k : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (hfuel : rest.length ≤ fuel) (hk1 : 1 ≤ k) (hk2 : k ≤ rest.length)
    (hlen : (rest.length : Int) ≤ 4096) (hplo : 0 < bv_unsigned p)
    (hphi : bv_unsigned p + (rest.length : Int) ≤ bv_unsigned rsp - 0x50)
    (h1 : reg_get regs 1 = (0x111a8 : word))
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (h9 : reg_get regs 9 = aG) (h10 : reg_get regs 10 = len_word (rest.take k))
    (h17 : bv_unsigned (reg_get regs 17) = 64)
    (hmap : map_has (m_vmmaps model).vm_maps aG (Z_to_bv 64 4096) = true)
    (hgrow : mem_grows (rwmem inp rsp rrnd) mem)
    (hra40 : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = some (word_to_le_bytes 8 (0x11094 : word)))
    (hcnt : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x28)) 8 = some (word_to_le_bytes 8 (len_word rest)))
    (hptr : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x30)) 8 = some (word_to_le_bytes 8 p))
    (hslra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8 = some (word_to_le_bytes 8 (0x11154 : word)))
    (hsl : ∀ a, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18),
      Z_to_bv 64 (bv_unsigned rsp - 0x10)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (hread : rdn source_segs mem p rest.length = some rest) :
    twm_tail source_segs (mkst regs 0x1120c mem rrom) model (rest.drop k) [] (Z_to_bv 64 0) := by
  induction fuel generalizing rest p k regs mem with
  | zero => omega
  | succ fuel ih =>
    have hlo := rsp_lo_num rsp Hsp_lo
    have hhi := rsp_hi_num rsp Hsp_hi
    have huk := u_len_word_firstn k rest hk2 (by omega)
    stepjr SF_1120c SD_1120c (0x111a8 : word) (getr_resolve; exact h1)
    mu_sld SF_111a8 SD_111a8 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (0x11094 : word) (exact hra40)
    stepiv SF_111ac SD_111ac (Z_to_bv 64 (bv_unsigned rsp - 0x30))
      (getr_resolve; rw [h2]; sp_norm; congr 1 <;> omega)
    stepj SF_111b0 SD_111b0
    stepi SF_111b4 SD_111b4
    chain_step
    · rfl
    · apply step_bltu_ft _ _ _ _ _ _ _ _ _ SF_111b8 rfl SD_111b8
      getr_resolve; rw [h10, c_ltu_ltb, huk]
      change decide (18446744073709547520 < (k : Int)) = false
      exact decide_eq_false (by omega)
    norm_pc
    stepjr SF_111bc SD_111bc (0x11094 : word) (getr_resolve; rfl)
    chain_step
    · rfl
    · apply step_bge_ft _ _ _ _ _ _ _ _ _ SF_11094 rfl SD_11094
      getr_resolve; rw [h10]
      apply c_lts_0_pos <;> rw [huk] <;> omega
    norm_pc
    mu_sld SF_11098 SD_11098 (Z_to_bv 64 (bv_unsigned rsp - 0x28)) (len_word rest) (exact hcnt)
    mu_sld SF_1109c SD_1109c (Z_to_bv 64 (bv_unsigned rsp - 0x30)) p (exact hptr)
    stepiv SF_110a0 SD_110a0 (len_word (rest.drop k))
      (getr_resolve; rw [h10]; apply v_sub_len_firstn <;> omega)
    stepiv SF_110a4 SD_110a4 (Z_to_bv 64 (bv_unsigned p + (k : Int)))
      (getr_resolve; rw [h10]; apply v_add_len_firstn_Z <;> omega)
    by_cases he : k = rest.length
    · subst k
      rw [List.drop_length]
      chain_step
      · rfl
      · apply step_bne_ft _ _ _ _ _ _ _ _ _ SF_110a8 rfl SD_110a8
        getr_resolve; exact c_eq_0_of_u _ rfl
      norm_pc
      apply twm_tail.twmt_done
      apply source_out_tail rsp Hsp_lo Hsp_hi aG HaAl HaCeil
      · regupd_resolve; rfl
      · regupd_resolve; exact h9
      · exact hmap
      · exact hslra
      · exact hsl
    · chain_step
      · rfl
      · apply step_bne_tk _ _ _ _ _ _ _ _ _ SF_110a8 rfl SD_110a8
        getr_resolve
        apply c_eq_0_false
        rw [u_len_word _ (by rw [List.length_drop]; omega), List.length_drop]
        omega
      norm_pc
      stepiv SF_11084 SD_11084 (Z_to_bv 64 1) (getr_resolve; rfl)
      mu_ssd SF_11088 SD_11088 (Z_to_bv 64 (bv_unsigned rsp - 0x28))
        (len_word (rest.drop k)) (getr_resolve; rfl)
      mu_ssd SF_1108c SD_1108c (Z_to_bv 64 (bv_unsigned rsp - 0x30))
        (Z_to_bv 64 (bv_unsigned p + (k : Int))) (getr_resolve; rfl)
      stepj SF_11090 SD_11090
      stepiv SF_11180 SD_11180 (Z_to_bv 64 (bv_unsigned rsp - 0x40))
        (getr_resolve; sp_norm; congr 1 <;> omega)
      stepiv SF_11184 SD_11184 (len_word (rest.drop k)) (getr_resolve; exact v_addi_0 _)
      stepi SF_11188 SD_11188
      stepiv SF_1118c SD_1118c (Z_to_bv 64 (bv_unsigned p + (k : Int))) (getr_resolve; exact v_addi_0 _)
      stepi SF_11190 SD_11190
      stepiv SF_11194 SD_11194 (Z_to_bv 64 1) (getr_resolve; exact v_addi_0 _)
      stepi SF_11198 SD_11198
      stepiv SF_1119c SD_1119c (Z_to_bv 64 64) (getr_resolve; rfl)
      mu_ssd SF_111a0 SD_111a0 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (0x11094 : word) (getr_resolve; rfl)
      stepj SF_111a4 SD_111a4
      stepj SF_11210 SD_11210
      stepiv SF_111ec SD_111ec (Z_to_bv 64 64) (getr_resolve; exact v_addi_0 _)
      stepiv SF_111f0 SD_111f0 (Z_to_bv 64 1) (getr_resolve; exact v_addi_0 _)
      stepiv SF_111f4 SD_111f4 (Z_to_bv 64 (bv_unsigned p + (k : Int))) (getr_resolve; exact v_addi_0 _)
      stepiv SF_111f8 SD_111f8 (len_word (rest.drop k)) (getr_resolve; exact v_addi_0 _)
      stepi SF_111fc SD_111fc
      stepi SF_11200 SD_11200
      stepi SF_11204 SD_11204
      refine twm_tail.twmt_step _ _ _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11208 rfl) ?_
      apply twm_tail_write_rec
      · getr_resolve; rfl
      · regupd_resolve; rfl
      · regupd_resolve
        rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        have hw : word_to_nat (len_word (rest.drop k)) = (rest.drop k).length :=
          word_to_nat_ntw _ (by rw [List.length_drop]; omega)
        change rdn source_segs _ _ (word_to_nat (len_word (rest.drop k))) = _
        rw [hw]
        repeat rw [rdn_wbytes_below _ _ _ _ _ _
          (by rw [List.length_drop]; u_norm; omega)
          (by rw [length_N_to_le_bytes]; u_norm; omega)]
        have hsk := rdn_skipn source_segs mem rest.length p rest k hread hk2
        rw [word_add_nat_Z _ _ (by omega)] at hsk
        rw [List.length_drop]
        exact hsk
      · rw [List.length_drop]; omega
      · intro m hm1 hm2
        norm_pc
        apply ih (rest.drop k) (Z_to_bv 64 (bv_unsigned p + (k : Int))) m
        · rw [List.length_drop]; omega
        · exact hm1
        · exact hm2
        · rw [List.length_drop]; omega
        · u_norm; omega
        · rw [List.length_drop]; u_norm; omega
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; exact h9
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · mu_grows
        · exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)
        · rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact hslra
        · intro aa haa
          have hab : bv_unsigned rsp - 0x20 ≤ bv_unsigned aa ∧ bv_unsigned aa + 8 ≤ bv_unsigned rsp - 8 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at haa
            rcases haa with rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
          repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
          exact hsl aa haa
        · repeat rw [rdn_wbytes_below _ _ _ _ _ _
            (by rw [List.length_drop]; u_norm; omega)
            (by rw [length_N_to_le_bytes]; u_norm; omega)]
          have hsk := rdn_skipn source_segs mem rest.length p rest k hread hk2
          rw [word_add_nat_Z _ _ (by omega)] at hsk
          rw [List.length_drop]
          exact hsk


include Hva Hve Hsp_lo Hsp_hi HaPos HaAl HaCeil H2av Hnle in
theorem source_succ_twm (model : Model) (regs : bvmap 5 word)
    (hr1 : reg_get regs 1 = (0x11058 : word))
    (hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (hr8 : reg_get regs 8 = nN inp) (hr18 : reg_get regs 18 = P inp rsp)
    (hmap : map_has (m_vmmaps model).vm_maps aG (Z_to_bv 64 4096) = true) :
    twm source_segs (mkst (regupd regs 10 aG) 0x1117c
      (zfill aG (Z_to_bv 64 4096) (fmem inp rsp rrnd)) rrom)
      model [out_buf s] (Z_to_bv 64 0) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have hnn := nN_le inp Hnle
  simp only [List.getD_eq_getElem?_getD] at hnn
  have har := u64_range aG
  sym_block source_segs 7 [false] [] [(0, ELit 0), (1, ELit 0x11058), (10, EVar 32)] [aG] [] RA HRA
  · exact c_lts_pos_0 aG (by omega)
  · getr_resolve; rfl
  · getr_resolve; regupd_resolve; exact hr1
  · getr_resolve; regupd_resolve; rfl
  · obtain ⟨regsC, hfrC, h12C, hmsC⟩ := source_copy inp rsp rrnd Hva Hve Hsp_lo Hsp_hi aG HaCeil H2av Hnle n 0 RA
      (by sym_regs HRA; getr_resolve; regupd_resolve; exact hr18)
      (by sym_regs HRA; getr_resolve; regupd_resolve; exact hr8)
      (by sym_regs HRA; exact v_addi_0 _)
      (by sym_regs HRA; rfl)
      (by sym_regs HRA; rfl) (by omega) (by omega)
    apply msteps_twm _ _ _ _ _ _ hmsC
    have hc2 : reg_get regsC 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) := by
      rw [hfrC 2 (by decide) (by decide) (by decide) (by decide)]
      sym_regs HRA; getr_resolve; regupd_resolve; exact hr2
    have hc9 : reg_get regsC 9 = aG := by
      rw [hfrC 9 (by decide) (by decide) (by decide) (by decide)]
      sym_regs HRA; exact v_addi_0 _
    have hc11 : reg_get regsC 11 = aG := by
      rw [hfrC 11 (by decide) (by decide) (by decide) (by decide)]
      sym_regs HRA; exact v_addi_0 _
    have hgrow : mem_grows (rwmem inp rsp rrnd) (wbytes (zmem inp rsp rrnd aG) aG (out_buf s)) :=
      mem_grows_trans _ _ _ (grows_zmem inp rsp rrnd aG) (wbytes_grows _ _ _)
    sym_block source_segs 22 [] [] [(2, EVar 32), (12, EVar 33), (11, EVar 34)]
      [Z_to_bv 64 (bv_unsigned rsp - 0x30), nat_to_word (n + 1), aG] [] RB HRB
    · repeat' apply And.intro
      all_goals first | omega | rfl | solve_store_ok_inv
    · getr_resolve; exact hc2
    · getr_resolve; exact h12C
    · getr_resolve; exact hc11
    · refine twm.twm_step _ _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11208 rfl) ?_
      apply twm_write_ret
      · sym_regs HRB; rfl
      · sym_regs HRB; rfl
      · rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        sym_regs HRB
        change rdn source_segs _ (v_addi aG 0) (word_to_nat (v_addi (nat_to_word (n + 1)) 0)) = _
        rw [v_addi_0, v_addi_0, word_to_nat_ntw _ (by omega)]
        rw [← length_out_buf s]
        repeat rw [rdn_wbytes_below _ _ _ _ _ _
          (by rw [length_out_buf]; u_norm; omega)
          (by rw [length_N_to_le_bytes]; u_norm; omega)]
        exact rdn_wbytes_hit _ _ _ _ (by rw [length_out_buf]; omega)
      · rw [length_out_buf]; omega
      · intro k hk1 hk2
        norm_pc
        have eln : len_word (out_buf s) = nat_to_word (n + 1) := by
          unfold len_word nat_to_word; rw [length_out_buf]
        apply src_put_wall inp rsp rrnd Hsp_lo Hsp_hi aG HaAl HaCeil model (out_buf s).length (out_buf s) aG k
        · omega
        · exact hk1
        · exact hk2
        · rw [length_out_buf]; omega
        · exact HaPos
        · rw [length_out_buf]; omega
        · regupd_resolve; sym_regs HRB <;> sym_close
        · regupd_resolve; sym_regs HRB <;> sym_close
        · regupd_resolve; sym_regs HRB; getr_resolve; exact hc9
        · regupd_resolve; rfl
        · regupd_resolve; sym_regs HRB; rfl
        · exact hmap
        · solve_mem_grows
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)
        · rw [eln]
          repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by first | rw [length_N_to_le_bytes]; u_norm; omega | rw [length_out_buf]; u_norm; omega)
            (by u_norm; omega)]
          unfold zmem
          rw [rdn_zfill_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
          exact fread_slot_ra inp rsp rrnd Hsp_lo Hsp_hi
        · intro aa haa
          have hab : bv_unsigned rsp - 0x20 ≤ bv_unsigned aa ∧ bv_unsigned aa + 8 ≤ bv_unsigned rsp - 8 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at haa
            rcases haa with rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
          repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by first | rw [length_N_to_le_bytes]; u_norm; omega | rw [length_out_buf]; u_norm; omega)
            (by omega)]
          unfold zmem
          rw [rdn_zfill_out _ _ _ _ _ _ (by omega) (by right; u_norm; omega)]
          exact fread_slot_0 inp rsp rrnd Hsp_lo Hsp_hi aa haa
        · repeat rw [rdn_wbytes_below _ _ _ _ _ _
            (by rw [length_out_buf]; u_norm; omega)
            (by rw [length_N_to_le_bytes]; u_norm; omega)]
          exact rdn_wbytes_hit _ _ _ _ (by rw [length_out_buf]; omega)

end SourceSucc


include Hva Hve Hsp_lo Hsp_hi in
theorem source_tmw (rbrk rmb : word) (h2 : 2 ≤ (av).length) (hn : n ≤ 4095) :
    tmw source_segs
      (init_machine_state source_segs 0x11128 source_phdrs rsp rrnd av ev (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      [] (Z_to_bv 64 4) [out_buf s] (Z_to_bv 64 0) := by
  obtain ⟨regsE, he1, he2, he8, he18, he11, he12, he13, he14, he15, he17, hms⟩ :=
    source_to_mmap inp rsp rrnd Hva Hve Hsp_lo Hsp_hi h2 hn
  apply msteps_tmw _ _ _ _ _ _ _ _ hms
  apply tmw_mmap_rec
  · exact he17
  · rw [he11]; decide
  · exact he12
  · exact he13
  · rw [he14]; rfl
  · exact he15
  · intro e hin
    obtain ⟨he1', he2'⟩ := mmap_errno_range e hin
    norm_pc
    exact source_fail_twm inp rsp rrnd Hsp_lo Hsp_hi _ regsE e he1' he2' he1 he2
  · intro aa hg
    rw [he11] at hg
    change grant_ok _ _ aa (page_round_up_Z 4096) = true at hg
    rw [page_round_up_Z_4096] at hg
    rw [he11, pru_4096]
    obtain ⟨hpos, hal, hceil, hda, hdb, hdc⟩ := source_grant_unpack inp _ rbrk rmb rsp aa hg
    norm_pc
    apply source_succ_twm inp rsp rrnd Hva Hve Hsp_lo Hsp_hi aa hpos hal hceil h2 hn _ regsE he1 he2 he8 he18
    change (bv_eqb aa aa && bv_eqb (Z_to_bv 64 4096) (Z_to_bv 64 4096) || false) = true
    rw [LinuxProcessSemantics.Common.PropExec.bv_eqb_refl, LinuxProcessSemantics.Common.PropExec.bv_eqb_refl]
    rfl
  · rw [he11]
    change ∃ aa, grant_ok _ _ aa (page_round_up_Z 4096) = true
    rw [page_round_up_Z_4096]
    exact ⟨Z_to_bv 64 0x2aaaaab000, source_grant_witness inp _ rbrk rmb rsp Hsp_lo⟩

end SourceProof

end LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_source
