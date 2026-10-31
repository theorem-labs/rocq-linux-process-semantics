import LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_defs
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Common.SymTac

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
-/

/-! Proof-side twin of `theories/Examples/mmap_upper_ns/mmap_upper_ns_target.v`.
Rocq section parameters are explicit Lean section variables; byte strings use
`List byte`, with `getD`, `take`, and `drop` for `nth`, `firstn`, and `skipn`.
Symbolic blocks use Common's checked executor, and the string, copy, and
partial-write loops retain their fuel inductions and register-frame claims.
-/

namespace LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_target

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
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymSide
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Examples.mmap_upper_ns.TargetMemImage
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_code
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001158 := rfl

theorem target_avoids_high (a n : Int) (ha : 0x1002000 ≤ a) :
    range_avoids_ro_segs target_segs a n = true := by
  change ((false || !(decide (0x1000000 < a + n) && decide (a < 0x1001000))) &&
    ((false || !(decide (0x1001000 < a + n) && decide (a < 0x1002000))) && true)) = true
  have h0 : decide (a < 0x1001000) = false := by simp only [decide_eq_false_iff_not]; omega
  have h1 : decide (a < 0x1002000) = false := by simp only [decide_eq_false_iff_not]; omega
  simp only [h0, h1, Bool.and_false, Bool.not_false, Bool.or_true, Bool.and_true]

theorem target_reserved_val : segments_reserved target_segs =
    [(Z_to_bv 64 0x1000000, Z_to_bv 64 0x1000),
     (Z_to_bv 64 0x1001000, Z_to_bv 64 0x1000)] := by decide

theorem target_grant_avoids (aGZ x k : Int)
    (hda : aGZ + 4096 ≤ 0x1000000 ∨ 0x1001000 ≤ aGZ)
    (hdb : aGZ + 4096 ≤ 0x1001000 ∨ 0x1002000 ≤ aGZ)
    (hx1 : aGZ ≤ x) (hx2 : x + k ≤ aGZ + 4096) :
    range_avoids_ro_segs target_segs x k = true := by
  change ((false || !(decide (0x1000000 < x + k) && decide (x < 0x1001000))) &&
    ((false || !(decide (0x1001000 < x + k) && decide (x < 0x1002000))) && true)) = true
  simp only [Bool.false_or, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem v_srl_12 (x : word) : v_srl x (Z_to_bv 64 12) = v_srli x 12 := rfl

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

section TargetProof
variable (inp : ProcInput) (asp : word) (arnd : EntryDraw)
variable (Hva : valid_argv inp.in_argv) (Hve : valid_envp inp.in_envp)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)

 include Hsp_lo in
theorem asp_lo_num : 0x7fff80000000 ≤ bv_unsigned asp := Hsp_lo
 include Hsp_hi in
theorem asp_hi_num : bv_unsigned asp ≤ 0x800000000000 := Hsp_hi

def targcN : word := len_word inp.in_argv
def awmem : word → Option byte :=
  wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd
def arom : word → Option byte := seg_rom target_segs

include Hva in
theorem u_targcN : bv_unsigned (targcN inp) = (inp.in_argv.length : Int) := by
  have h := valid_argv_len inp.in_argv Hva
  exact u_Z2bv _ (by omega) (by omega)

include Hva Hve Hsp_hi in
theorem target_bsb_nw : bv_unsigned asp +
    ((build_stack_bytes target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd).length : Int)
      < 2 ^ 64 := by
  have h := bsb_bound target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd Hva Hve
  have hi := asp_hi_num asp Hsp_hi
  omega

def smem : word → Option byte :=
  wbytes (wbytes (awmem inp asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))
def tfmem : word → Option byte :=
  wbytes (wbytes (smem inp asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 24)) (word_to_le_bytes 8 (0x1001178 : word)))
    (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 asp)
def tnN : word := nat_to_word (inp.in_argv.getD 1 []).length
def tP : word := cat_argv_ptr asp inp.in_argv inp.in_envp 1

theorem rdn_awmem_stack (a : word) (k : Nat)
    (ha : bv_unsigned asp ≤ bv_unsigned a) (hnw : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn target_segs (awmem inp asp arnd) a k =
      rdn target_segs (stack_to_mem asp
        (entry_stack_image target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd)) a k :=
  rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ ha hnw

include Hsp_lo Hsp_hi in
theorem rdn_smem_above (a : word) (k : Nat)
    (ha : bv_unsigned asp ≤ bv_unsigned a) (hnw : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn target_segs (smem inp asp arnd) a k = rdn target_segs (awmem inp asp arnd) a k := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  unfold smem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) hnw,
      rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) hnw]

include Hsp_lo Hsp_hi in
theorem rdn_tfmem_above (a : word) (k : Nat)
    (ha : bv_unsigned asp ≤ bv_unsigned a) (hnw : bv_unsigned a + (k : Int) ≤ 2 ^ 64) :
    rdn target_segs (tfmem inp asp arnd) a k = rdn target_segs (awmem inp asp arnd) a k := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) hnw,
      rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) hnw]
  exact rdn_smem_above inp asp arnd Hsp_lo Hsp_hi a k ha hnw

include Hva Hve Hsp_hi in
theorem target_ptr_bounds (h2 : 2 ≤ inp.in_argv.length) :
    bv_unsigned asp ≤ bv_unsigned (tP inp asp) ∧
    bv_unsigned (tP inp asp) + ((inp.in_argv.getD 1 []).length : Int) + 1 < 2 ^ 64 := by
  apply argv_ptr_bounds asp inp.in_argv inp.in_envp 1 Hva Hve (by omega)
  have hi := asp_hi_num asp Hsp_hi
  unfold argv_layout_slack
  omega

include Hva Hve Hsp_lo Hsp_hi in
theorem tread_str_byte (j : Nat) (h2 : 2 ≤ inp.in_argv.length)
    (hj : j ≤ (inp.in_argv.getD 1 []).length) :
    rdn target_segs (tfmem inp asp arnd) (tP inp asp + nat_to_word j) 1 =
      some [byte_at (inp.in_argv.getD 1 []) j] := by
  obtain ⟨hge, hup⟩ := target_ptr_bounds inp asp Hva Hve Hsp_hi h2
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  rw [rdn_tfmem_above inp asp arnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_awmem_stack inp asp arnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_byte_k _ _ _ _ _ _ _ _ _ _ (by omega) hj
    (target_bsb_nw inp asp arnd Hva Hve Hsp_hi)

include Hsp_lo Hsp_hi in
theorem tfread_slot_ra :
    rdn target_segs (tfmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x1001178 : word)) := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  unfold tfmem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
  exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)

include Hsp_lo Hsp_hi in
theorem tfread_slot_s0 :
    rdn target_segs (tfmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp) := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  exact rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)

include Hsp_lo Hsp_hi in
theorem target_epilogue (regs : bvmap 5 word) (mem : word → Option byte) (code : word)
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (h10 : reg_get regs 10 = code)
    (hra : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8 =
      some (word_to_le_bytes 8 (0x1001178 : word)))
    (hs0 : rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8 =
      some (word_to_le_bytes 8 asp)) :
    ∃ regs', bv_unsigned (getr regs' 17) = 93 ∧ reg_get regs' 10 = code ∧
      msteps target_segs (mkst regs 0x1001274 mem arom)
        { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := 0x100117c,
          ms_svc_pending := some (getr regs' 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := arom } := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x1001274) mem arom)
    6 [] [ELit 0x1001178] [(2, EVar 32)] [Z_to_bv 64 (bv_unsigned asp - 32)]
    [Z_to_bv 64 0, asp] R HR Hms
  · repeat' apply And.intro
    all_goals first
      | exact ⟨word_to_le_bytes 8 asp, hs0, bytes_le_to_Z_8 asp⟩
      | exact ⟨word_to_le_bytes 8 (0x1001178 : word), hra, bytes_le_to_Z_8 _⟩
      | (u_norm; omega)
  · exact h2
  · refine ⟨R, ?_, ?_, ?_⟩
    · sym_regs HR; rfl
    · sym_regs HR
      rw [getr_nz _ _ (by decide)]
      exact h10
    · apply msteps_trans _ _ _ _ Hms
      norm_pc; sym_pc_lit
      exact msteps.mst_step _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_100117c (by decide)) (msteps.mst_refl _)

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_lt2 (hlt2 : inp.in_argv.length < 2) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 2) := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  have hlen := valid_argv_len inp.in_argv Hva
  have hu := u_targcN inp Hva
  rw [init_mkst]
  norm_pc
  sym_block target_segs 14 [false] []
    [(1, ELit 0), (8, ELit 0), (2, EVar 32)] [asp] [targcN inp] RA HRA
  · repeat' apply And.intro
    all_goals first
      | sym_br
      | solve_store_ok
      | (rw [show Z_to_bv 64 (bv_unsigned asp + 0) = asp from v_addi_0 asp]
         refine ⟨word_le8 (targcN inp), ?_, bytes_le_n_to_le_8 _⟩
         rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
         exact read_argc _ _ _ _ _ _ _ _ (target_bsb_nw inp asp arnd Hva Hve Hsp_hi))
  · getr_resolve; rfl
  · getr_resolve; rfl
  · getr_resolve; rfl
  · apply to_wexit.tw_step _ _ _ _ rfl
      (step_ecall _ _ _ _ _ _ TF_100117c (by decide))
    apply tw_exit_coden
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · decide

include Hva Hve Hsp_lo Hsp_hi in
theorem target_prologue (h2 : 2 ≤ inp.in_argv.length) :
    ∃ regsP,
      (reg_get regsP 2 = Z_to_bv 64 (bv_unsigned asp - 32) ∧
       reg_get regsP 8 = tP inp asp ∧ reg_get regsP 10 = tP inp asp ∧
       reg_get regsP 1 = (0x10011ac : word) ∧ reg_get regsP 11 = Z_to_bv 64 0) ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regsP 0x1001288 (tfmem inp asp arnd) arom) := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  have hlen := valid_argv_len inp.in_argv Hva
  have hu := u_targcN inp Hva
  rw [init_mkst]
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
      (Z_to_bv 64 0x1001158)
      (wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd)
      (seg_rom target_segs))
    18 [true] [] [(1, ELit 0), (8, ELit 0), (2, EVar 32)] [asp]
    [targcN inp, tP inp asp] RA HRA Hms
  · repeat' apply And.intro
    all_goals first
      | sym_br
      | solve_store_ok
      | (rw [show Z_to_bv 64 (bv_unsigned asp + 0) = asp from v_addi_0 asp]
         refine ⟨word_le8 (targcN inp), ?_, bytes_le_n_to_le_8 _⟩
         rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
         exact read_argc _ _ _ _ _ _ _ _ (target_bsb_nw inp asp arnd Hva Hve Hsp_hi))
      | (rw [show Z_to_bv 64 (bv_unsigned asp + 16) = asp + nat_to_word (8 + 8 * 1) from
              (word_add_nat asp 16).symm]
         refine ⟨word_le8 (tP inp asp), ?_, bytes_le_n_to_le_8 _⟩
         rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _
           (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
         exact read_argv_ptr_k _ _ _ _ _ _ _ _ _ (by omega)
           (target_bsb_nw inp asp arnd Hva Hve Hsp_hi))
  · getr_resolve; rfl
  · getr_resolve; rfl
  · getr_resolve; rfl
  · refine ⟨RA, ?_, ?_⟩
    · repeat' apply And.intro
      all_goals sym_regs HRA <;> first | rfl | exact v_addi_0 _
    · unfold tfmem smem awmem arom
      revert Hms
      sym_mem_norm
      exact fun h => h

include Hva Hve Hsp_lo Hsp_hi in
theorem target_slen (h2 : 2 ≤ inp.in_argv.length) (f j : Nat) (regs : bvmap 5 word)
    (h10 : reg_get regs 10 = tP inp asp) (h11 : reg_get regs 11 = nat_to_word j)
    (hj : j ≤ (inp.in_argv.getD 1 []).length)
    (hf : (inp.in_argv.getD 1 []).length - j ≤ f) :
    ∃ regs',
      (∀ r : reg, r ≠ 11 → r ≠ 12 → reg_get regs' r = reg_get regs r) ∧
      reg_get regs' 11 = nat_to_word ((inp.in_argv.getD 1 []).length + 1) ∧
      msteps target_segs (mkst regs 0x1001288 (tfmem inp asp arnd) arom)
        (mkst regs' 0x1001298 (tfmem inp asp arnd) arom) := by
  have hn := valid_argv_str_len inp.in_argv 1 Hva (by omega)
  have hnz := valid_argv_str_nz inp.in_argv 1 Hva (by omega)
  have body (j : Nat) (regs : bvmap 5 word)
      (h10 : reg_get regs 10 = tP inp asp) (h11 : reg_get regs 11 = nat_to_word j)
      (hj : j ≤ (inp.in_argv.getD 1 []).length) :
      msteps target_segs (mkst regs 0x1001288 (tfmem inp asp arnd) arom)
        (mkst (regupd (regupd (regupd regs 12 (tP inp asp + nat_to_word j))
          12 (Z_to_bv 64 (bv_unsigned (byte_at (inp.in_argv.getD 1 []) j))))
          11 (nat_to_word (j + 1))) 0x1001294 (tfmem inp asp arnd) arom) := by
    stepiv TF_1001288 TD_1001288 (tP inp asp + nat_to_word j)
      (getr_resolve; rw [h10, h11]; rfl)
    refine msteps.mst_step _ _ _ rfl
      (step_lbu _ _ _ _ _ _ _ _ _ (byte_at (inp.in_argv.getD 1 []) j)
        TF_100128c (by decide) TD_100128c ?_) ?_
    · getr_resolve
      imm_norm
      rw [v_addi_0]
      exact tread_str_byte inp asp arnd Hva Hve Hsp_lo Hsp_hi j h2 hj
    · reduce_bv_eqb_ifs; norm_pc
      stepiv TF_1001290 TD_1001290 (nat_to_word (j + 1))
        (getr_resolve; rw [h11]; exact v_addi_Sj j (by omega))
      exact msteps.mst_refl _
  induction f generalizing j regs with
  | zero =>
    have heq : j = (inp.in_argv.getD 1 []).length := by omega
    refine ⟨regupd (regupd (regupd regs 12 (tP inp asp + nat_to_word j))
          12 (Z_to_bv 64 (bv_unsigned (byte_at (inp.in_argv.getD 1 []) j))))
          11 (nat_to_word (j + 1)), ?_, ?_, msteps_trans _ _ _ _ (body j regs h10 h11 hj) ?_⟩
    · intro r hr11 hr12
      simp only [regupd_other _ _ _ _ hr11, regupd_other _ _ _ _ hr12]
    · rw [regupd_same, heq]
    · refine msteps.mst_step _ _ _ rfl
        (step_bne_ft _ _ _ _ _ _ _ _ _ TF_1001294 (by decide) TD_1001294 ?_) ?_
      · getr_resolve
        rw [heq, byte_at_len]
        exact c_eq_0_true
      · norm_pc; exact msteps.mst_refl _
  | succ f ih =>
    by_cases heq : j = (inp.in_argv.getD 1 []).length
    · refine ⟨regupd (regupd (regupd regs 12 (tP inp asp + nat_to_word j))
          12 (Z_to_bv 64 (bv_unsigned (byte_at (inp.in_argv.getD 1 []) j))))
          11 (nat_to_word (j + 1)), ?_, ?_, msteps_trans _ _ _ _ (body j regs h10 h11 hj) ?_⟩
      · intro r hr11 hr12
        simp only [regupd_other _ _ _ _ hr11, regupd_other _ _ _ _ hr12]
      · rw [regupd_same, heq]
      · refine msteps.mst_step _ _ _ rfl
          (step_bne_ft _ _ _ _ _ _ _ _ _ TF_1001294 (by decide) TD_1001294 ?_) ?_
        · getr_resolve
          rw [heq, byte_at_len]
          exact c_eq_0_true
        · norm_pc; exact msteps.mst_refl _
    · let r3 := regupd (regupd (regupd regs 12 (tP inp asp + nat_to_word j))
          12 (Z_to_bv 64 (bv_unsigned (byte_at (inp.in_argv.getD 1 []) j))))
          11 (nat_to_word (j + 1))
      obtain ⟨regs', hfr, h11f, hms⟩ := ih (j + 1) r3
        (by unfold r3; regupd_resolve; exact h10)
        (by unfold r3; regupd_resolve; rfl) (by omega) (by omega)
      refine ⟨regs', ?_, h11f, msteps_trans _ _ _ _ (body j regs h10 h11 hj) ?_⟩
      · intro r hr11 hr12
        rw [hfr r hr11 hr12]
        simp only [r3, regupd_other _ _ _ _ hr11, regupd_other _ _ _ _ hr12]
      · refine msteps.mst_step _ _ _ rfl
          (step_bne_tk _ _ _ _ _ _ _ _ _ TF_1001294 (by decide) TD_1001294 ?_) ?_
        · getr_resolve
          apply c_eq_0_false
          rw [u_zext8]
          exact byte_nz_u _ (byte_at_nz _ _ hnz (by omega))
        · norm_pc; exact hms

include Hva Hve Hsp_lo Hsp_hi in
theorem target_after_slen (h2 : 2 ≤ inp.in_argv.length) :
    ∃ regsA,
      (reg_get regsA 2 = Z_to_bv 64 (bv_unsigned asp - 32) ∧
       reg_get regsA 8 = tP inp asp ∧ reg_get regsA 10 = tnN inp) ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regsA 0x10011ac (tfmem inp asp arnd) arom) := by
  have hn := valid_argv_str_len inp.in_argv 1 Hva (by omega)
  obtain ⟨regsP, ⟨hp2, hp8, hp10, hp1, hp11⟩, hmsP⟩ :=
    target_prologue inp asp arnd Hva Hve Hsp_lo Hsp_hi h2
  obtain ⟨regsL, hfr, h11, hmsL⟩ :=
    target_slen inp asp arnd Hva Hve Hsp_lo Hsp_hi h2
      (inp.in_argv.getD 1 []).length 0 regsP hp10 (by rw [hp11]; rfl) (by omega) (by omega)
  refine ⟨regupd regsL 10 (tnN inp), ?_, ?_⟩
  · refine ⟨?_, ?_, regupd_same _ _ _⟩
    · regupd_resolve; rw [hfr 2 (by decide) (by decide)]; exact hp2
    · regupd_resolve; rw [hfr 8 (by decide) (by decide)]; exact hp8
  · apply msteps_trans _ _ _ _ hmsP
    apply msteps_trans _ _ _ _ hmsL
    stepiv TF_1001298 TD_1001298 (tnN inp)
      (getr_resolve; rw [h11]; imm_norm; exact v_addi_ntw_pred _ (by omega))
    stepjr TF_100129c TD_100129c (0x10011ac : word)
      (getr_resolve; rw [hfr 1 (by decide) (by decide)]; exact hp1)
    exact msteps.mst_refl _

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_len3 (h2 : 2 ≤ inp.in_argv.length)
    (hn : 4095 < (inp.in_argv.getD 1 []).length) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 3) := by
  have hlen := valid_argv_str_len inp.in_argv 1 Hva (by omega)
  obtain ⟨regsA, ⟨ha2, ha8, ha10⟩, hms⟩ :=
    target_after_slen inp asp arnd Hva Hve Hsp_lo Hsp_hi h2
  apply msteps_to_wexit _ _ _ _ _ hms
  sym_block target_segs 5 [false] [] [(0, ELit 0), (10, EVar 32)] [tnN inp] [] RA HRA
  · rw [v_srl_12]
    apply c_eq_0_false
    rw [v_srli_div _ _ (by omega), tnN, u_ntw _ (by omega)]
    change ((inp.in_argv.getD 1 []).length : Int) / 4096 ≠ 0
    omega
  · getr_resolve; rfl
  · getr_resolve; exact ha10
  · obtain ⟨regsE, he17, he10, hmse⟩ := target_epilogue asp Hsp_lo Hsp_hi RA
      (tfmem inp asp arnd) (Z_to_bv 64 3)
      (by sym_regs HRA; getr_resolve; exact ha2)
      (by sym_regs HRA; rfl)
      (tfread_slot_ra inp asp arnd Hsp_lo Hsp_hi)
      (tfread_slot_s0 inp asp arnd Hsp_lo Hsp_hi)
    exact msteps_to_wexit _ _ _ _ _ hmse (tw_exit_coden _ _ _ _ _ _ he17 he10 (by decide))

include Hsp_lo Hsp_hi in
theorem target_fail_twm (model : Model) (regs : bvmap 5 word) (e : Int)
    (he1 : 1 ≤ e) (he2 : e ≤ 4095)
    (hr2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32)) :
    twm target_segs (mkst (regupd regs 10 (errno_ret e)) 0x10011dc (tfmem inp asp arnd) arom)
      model [] (Z_to_bv 64 4) := by
  obtain ⟨her1, her2⟩ := errno_ret_range e he1 he2
  sym_block target_segs 3 [true] [] [(0, ELit 0), (10, EVar 32)] [errno_ret e] [] RA HRA
  · exact c_lts_neg_0 _ (by omega)
  · getr_resolve; rfl
  · getr_resolve; rfl
  · obtain ⟨regsE, he17, he10, hmse⟩ := target_epilogue asp Hsp_lo Hsp_hi RA
      (tfmem inp asp arnd) (Z_to_bv 64 4)
      (by sym_regs HRA; getr_resolve; exact hr2)
      (by sym_regs HRA; rfl)
      (tfread_slot_ra inp asp arnd Hsp_lo Hsp_hi)
      (tfread_slot_s0 inp asp arnd Hsp_lo Hsp_hi)
    exact msteps_twm _ _ _ _ _ _ hmse (twm_exit_coden _ _ _ _ _ _ _ he17 he10 (by decide))

include Hva Hve Hsp_lo Hsp_hi in
theorem target_to_mmap (h2 : 2 ≤ inp.in_argv.length)
    (hn : (inp.in_argv.getD 1 []).length ≤ 4095) :
    ∃ regsE,
      reg_get regsE 2 = Z_to_bv 64 (bv_unsigned asp - 32) ∧
      reg_get regsE 8 = tP inp asp ∧ reg_get regsE 16 = tnN inp ∧
      reg_get regsE 11 = Z_to_bv 64 4096 ∧ reg_get regsE 12 = Z_to_bv 64 3 ∧
      reg_get regsE 13 = Z_to_bv 64 34 ∧ reg_get regsE 14 = Z_to_bv 64 (2 ^ 64 - 1) ∧
      reg_get regsE 15 = Z_to_bv 64 0 ∧ bv_unsigned (getr regsE 17) = 222 ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        { ms_regs := regsE, ms_fregs := bvmap_empty, ms_pc_val := 0x10011d8,
          ms_svc_pending := some (getr regsE 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := tfmem inp asp arnd, ms_rom := arom } := by
  obtain ⟨regsA, ⟨ha2, ha8, ha10⟩, hmsa⟩ :=
    target_after_slen inp asp arnd Hva Hve Hsp_lo Hsp_hi h2
  sym_block_ex target_segs (mkst regsA (Z_to_bv 64 0x10011ac) (tfmem inp asp arnd) arom)
    9 [true] [] [(0, ELit 0), (10, EVar 32)] [tnN inp] [] RA HRA Hms
  · rw [v_srl_12]
    apply c_eq_0_of_u
    rw [v_srli_div _ _ (by omega), tnN, u_ntw _ (by omega)]
    change ((inp.in_argv.getD 1 []).length : Int) / 4096 = 0
    omega
  · getr_resolve; rfl
  · getr_resolve; exact ha10
  · refine ⟨RA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_regs HRA; getr_resolve; exact ha2
    · sym_regs HRA; getr_resolve; exact ha8
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · sym_regs HRA; first | rfl | exact v_addi_0 _
    · apply msteps_trans _ _ _ _ hmsa
      apply msteps_trans _ _ _ _ Hms
      norm_pc; sym_pc_lit
      exact msteps.mst_step _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_10011d8 (by decide)) (msteps.mst_refl _)

section TargetSucc
variable (aG : word)
variable (HaPos : 0 < bv_unsigned aG) (HaAl : bv_unsigned aG % page_size = 0)
variable (HaCeil : bv_unsigned aG + 4096 ≤ bv_unsigned asp - stack_max_size)
variable (Hda : bv_unsigned aG + 4096 ≤ 0x1000000 ∨ 0x1001000 ≤ bv_unsigned aG)
variable (Hdb : bv_unsigned aG + 4096 ≤ 0x1001000 ∨ 0x1002000 ≤ bv_unsigned aG)
variable (H2av : 2 ≤ inp.in_argv.length) (Hnle : (inp.in_argv.getD 1 []).length ≤ 4095)

include Hnle in
theorem tnN_le : ((inp.in_argv.getD 1 []).length : Int) ≤ 4095 := by omega

def zmemT : word → Option byte := zfill aG (Z_to_bv 64 4096) (tfmem inp asp arnd)
def cmemT (i : Nat) : word → Option byte :=
  wbytes (zmemT inp asp arnd aG) aG (upperv ((inp.in_argv.getD 1 []).take i))

theorem tcmem_S (i : Nat) (hi : i < (inp.in_argv.getD 1 []).length) :
    cmemT inp asp arnd aG (i + 1) =
      wbytes (cmemT inp asp arnd aG i) (aG + nat_to_word i)
        [upperb (byte_at (inp.in_argv.getD 1 []) i)] := by
  unfold cmemT
  rw [upperv_firstn_S _ _ hi, wbytes_snoc, length_upperv_firstn _ _ (by omega)]

include Hva Hve Hsp_lo Hsp_hi HaCeil H2av Hnle in
theorem tcread_str_byte (i j : Nat) (hi : i ≤ (inp.in_argv.getD 1 []).length)
    (hj : j ≤ (inp.in_argv.getD 1 []).length) :
    rdn target_segs (cmemT inp asp arnd aG i) (tP inp asp + nat_to_word j) 1 =
      some [byte_at (inp.in_argv.getD 1 []) j] := by
  obtain ⟨hge, hup⟩ := target_ptr_bounds inp asp Hva Hve Hsp_hi H2av
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  have hceil := HaCeil
  unfold stack_max_size at hceil
  unfold cmemT
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_upperv_firstn _ _ hi, word_add_nat]; u_norm; omega)
    (by rw [word_add_nat]; u_norm; omega)]
  unfold zmemT
  rw [rdn_zfill_out _ _ _ _ _ _ (by rw [word_add_nat]; u_norm; omega)
    (by right; rw [word_add_nat]; u_norm; omega)]
  exact tread_str_byte inp asp arnd Hva Hve Hsp_lo Hsp_hi j H2av hj

include Hsp_hi HaCeil in
theorem tgrant_store_ok (m : word → Option byte) (a : word) (k : Nat)
    (hx1 : bv_unsigned aG ≤ bv_unsigned a)
    (hx2 : bv_unsigned a + (k : Int) ≤ bv_unsigned aG + 4096) :
    store_ok target_segs (zfill aG (Z_to_bv 64 4096) m) a k = true := by
  have hhi := asp_hi_num asp Hsp_hi
  have hceil := HaCeil
  unfold stack_max_size at hceil
  apply store_ok_zmem
  · omega
  · exact hx1
  · exact hx2

include Hva Hve Hsp_lo Hsp_hi HaCeil H2av Hnle in
theorem target_copy (f i : Nat) (regs : bvmap 5 word)
    (h8 : reg_get regs 8 = tP inp asp + nat_to_word i)
    (h10 : reg_get regs 10 = aG + nat_to_word i)
    (h11 : reg_get regs 11 = nat_to_word ((inp.in_argv.getD 1 []).length - i))
    (hi : i < (inp.in_argv.getD 1 []).length)
    (hf : (inp.in_argv.getD 1 []).length - i ≤ f) :
    ∃ regs',
      (∀ r : reg, r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 14 →
        reg_get regs' r = reg_get regs r) ∧
      msteps target_segs (mkst regs 0x10011ec (cmemT inp asp arnd aG i) arom)
        (mkst regs' 0x100121c
          (wbytes (zmemT inp asp arnd aG) aG (upperv (inp.in_argv.getD 1 []))) arom) := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  have hceil := HaCeil
  unfold stack_max_size at hceil
  have har := u64_range aG
  have ems : wbytes (zmemT inp asp arnd aG) aG (upperv (inp.in_argv.getD 1 [])) =
      cmemT inp asp arnd aG (inp.in_argv.getD 1 []).length := by
    unfold cmemT
    rw [List.take_length]
  induction f generalizing i regs with
  | zero => omega
  | succ f ih =>
    let b := byte_at (inp.in_argv.getD 1 []) i
    let fl := if islower b then Z_to_bv 64 1 else Z_to_bv 64 0
    let m1 := if islower b then Z_to_bv 64 (2 ^ 64 - 1) else Z_to_bv 64 0
    let msk := if islower b then Z_to_bv 64 224 else Z_to_bv 64 0
    have efl : v_sltiu (usub97 b) 26 = fl := by
      rw [v_sltiu_26]
      unfold fl
      cases el : islower b with
      | false =>
        have hb := usub97_gt25 b el
        rw [show decide (bv_unsigned (usub97 b) < 26) = false from
          decide_eq_false (by omega)]
      | true =>
        have hb := usub97_le25 b el
        rw [show decide (bv_unsigned (usub97 b) < 26) = true from
          decide_eq_true (by omega)]
    have em1 : v_subw (Z_to_bv 64 0) fl = m1 := by
      unfold fl m1
      cases islower b
      · exact negw_0
      · exact negw_1
    have emsk : v_andi m1 224 = msk := by
      unfold m1 msk
      cases islower b
      · exact andi_0_224
      · exact andi_m1_224
    have estore : Z_to_bv 8 (bv_unsigned (v_add (Z_to_bv 64 (bv_unsigned b)) msk)) =
        upperb b := by
      unfold msk
      cases el : islower b
      · exact target_upper_hi b el
      · exact target_upper_lo b el
    let r1 := regupd regs 12 (Z_to_bv 64 (bv_unsigned b))
    let r2 := regupd r1 11 (nat_to_word ((inp.in_argv.getD 1 []).length - (i + 1)))
    let r3 := regupd r2 8 (tP inp asp + nat_to_word (i + 1))
    let r4 := regupd r3 14 (Z_to_bv 64 (bv_unsigned b - 97))
    let r5 := regupd r4 14 (usub97 b)
    let r6 := regupd r5 14 fl
    let r7 := regupd r6 14 m1
    let r8 := regupd r7 14 msk
    let r9 := regupd r8 12 (v_add (Z_to_bv 64 (bv_unsigned b)) msk)
    let r10 := regupd r9 10 (aG + nat_to_word (i + 1))
    have e7 : step target_segs (mkst r6 0x1001204 (cmemT inp asp arnd aG i) arom) =
        MachineOk (mkst r7 0x1001208 (cmemT inp asp arnd aG i) arom) := by
      rw [step_subw _ _ _ _ _ _ _ _ _ TF_1001204 (by decide) TD_1001204]
      reduce_bv_eqb_ifs
      unfold r7 r6
      getr_resolve
      rw [em1]
      rfl
    have body : msteps target_segs (mkst regs 0x10011ec (cmemT inp asp arnd aG i) arom)
        (mkst r10 0x1001218 (cmemT inp asp arnd aG (i + 1)) arom) := by
      refine msteps.mst_step _ _ _ rfl
        (step_lbu _ _ _ _ _ _ _ _ _ b TF_10011ec (by decide) TD_10011ec ?_) ?_
      · getr_resolve; imm_norm
        rw [h8, v_addi_0]
        exact tcread_str_byte inp asp arnd Hva Hve Hsp_lo Hsp_hi aG HaCeil H2av Hnle i i
          (by omega) (by omega)
      · reduce_bv_eqb_ifs; norm_pc
        stepiv TF_10011f0 TD_10011f0 (nat_to_word ((inp.in_argv.getD 1 []).length - (i + 1)))
          (getr_resolve; rw [h11]; imm_norm
           rw [show (inp.in_argv.getD 1 []).length - i =
             ((inp.in_argv.getD 1 []).length - (i + 1)) + 1 by omega]
           exact v_addi_ntw_pred _ (by omega))
        stepiv TF_10011f4 TD_10011f4 (tP inp asp + nat_to_word (i + 1))
          (getr_resolve; rw [h8]; imm_norm; exact v_addi_word_Sj _ _)
        stepiv TF_10011f8 TD_10011f8 (Z_to_bv 64 (bv_unsigned b - 97))
          (getr_resolve; imm_norm; exact v_addi_byte_m97 b)
        stepiv TF_10011fc TD_10011fc (usub97 b)
          (getr_resolve; imm_norm; exact usub97_andi b)
        stepiv TF_1001200 TD_1001200 fl (getr_resolve; imm_norm; exact efl)
        apply msteps.mst_step _ _ _ rfl e7
        stepiv TF_1001208 TD_1001208 msk
          (unfold r7; getr_resolve; imm_norm; exact emsk)
        stepiv TF_100120c TD_100120c (v_add (Z_to_bv 64 (bv_unsigned b)) msk)
          (unfold r7 r6 r5 r4 r3 r2 r1; getr_resolve; rfl)
        refine msteps.mst_step _ _ _ rfl
          (step_sb_at _ _ _ _ _ _ _ _ _ (aG + nat_to_word i)
            (v_add (Z_to_bv 64 (bv_unsigned b)) msk) (upperb b)
            TF_1001210 (by decide) TD_1001210 ?_ ?_ estore ?_) ?_
        · unfold r7 r6 r5 r4 r3 r2 r1
          getr_resolve; imm_norm
          rw [h10]; exact v_addi_0 _
        · getr_resolve; rfl
        · unfold cmemT
          store_ok_peel
          apply tgrant_store_ok asp Hsp_hi aG HaCeil
          · rw [word_add_nat]; u_norm; omega
          · rw [word_add_nat]; u_norm; omega
        · rw [← tcmem_S inp asp arnd aG i hi]
          norm_pc
          stepiv TF_1001214 TD_1001214 (aG + nat_to_word (i + 1))
            (unfold r7 r6 r5 r4 r3 r2 r1
             getr_resolve; rw [h10]; imm_norm; exact v_addi_word_Sj _ _)
          exact msteps.mst_refl _
    have frame (r : reg) (hr8 : r ≠ 8) (hr10 : r ≠ 10) (hr11 : r ≠ 11)
        (hr12 : r ≠ 12) (hr14 : r ≠ 14) : reg_get r10 r = reg_get regs r := by
      simp only [r10, r9, r8, r7, r6, r5, r4, r3, r2, r1,
        regupd_other _ _ _ _ hr8, regupd_other _ _ _ _ hr10,
        regupd_other _ _ _ _ hr11, regupd_other _ _ _ _ hr12, regupd_other _ _ _ _ hr14]
    have h11' : reg_get r10 11 = nat_to_word ((inp.in_argv.getD 1 []).length - (i + 1)) := by
      unfold r10 r9 r8 r7 r6 r5 r4 r3 r2
      regupd_resolve; rfl
    by_cases heq : i + 1 = (inp.in_argv.getD 1 []).length
    · refine ⟨r10, frame, ?_⟩
      rw [ems, ← heq]
      apply msteps_trans _ _ _ _ body
      refine msteps.mst_step _ _ _ rfl
        (step_bne_ft _ _ _ _ _ _ _ _ _ TF_1001218 (by decide) TD_1001218 ?_) ?_
      · getr_resolve
        rw [heq, Nat.sub_self]
        exact c_eq_0_true
      · norm_pc; exact msteps.mst_refl _
    · obtain ⟨regs', hfr, hms⟩ := ih (i + 1) r10
        (by unfold r10 r9 r8 r7 r6 r5 r4 r3; regupd_resolve; rfl)
        (by unfold r10; regupd_resolve; rfl) h11' (by omega) (by omega)
      refine ⟨regs', fun r h8 h10 h11 h12 h14 =>
        (hfr r h8 h10 h11 h12 h14).trans (frame r h8 h10 h11 h12 h14), ?_⟩
      apply msteps_trans _ _ _ _ body
      refine msteps.mst_step _ _ _ rfl
        (step_bne_tk _ _ _ _ _ _ _ _ _ TF_1001218 (by decide) TD_1001218 ?_) ?_
      · getr_resolve
        apply c_eq_0_false
        rw [u_ntw _ (by omega)]
        omega
      · norm_pc; exact hms

include Hsp_lo Hsp_hi HaAl HaCeil Hnle in
theorem target_out_tail (model : Model) (regs : bvmap 5 word)
    (h2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (h13 : reg_get regs 13 = aG)
    (hmap : map_has (m_vmmaps model).vm_maps aG (Z_to_bv 64 4096) = true) :
    twm target_segs
      (mkst regs 0x1001250 (wbytes (zmemT inp asp arnd aG) aG (out_buf (inp.in_argv.getD 1 []))) arom)
      model [] (Z_to_bv 64 0) := by
  have hlo := asp_lo_num asp Hsp_lo
  have hhi := asp_hi_num asp Hsp_hi
  have hceil := HaCeil
  unfold stack_max_size at hceil
  sym_block target_segs 3 [] [] [(13, EVar 32)] [aG] [] RC HRC
  · getr_resolve; exact h13
  · refine twm.twm_step _ _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_100125c (by decide)) ?_
    apply twm_munmap_rec (a := aG) (nlen := Z_to_bv 64 4096)
    · sym_regs HRC; rfl
    · sym_regs HRC; exact v_addi_0 _
    · sym_regs HRC; rfl
    · exact HaAl
    · decide
    · change bv_unsigned aG + page_round_up_Z 4096 ≤ TASK_SIZE
      rw [page_round_up_Z_4096]
      unfold TASK_SIZE
      omega
    · rw [pru_4096]; exact hmap
    · rw [pru_4096]
      norm_pc
      sym_block target_segs 2 [] [] [] [] [] RD HRD
      obtain ⟨regsE, he17, he10, hmse⟩ := target_epilogue asp Hsp_lo Hsp_hi RD
        (unfill aG (Z_to_bv 64 4096)
          (wbytes (zmemT inp asp arnd aG) aG (out_buf (inp.in_argv.getD 1 [])))) (Z_to_bv 64 0)
        (by sym_regs HRD; getr_resolve; sym_regs HRC; getr_resolve; exact h2r)
        (by sym_regs HRD; rfl)
        (by
          rw [rdn_unfill_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
          rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_out_buf]; u_norm; omega) (by u_norm; omega)]
          unfold zmemT
          rw [rdn_zfill_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
          exact tfread_slot_ra inp asp arnd Hsp_lo Hsp_hi)
        (by
          rw [rdn_unfill_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
          rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_out_buf]; u_norm; omega) (by u_norm; omega)]
          unfold zmemT
          rw [rdn_zfill_out _ _ _ _ _ _ (by u_norm; omega) (by right; u_norm; omega)]
          exact tfread_slot_s0 inp asp arnd Hsp_lo Hsp_hi)
      exact msteps_twm _ _ _ _ _ _ hmse
        (twm_exit_coden _ _ _ _ _ _ _ he17 he10 (by decide))

include Hsp_lo Hsp_hi HaAl HaCeil Hnle in
theorem tgt_put_wall (model : Model) (fuel : Nat) (rest : List byte) (p : word)
    (k : Nat) (regs : bvmap 5 word)
    (hfuel : rest.length ≤ fuel) (hk1 : 1 ≤ k) (hk2 : k ≤ rest.length)
    (hlen : (rest.length : Int) ≤ 4096) (hplo : 0 < bv_unsigned p)
    (hphi : bv_unsigned p + (rest.length : Int) < 2 ^ 64)
    (h2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (h10 : reg_get regs 10 = len_word (rest.take k))
    (h11 : reg_get regs 11 = p) (h12 : reg_get regs 12 = len_word rest)
    (h13 : reg_get regs 13 = aG) (h17 : bv_unsigned (reg_get regs 17) = 64)
    (hmap : map_has (m_vmmaps model).vm_maps aG (Z_to_bv 64 4096) = true)
    (hread : rdn target_segs (wbytes (zmemT inp asp arnd aG) aG (out_buf (inp.in_argv.getD 1 [])))
      p rest.length = some rest) :
    twm_tail target_segs
      (mkst regs 0x1001240 (wbytes (zmemT inp asp arnd aG) aG (out_buf (inp.in_argv.getD 1 []))) arom)
      model (rest.drop k) [] (Z_to_bv 64 0) := by
  induction fuel generalizing rest p k regs with
  | zero => omega
  | succ fuel ih =>
    have hu := u_len_word_firstn k rest hk2 (by omega)
    refine twm_tail.twmt_step _ _ _ _ _ _ rfl
      (step_bge_ft _ _ _ _ _ _ _ _ _ TF_1001240 (by decide) TD_1001240
        (by getr_resolve; rw [h10]; exact c_lts_0_pos _ (by omega) (by omega))) ?_
    norm_pc
    stepiv TF_1001244 TD_1001244 (Z_to_bv 64 (bv_unsigned p + (k : Int)))
      (getr_resolve; rw [h11, h10]; exact v_add_len_firstn_Z p k rest hk2 (by omega))
    stepiv TF_1001248 TD_1001248 (len_word (rest.drop k))
      (getr_resolve; rw [h12, h10]; exact v_sub_len_firstn k rest hk2 (by omega))
    by_cases heq : k = rest.length
    · subst k
      rw [List.drop_length]
      refine twm_tail.twmt_step _ _ _ _ _ _ rfl
        (step_bne_ft _ _ _ _ _ _ _ _ _ TF_100124c (by decide) TD_100124c
          (by getr_resolve; exact c_eq_0_true)) ?_
      norm_pc
      apply twm_tail.twmt_done
      apply target_out_tail inp asp arnd Hsp_lo Hsp_hi aG HaAl HaCeil Hnle
      · regupd_resolve; exact h2r
      · regupd_resolve; exact h13
      · exact hmap
    · have hdlen : ((rest.drop k).length : Int) < 2 ^ 64 := by rw [List.length_drop]; omega
      have hdu := u_len_word (rest.drop k) hdlen
      have hw : word_to_nat (len_word (rest.drop k)) = (rest.drop k).length := by
        change (word_to_nat (len_word (rest.drop k)) : Int) = ((rest.drop k).length : Int) at hdu
        omega
      have hsk := rdn_skipn target_segs
        (wbytes (zmemT inp asp arnd aG) aG (out_buf (inp.in_argv.getD 1 [])))
        rest.length p rest k hread hk2
      rw [word_add_nat_Z p k (by omega), ← List.length_drop] at hsk
      refine twm_tail.twmt_step _ _ _ _ _ _ rfl
        (step_bne_tk _ _ _ _ _ _ _ _ _ TF_100124c (by decide) TD_100124c
          (by getr_resolve; apply c_eq_0_false; rw [hdu, List.length_drop]; omega)) ?_
      norm_pc
      stepiv TF_1001238 TD_1001238 (Z_to_bv 64 1) (getr_resolve; rfl)
      refine twm_tail.twmt_step _ _ _ _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_100123c (by decide)) ?_
      apply twm_tail_write_rec
      · getr_resolve; exact h17
      · regupd_resolve; rfl
      · regupd_resolve
        rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs _ (Z_to_bv 64 (bv_unsigned p + (k : Int)))
          (word_to_nat (len_word (rest.drop k))) = _
        rw [hw]; exact hsk
      · rw [List.length_drop]; omega
      · intro m hm1 hm2
        norm_pc
        apply ih (rest.drop k) (Z_to_bv 64 (bv_unsigned p + (k : Int))) m
        · rw [List.length_drop]; omega
        · exact hm1
        · exact hm2
        · rw [List.length_drop]; omega
        · rw [u_Z2bv _ (by omega) (by omega)]; omega
        · rw [u_Z2bv _ (by omega) (by omega), List.length_drop]; omega
        · regupd_resolve; exact h2r
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; exact h13
        · regupd_resolve; exact h17
        · exact hsk

include Hsp_lo Hsp_hi HaPos HaAl HaCeil Hnle in
theorem target_out (model : Model) (regs : bvmap 5 word)
    (h2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (h13 : reg_get regs 13 = aG) (h16 : reg_get regs 16 = tnN inp)
    (hmap : map_has (m_vmmaps model).vm_maps aG (Z_to_bv 64 4096) = true) :
    twm target_segs
      (mkst regs 0x100121c (wbytes (zmemT inp asp arnd aG) aG (upperv (inp.in_argv.getD 1 []))) arom)
      model [out_buf (inp.in_argv.getD 1 [])] (Z_to_bv 64 0) := by
  have hhi := asp_hi_num asp Hsp_hi
  have hceil := HaCeil
  unfold stack_max_size at hceil
  have huN : bv_unsigned (tnN inp) = ((inp.in_argv.getD 1 []).length : Int) :=
    u_ntw _ (by omega)
  have emt : wbytes (zmemT inp asp arnd aG) aG (out_buf (inp.in_argv.getD 1 [])) =
      wbytes (wbytes (zmemT inp asp arnd aG) aG (upperv (inp.in_argv.getD 1 [])))
        (aG + nat_to_word (inp.in_argv.getD 1 []).length) [Z_to_bv 8 10] := by
    unfold out_buf
    rw [wbytes_snoc, length_upperv]
  stepiv TF_100121c TD_100121c (aG + nat_to_word (inp.in_argv.getD 1 []).length)
    (getr_resolve; rw [h13, h16]; rfl)
  stepi_at TF_1001220 TD_1001220 (Z_to_bv 64 10)
  refine twm.twm_step _ _ _ _ _ rfl
    (step_sb_at _ _ _ _ _ _ _ _ _ (aG + nat_to_word (inp.in_argv.getD 1 []).length)
      (Z_to_bv 64 10) (Z_to_bv 8 10) TF_1001224 (by decide) TD_1001224 ?_ ?_ (by decide) ?_) ?_
  · getr_resolve; imm_norm; exact v_addi_0 _
  · getr_resolve; rfl
  · store_ok_peel
    apply tgrant_store_ok asp Hsp_hi aG HaCeil
    · rw [word_add_nat]; u_norm; omega
    · rw [word_add_nat]; u_norm; omega
  · rw [← emt]
    norm_pc
    sym_block target_segs 5 [false] [] [(0, ELit 0), (16, EVar 32), (13, EVar 33)]
      [tnN inp, aG] [] RB HRB
    · apply c_eq_0_false
      u_norm
      omega
    · getr_resolve; rfl
    · getr_resolve; exact h16
    · getr_resolve; exact h13
    · have hb17 : bv_unsigned (getr RB 17) = 64 := by sym_regs HRB; rfl
      have hb10 : reg_get RB 10 = Z_to_bv 64 1 := by sym_regs HRB; rfl
      have hb11 : reg_get RB 11 = aG := by sym_regs HRB; exact v_addi_0 _
      have hb12 : reg_get RB 12 = len_word (out_buf (inp.in_argv.getD 1 [])) := by
        sym_regs HRB
        unfold len_word
        rw [huN, length_out_buf]
        congr 1 <;> omega
      have hb13 : reg_get RB 13 = aG := by sym_regs HRB
      have hb2 : reg_get RB 2 = Z_to_bv 64 (bv_unsigned asp - 32) := by
        sym_regs HRB; getr_resolve; exact h2r
      have hout : ((out_buf (inp.in_argv.getD 1 [])).length : Int) < 2 ^ 64 := by
        rw [length_out_buf]; omega
      have hw : word_to_nat (len_word (out_buf (inp.in_argv.getD 1 []))) =
          (out_buf (inp.in_argv.getD 1 [])).length := word_to_nat_ntw _ hout
      have hr := rdn_wbytes_hit target_segs (out_buf (inp.in_argv.getD 1 []))
        (zmemT inp asp arnd aG) aG (by rw [length_out_buf]; omega)
      refine twm.twm_step _ _ _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_100123c (by decide)) ?_
      apply twm_write_ret
      · exact hb17
      · exact hb10
      · rw [hb11, hb12, ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs _ aG (word_to_nat (len_word (out_buf (inp.in_argv.getD 1 [])))) = _
        rw [hw]; exact hr
      · rw [length_out_buf]; omega
      · intro k hk1 hk2
        norm_pc
        apply tgt_put_wall inp asp arnd Hsp_lo Hsp_hi aG HaAl HaCeil Hnle model
          (out_buf (inp.in_argv.getD 1 [])).length (out_buf (inp.in_argv.getD 1 [])) aG k
        · exact Nat.le_refl _
        · exact hk1
        · exact hk2
        · rw [length_out_buf]; omega
        · exact HaPos
        · rw [length_out_buf]; omega
        · regupd_resolve; exact hb2
        · regupd_resolve; rfl
        · regupd_resolve; exact hb11
        · regupd_resolve; exact hb12
        · regupd_resolve; exact hb13
        · regupd_resolve
          rw [getr_nz _ _ (by decide)] at hb17
          exact hb17
        · exact hmap
        · exact hr

include Hva Hve Hsp_lo Hsp_hi HaPos HaAl HaCeil H2av Hnle in
theorem target_succ_twm (model : Model) (regs : bvmap 5 word)
    (h2r : reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32))
    (h8r : reg_get regs 8 = tP inp asp) (h16r : reg_get regs 16 = tnN inp)
    (hmap : map_has (m_vmmaps model).vm_maps aG (Z_to_bv 64 4096) = true) :
    twm target_segs
      (mkst (regupd regs 10 aG) 0x10011dc (zfill aG (Z_to_bv 64 4096) (tfmem inp asp arnd)) arom)
      model [out_buf (inp.in_argv.getD 1 [])] (Z_to_bv 64 0) := by
  have hhi := asp_hi_num asp Hsp_hi
  have hceil := HaCeil
  unfold stack_max_size at hceil
  refine twm.twm_step _ _ _ _ _ rfl
    (step_blt_ft _ _ _ _ _ _ _ _ _ TF_10011dc (by decide) TD_10011dc
      (by getr_resolve; apply c_lts_pos_0; omega)) ?_
  norm_pc
  stepiv TF_10011e0 TD_10011e0 aG (getr_resolve; exact v_addi_0 _)
  stepiv TF_10011e4 TD_10011e4 (tnN inp) (getr_resolve; rw [h16r]; exact v_addi_0 _)
  by_cases hn0 : (inp.in_argv.getD 1 []).length = 0
  · have hnil : inp.in_argv.getD 1 [] = [] := List.length_eq_zero_iff.mp hn0
    refine twm.twm_step _ _ _ _ _ rfl
      (step_beq_tk _ _ _ _ _ _ _ _ _ TF_10011e8 (by decide) TD_10011e8
        (by getr_resolve; rw [h16r]; unfold tnN; rw [hn0]; exact c_eq_0_true)) ?_
    norm_pc
    have emem0 : wbytes (zmemT inp asp arnd aG) aG (upperv (inp.in_argv.getD 1 [])) =
        zfill aG (Z_to_bv 64 4096) (tfmem inp asp arnd) := by
      rw [hnil]; rfl
    rw [← emem0]
    apply target_out inp asp arnd Hsp_lo Hsp_hi aG HaPos HaAl HaCeil Hnle
    · regupd_resolve; exact h2r
    · regupd_resolve; rfl
    · regupd_resolve; exact h16r
    · exact hmap
  · refine twm.twm_step _ _ _ _ _ rfl
      (step_beq_ft _ _ _ _ _ _ _ _ _ TF_10011e8 (by decide) TD_10011e8
        (by getr_resolve; rw [h16r]; apply c_eq_0_false
            unfold tnN; rw [u_ntw _ (by omega)]; omega)) ?_
    norm_pc
    obtain ⟨regsC, hfrC, hmsC⟩ := target_copy inp asp arnd Hva Hve Hsp_lo Hsp_hi
      aG HaCeil H2av Hnle (inp.in_argv.getD 1 []).length 0
      (regupd (regupd (regupd regs 10 aG) 13 aG) 11 (tnN inp))
      (by regupd_resolve; rw [word_add_0]; exact h8r)
      (by regupd_resolve; rw [word_add_0])
      (by regupd_resolve; rw [Nat.sub_zero]; rfl) (by omega) (by omega)
    apply msteps_twm _ _ _ _ _ _ hmsC
    apply target_out inp asp arnd Hsp_lo Hsp_hi aG HaPos HaAl HaCeil Hnle
    · rw [hfrC 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
      regupd_resolve; exact h2r
    · rw [hfrC 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
      regupd_resolve; rfl
    · rw [hfrC 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
      regupd_resolve; exact h16r
    · exact hmap

end TargetSucc

include Hva Hve Hsp_lo Hsp_hi in
theorem target_tmw (abrk amb : word) (h2 : 2 ≤ inp.in_argv.length)
    (hn : (inp.in_argv.getD 1 []).length ≤ 4095) :
    tmw target_segs
      (init_machine_state target_segs 0x1001158 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      [] (Z_to_bv 64 4) [out_buf (inp.in_argv.getD 1 [])] (Z_to_bv 64 0) := by
  obtain ⟨regsE, he2, he8, he16, he11, he12, he13, he14, he15, he17, hms⟩ :=
    target_to_mmap inp asp arnd Hva Hve Hsp_lo Hsp_hi h2 hn
  apply msteps_tmw _ _ _ _ _ _ _ _ hms
  apply tmw_mmap_rec
  · exact he17
  · rw [he11]; decide
  · exact he12
  · exact he13
  · rw [he14]; rfl
  · exact he15
  · intro e hin
    obtain ⟨he1, he2'⟩ := mmap_errno_range e hin
    norm_pc
    exact target_fail_twm inp asp arnd Hsp_lo Hsp_hi _ _ e he1 he2' he2
  · intro aa hg
    rw [he11] at hg
    change grant_ok _ _ aa (page_round_up_Z 4096) = true at hg
    rw [page_round_up_Z_4096] at hg
    rw [he11, pru_4096]
    obtain ⟨hpos, hal, hceil, hda, hdb⟩ := target_grant_unpack inp _ abrk amb asp aa hg
    norm_pc
    apply target_succ_twm inp asp arnd Hva Hve Hsp_lo Hsp_hi aa hpos hal hceil h2 hn
    · exact he2
    · exact he8
    · exact he16
    · change (bv_eqb aa aa && bv_eqb (Z_to_bv 64 4096) (Z_to_bv 64 4096) || false) = true
      rw [(bv_eqb_eq aa aa).2 rfl]
      rfl
  · rw [he11]
    change ∃ a, grant_ok _ _ a (page_round_up_Z 4096) = true
    rw [page_round_up_Z_4096]
    exact ⟨Z_to_bv 64 0x2aaaaab000, target_grant_witness inp _ abrk amb asp Hsp_lo⟩



end TargetProof

end LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_target
