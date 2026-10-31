import LinuxProcessSemantics.Examples.cp_ns.cp_ns_defs
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.ArgvEnv

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Proof-side execution of the source copy binary. The frame invariant and
instruction blocks are shared by the bounded copy-loop induction and the
huge-file divergence invariant. Syscall nodes use Common.FileSim; the private
helpers factor the source binary's repeated open and close continuations.
Rocq section parameters are explicit leading arguments. -/

namespace LinuxProcessSemantics.Examples.cp_ns.cp_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.FileSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Common.ArgvEnv
open LinuxProcessSemantics.Examples.cp_ns.SourceMemImage
open LinuxProcessSemantics.Examples.cp_ns.TargetMemImage
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_code
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_defs
open LinuxProcessSemantics.Common.ErrEscape
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open FdEntry ProcInput aluop config
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def rrom : word → Option byte := seg_rom source_segs
def sbuf : word := 0x13008

theorem u_sbuf : bv_unsigned sbuf = 0x13008 := rfl

theorem In_firstn_incl (A : Type) (x : A) (n : Nat) (l : List A)
    (H : x ∈ l.take n) : x ∈ l := List.mem_of_mem_take H

theorem c_eq_0_of_u (x : word) (Hx : bv_unsigned x = 0) :
    c_eq x (Z_to_bv 64 0) = true := by
  rw [c_eq, bv_eqb_Z, Hx]
  rfl

variable (inp : ProcInput)
variable (Hva : valid_argv (in_argv inp)) (Hve : valid_envp (in_envp inp))
variable (rsp : word) (rrnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
variable (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
variable (rbrk rmb : word)

include Hsp_lo in
theorem rsp_lo_num : 0x7fff80000000 ≤ bv_unsigned rsp := Hsp_lo
include Hsp_hi in
theorem rsp_hi_num : bv_unsigned rsp ≤ 0x800000000000 := Hsp_hi

def argcN : word := len_word (in_argv inp)
def wmem : word → Option byte :=
  wrap_mem source_phdrs rsp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rrnd

include Hva in
theorem u_argcN : bv_unsigned (argcN inp) = (((in_argv inp)).length : Int) := by
  have H := valid_argv_len (in_argv inp) Hva
  exact u_len_word (in_argv inp) (by omega)

include Hva Hve Hsp_hi in
theorem source_bsb_nw : bv_unsigned rsp +
    ((build_stack_bytes source_phdrs rsp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rrnd).length : Int) < 2^64 :=
  bsb_nw source_phdrs rsp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rrnd Hva Hve Hsp_hi

def envp_val : word := Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * (((in_argv inp)).length : Int))

include Hva Hsp_lo Hsp_hi in
theorem envp_val_eq :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp) 3)) 8 =
      envp_val inp rsp := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hlen := valid_argv_len (in_argv inp) Hva
  have Ha := u_argcN inp Hva
  have Hs := v_slli_3 (argcN inp) (by omega)
  apply bv_eq_of_unsigned
  unfold envp_val v_addi
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned,
    v_add_small _ _ (by u_norm; rw [Hs, Ha]; omega)]
  u_norm
  rw [Hs, Ha]
  congr 1 <;> omega

theorem v_sll_3 (x : word) : v_sll x (Z_to_bv 64 3) = v_slli x 3 := rfl

include Hva Hsp_lo Hsp_hi in
theorem envp_val_eq_sym :
    Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (argcN inp) (Z_to_bv 64 3))) + 8) = envp_val inp rsp := by
  rw [alu_add, v_sll_3]
  exact envp_val_eq inp Hva rsp Hsp_lo Hsp_hi

def emem : word → Option byte :=
  wbytes (wmem inp rsp rrnd) 0x13000 (word_to_le_bytes 8 (envp_val inp rsp))

/-- The four callee-saved slots in main's 48-byte frame. The lower two
slots are reserved for the copy loop's pointer and count. -/
def fmem : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (emem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x11158 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))

def smem_inv (mem : word → Option byte) : Prop :=
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
    some (word_to_le_bytes 8 (0x11158 : word)) ∧
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8 =
    some (word_to_le_bytes 8 (Z_to_bv 64 0)) ∧
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8 =
    some (word_to_le_bytes 8 (Z_to_bv 64 0)) ∧
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8 =
    some (word_to_le_bytes 8 (Z_to_bv 64 0)) ∧
  mem_grows (wmem inp rsp rrnd) mem

include Hsp_lo Hsp_hi in
theorem smem_inv_fmem : smem_inv inp rsp rrnd (fmem inp rsp rrnd) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold smem_inv fmem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | (solve | (unfold emem; solve_mem_grows))
  | (repeat first
      | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
      | rw [rdn_wbytes_disjoint _ _ _ _ _ _
          (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
      | rw [rdn_wbytes_below _ _ _ _ _ _
          (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)])

theorem smem_inv_grows (mem : word → Option byte) (H : smem_inv inp rsp rrnd mem) :
    mem_grows (wmem inp rsp rrnd) mem := H.2.2.2.2

local macro_rules
  | `(tactic| store_ok_grows) => `(tactic| (apply smem_inv_grows; assumption))

include Hsp_lo in
theorem rdn_emem_above (a : word) (n : Nat)
    (Ha : bv_unsigned rsp ≤ bv_unsigned a) (Hnw : bv_unsigned a + (n : Int) ≤ 2^64) :
    rdn source_segs (emem inp rsp rrnd) a n = rdn source_segs (wmem inp rsp rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  unfold emem
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; imm_norm; omega) Hnw]

include Hsp_lo Hsp_hi in
theorem rdn_fmem_above (a : word) (n : Nat)
    (Ha : bv_unsigned rsp ≤ bv_unsigned a) (Hnw : bv_unsigned a + (n : Int) ≤ 2^64) :
    rdn source_segs (fmem inp rsp rrnd) a n = rdn source_segs (wmem inp rsp rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) Hnw]
  exact rdn_emem_above inp rsp rrnd Hsp_lo a n Ha Hnw

theorem rdn_wmem_stack (a : word) (n : Nat)
    (Ha : bv_unsigned rsp ≤ bv_unsigned a) (Hnw : bv_unsigned a + (n : Int) ≤ 2^64) :
    rdn source_segs (wmem inp rsp rrnd) a n =
      rdn source_segs (stack_to_mem rsp
        (entry_stack_image source_phdrs rsp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rrnd)) a n :=
  rdn_wrap_stack_above source_segs _ _ _ _ _ _ _ _ _ Ha Hnw

include Hva Hve Hsp_hi in
theorem read_argc_w : rdn source_segs (wmem inp rsp rrnd) rsp 8 = some (word_le8 (argcN inp)) := by
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_wmem_stack inp rsp rrnd rsp 8 (by omega) (by omega)]
  exact read_argc source_phdrs source_segs rsp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rrnd
    (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

local macro "s_out" H:ident : tactic => `(tactic| (
  sym_regs $H <;> getr_resolve <;> imm_norm <;>
    first | rfl | assumption | exact v_addi_0 _ | (congr 1 <;> omega) | decide +kernel | sym_close | (apply bv_eq_of_unsigned; u_norm; omega)))

set_option hygiene false in
local macro "s_ro" : tactic => `(tactic| (
  first | (apply source_store_ok <;> (imm_norm; u_norm; omega)) | solve_store_ok_inv))

theorem src_shuffle : ∀ regs mem,
  ∃ regs',
    reg_get regs' 17 = reg_get regs 10 ∧
    reg_get regs' 10 = reg_get regs 11 ∧
    reg_get regs' 11 = reg_get regs 12 ∧
    reg_get regs' 12 = reg_get regs 13 ∧
    reg_get regs' 1 = reg_get regs 1 ∧
    reg_get regs' 2 = reg_get regs 2 ∧
    reg_get regs' 3 = reg_get regs 3 ∧
    reg_get regs' 8 = reg_get regs 8 ∧
    reg_get regs' 9 = reg_get regs 9 ∧
    reg_get regs' 18 = reg_get regs 18 ∧
    reg_get regs' 19 = reg_get regs 19 ∧
    msteps source_segs (mkst regs (0x11160 : word) mem rrom)
      (mkst regs' (0x1117c : word) mem rrom) := by
  intro regs mem
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69984) mem rrom)
    7 [] ([] : List expr) ([] : List (reg × expr)) ([] : List word) ([] : List word) R HR Hms
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | exact Hms | s_out HR

include Hsp_lo Hsp_hi in
theorem source_fepilogue : ∀ regs mem model code fsv,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 10 = code → (bv_unsigned code < 256) →
  (smem_inv inp rsp rrnd) mem →
  m_fs model = fsv →
  to_fout source_segs (mkst regs (0x110fc : word) mem rrom) model
    (fun o => o = (code, fsv)) := by
  intro regs mem model code fsv H2 H10 Hc Hsm Hfs
  obtain ⟨Hra, Hs0, Hs1, Hs2, Hg⟩ := Hsm
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69884) mem rrom)
    9 [] [ELit 0x11158, ELit 0, ELit 0, ELit 0]
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned rsp - 48)] ([] : List word) R HR Hms
  · repeat' first
    | apply And.intro
    | omega
    | exact ⟨_, Hs2, bytes_le_to_Z_8 _⟩
    | exact ⟨_, Hs1, bytes_le_to_Z_8 _⟩
    | exact ⟨_, Hs0, bytes_le_to_Z_8 _⟩
    | exact ⟨_, Hra, bytes_le_to_Z_8 _⟩
  · exact H2
  apply tfo_msteps source_segs _ _ _ _ Hms
  sym_pc_lit
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1115c rfl)
  apply tfo_exit_rec
  · s_out HR
  · s_out HR
  · exact Hc
  · exact Hfs

theorem src_sret : ∀ regs mem spv rv raL s0v g3 g9 g18,
  reg_get regs 2 = spv → reg_get regs 10 = rv → reg_get regs 1 = raL →
  reg_get regs 8 = s0v →
  reg_get regs 3 = g3 → reg_get regs 9 = g9 → reg_get regs 18 = g18 →
  (bv_unsigned rv ≤ 1024) →
  v_jalr raL 0 = raL →
  ∃ regs',
    reg_get regs' 2 = spv ∧ reg_get regs' 10 = rv ∧ reg_get regs' 1 = raL ∧
    reg_get regs' 8 = s0v ∧ reg_get regs' 3 = g3 ∧ reg_get regs' 9 = g9 ∧
    reg_get regs' 18 = g18 ∧
    msteps source_segs (mkst regs (0x111dc : word) mem rrom)
      (mkst regs' raL mem rrom) := by
  intro regs mem spv rv raL s0v g3 g9 g18 H2 H10 H1 H8 H3 H9 H18 Hrv Hvj
  refine ⟨regupd regs 15 (Z_to_bv 64 18446744073709547520), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 7
  · stepiv SF_111dc SD_111dc (Z_to_bv 64 18446744073709547520) (bveq)
    step_intro
    · rfl
    · apply step_bltu_ft (hf := SF_111e0) (he := rfl) (hd := SD_111e0)
      getr_resolve; regupd_resolve
      rw [H10, c_ltu_ltb]
      apply decide_eq_false
      u_norm; omega
    norm_pc
    step_intro
    · rfl
    · apply step_jalr_x0 (tgt := raL) (hf := SF_111e4) (he := rfl) (hd := SD_111e4)
      getr_resolve; regupd_resolve; exact H1
    imm_norm
    rw [Hvj]
    exact msteps.mst_refl _
  all_goals regupd_resolve; assumption

def spill (rsp : word) (mem : word → Option byte) (cnt : word) : word → Option byte :=
  wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 cnt))
    (Z_to_bv 64 (bv_unsigned rsp - 48)) (word_to_le_bytes 8 sbuf)

include Hsp_lo Hsp_hi in
theorem rdn_spill_cnt : ∀ mem cnt,
  rdn source_segs ((spill rsp) mem cnt) (Z_to_bv 64 (bv_unsigned rsp - 40)) 8
    = some (word_to_le_bytes 8 cnt) := by
  intro mem cnt
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold spill
  rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
  apply rdn_wbytes_hit8; u_norm; omega

include Hsp_lo Hsp_hi in
theorem rdn_spill_ptr : ∀ mem cnt,
  rdn source_segs ((spill rsp) mem cnt) (Z_to_bv 64 (bv_unsigned rsp - 48)) 8
    = some (word_to_le_bytes 8 sbuf) := by
  intro mem cnt
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold spill
  apply rdn_wbytes_hit8; u_norm; omega

theorem src_head_to_read : ∀ regs mem fdin fdout,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 3 = (0x13800 : word) →
  reg_get regs 8 = sbuf →
  reg_get regs 18 = fdin → reg_get regs 9 = fdout →
  ∃ regs',
    bv_unsigned (getr regs' 17) = 63 ∧
    reg_get regs' 10 = fdin ∧ reg_get regs' 11 = sbuf ∧
    reg_get regs' 12 = Z_to_bv 64 1024 ∧
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs' 1 = (0x1109c : word) ∧
    reg_get regs' 3 = (0x13800 : word) ∧
    reg_get regs' 8 = sbuf ∧
    reg_get regs' 9 = fdout ∧ reg_get regs' 18 = fdin ∧
    msteps source_segs (mkst regs (0x1107c : word) mem rrom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x1117c : word),
         ms_svc_pending := some (getr regs' 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
         ms_mem := mem, ms_rom := rrom } := by
  intro regs mem fdin fdout H2 H3 H8 H18 H9
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69756) mem rrom)
    16 [] ([] : List expr)
    [((8 : reg), EVar 32), ((18 : reg), EVar 33)] [sbuf, fdin] ([] : List word) R HR Hms
  · exact H8
  · exact H18
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 10
  · apply msteps_trans _ _ _ _ Hms
    sym_pc_lit
    exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl) (msteps.mst_refl _)
  all_goals s_out HR

include Hsp_lo Hsp_hi in
theorem smem_inv_wtm : ∀ mem (chunk : List byte),
  (smem_inv inp rsp rrnd) mem → ((chunk.length : Int) ≤ 1024) →
  (smem_inv inp rsp rrnd) (write_to_mem mem sbuf chunk) := by
  intro mem chunk Hsm Hlen
  obtain ⟨Hra, Hs0, Hs1, Hs2, Hg⟩ := Hsm
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold smem_inv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | (solve | solve_mem_grows)
  | (rw [rdn_wtm_out _ _ _ _ _ _ (by u_norm; omega)
      (by rw [u_sbuf]; omega) (by left; rw [u_sbuf]; u_norm; omega)]; assumption)

include Hsp_lo Hsp_hi in
theorem smem_inv_spill : ∀ mem cnt,
  (smem_inv inp rsp rrnd) mem → (smem_inv inp rsp rrnd) ((spill rsp) mem cnt) := by
  intro mem cnt Hsm
  obtain ⟨Hra, Hs0, Hs1, Hs2, Hg⟩ := Hsm
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold smem_inv spill
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | (solve | solve_mem_grows)
  | (repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
     assumption)

def src : path := (in_argv inp).getD 1 []
def dst : path := (in_argv inp).getD 2 []
def psrc : word := cat_argv_ptr rsp (in_argv inp) (in_envp inp) 1
def pdst : word := cat_argv_ptr rsp (in_argv inp) (in_envp inp) 2

variable (Hge3 : 3 ≤ (in_argv inp).length)

include Hva Hve Hsp_hi Hge3 in
theorem psrc_bounds :
  (bv_unsigned rsp ≤ bv_unsigned (psrc inp rsp)) ∧
  (bv_unsigned (psrc inp rsp) + ((src inp).length : Int) + 1 < 2^64) := by
  exact argv_ptr_bounds_at rsp (in_argv inp) (in_envp inp) Hva Hve Hsp_hi 1 (by omega)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_psrc_e :
  rdn source_segs (emem inp rsp rrnd) (rsp + nat_to_word (8 + 8 * 1)) 8
    = some (word_le8 (psrc inp rsp)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_emem_above inp rsp rrnd Hsp_lo _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_wmem_stack inp rsp rrnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k source_phdrs source_segs rsp (in_argv inp) (in_envp inp) 1
    (in_uid inp) (in_hwcap inp) rrnd (by omega)
    (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_src : (List.length (src inp) ≤ 4095) →
  read_cstr (mrb source_segs (fmem inp rsp rrnd)) (psrc inp rsp) = CstrOk (src inp) := by
  intro Hlen
  obtain ⟨Hlo, Hhi⟩ := psrc_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz (in_argv inp) 1 Hva (by omega)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp rsp rrnd _ _ (by omega) (by omega)]
    exact read_argv_cstr_k source_phdrs source_segs rsp (in_argv inp) (in_envp inp) 1
      (in_uid inp) (in_hwcap inp) rrnd (by omega)
      (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_src_toolong : (4096 ≤ List.length (src inp)) →
  read_cstr (mrb source_segs (fmem inp rsp rrnd)) (psrc inp rsp) = CstrTooLong := by
  intro Hlen
  obtain ⟨Hlo, Hhi⟩ := psrc_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn source_segs (fmem inp rsp rrnd) (psrc inp rsp)
    ((src inp).take 4096)
  · rw [List.length_take]; omega
  · intro H
    exact valid_argv_str_nz (in_argv inp) 1 Hva (by omega) (List.mem_of_mem_take H)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp rsp rrnd _ _ (by omega) (by omega)]
    exact read_argv_prefix_k source_phdrs source_segs rsp (in_argv inp) (in_envp inp) 1 4096
      (in_uid inp) (in_hwcap inp) rrnd (by omega) Hlen
      (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

include Hva Hve Hsp_hi Hge3 in
theorem pdst_bounds :
  (bv_unsigned rsp ≤ bv_unsigned (pdst inp rsp)) ∧
  (bv_unsigned (pdst inp rsp) + ((dst inp).length : Int) + 1 < 2^64) := by
  exact argv_ptr_bounds_at rsp (in_argv inp) (in_envp inp) Hva Hve Hsp_hi 2 (by omega)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_pdst_f :
  rdn source_segs (fmem inp rsp rrnd) (rsp + nat_to_word (8 + 8 * 2)) 8
    = some (word_le8 (pdst inp rsp)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_wmem_stack inp rsp rrnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k source_phdrs source_segs rsp (in_argv inp) (in_envp inp) 2
    (in_uid inp) (in_hwcap inp) rrnd (by omega)
    (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_dst : (List.length (dst inp) ≤ 4095) →
  read_cstr (mrb source_segs (fmem inp rsp rrnd)) (pdst inp rsp) = CstrOk (dst inp) := by
  intro Hlen
  obtain ⟨Hlo, Hhi⟩ := pdst_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz (in_argv inp) 2 Hva (by omega)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp rsp rrnd _ _ (by omega) (by omega)]
    exact read_argv_cstr_k source_phdrs source_segs rsp (in_argv inp) (in_envp inp) 2
      (in_uid inp) (in_hwcap inp) rrnd (by omega)
      (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_dst_toolong : (4096 ≤ List.length (dst inp)) →
  read_cstr (mrb source_segs (fmem inp rsp rrnd)) (pdst inp rsp) = CstrTooLong := by
  intro Hlen
  obtain ⟨Hlo, Hhi⟩ := pdst_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn source_segs (fmem inp rsp rrnd) (pdst inp rsp)
    ((dst inp).take 4096)
  · rw [List.length_take]; omega
  · intro H
    exact valid_argv_str_nz (in_argv inp) 2 Hva (by omega) (List.mem_of_mem_take H)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp rsp rrnd _ _ (by omega) (by omega)]
    exact read_argv_prefix_k source_phdrs source_segs rsp (in_argv inp) (in_envp inp) 2 4096
      (in_uid inp) (in_hwcap inp) rrnd (by omega) Hlen
      (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)

include Hsp_lo Hsp_hi in
theorem src_close_entry : ∀ regs mem fdv raM s0v g3 g9 g18,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 10 = fdv → reg_get regs 1 = raM → reg_get regs 8 = s0v →
  reg_get regs 3 = g3 → reg_get regs 9 = g9 → reg_get regs 18 = g18 →
  mem_grows (wmem inp rsp rrnd) mem →
  ∃ regs',
    bv_unsigned (getr regs' 17) = 57 ∧ reg_get regs' 10 = fdv ∧
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ∧
    reg_get regs' 1 = (0x111b4 : word) ∧ reg_get regs' 8 = s0v ∧
    reg_get regs' 3 = g3 ∧ reg_get regs' 9 = g9 ∧ reg_get regs' 18 = g18 ∧
    msteps source_segs (mkst regs (0x11188 : word) mem rrom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x11230 : word),
         ms_svc_pending := some (getr regs' 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
         ms_mem := wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56))
                          (word_to_le_bytes 8 raM),
         ms_rom := rrom } := by
  intro regs mem fdv raM s0v g3 g9 g18 H2 H10 H1 H8 H3 H9 H18 Hg
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 70024) mem rrom)
    21 [] ([] : List expr)
    [((1 : reg), EVar 32), ((2 : reg), EVar 33), ((10 : reg), EVar 34)]
    [raM, Z_to_bv 64 (bv_unsigned rsp - 48), fdv] ([] : List word) R HR Hms
  · unfold wmem at Hg
    repeat' first | apply And.intro | omega | solve_store_ok_inv
  · exact H1
  · exact H2
  · exact H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 8
  · apply msteps_trans _ _ _ _ Hms
    sym_pc_lit
    sym_mem_norm
    step_intro
    · rfl
    · exact step_ecall _ _ _ _ _ _ SF_11230 rfl
    exact msteps.mst_refl _
  all_goals s_out HR

include Hsp_lo Hsp_hi in
theorem src_close_tail : ∀ regs mem raM s0v g3 g9 g18,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) →
  reg_get regs 10 = Z_to_bv 64 0 →
  reg_get regs 1 = (0x111b4 : word) → reg_get regs 8 = s0v →
  reg_get regs 3 = g3 → reg_get regs 9 = g9 → reg_get regs 18 = g18 →
  v_jalr raM 0 = raM →
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8
    = some (word_to_le_bytes 8 raM) →
  ∃ regs',
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs' 10 = Z_to_bv 64 0 ∧ reg_get regs' 1 = raM ∧
    reg_get regs' 8 = s0v ∧ reg_get regs' 3 = g3 ∧
    reg_get regs' 9 = g9 ∧ reg_get regs' 18 = g18 ∧
    msteps source_segs (mkst regs (0x11234 : word) mem rrom)
      (mkst regs' raM mem rrom) := by
  intro regs mem raM s0v g3 g9 g18 H2 H10 H1 H8 H3 H9 H18 Hvj Hrd
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 70196) mem rrom)
    11 [false, false] [EVar 33]
    [((1 : reg), ELit 0x111b4), ((2 : reg), EVar 32), ((10 : reg), ELit 0)]
    [Z_to_bv 64 (bv_unsigned rsp - 64)] [raM] R HR Hms
  · repeat' first
    | apply And.intro
    | omega
    | decide +kernel
    | (refine ⟨word_to_le_bytes 8 raM, ?_, bytes_le_to_Z_8 _⟩
       first | exact Hrd | (rw [show bv_unsigned rsp - 64 + 8 = bv_unsigned rsp - 56 by omega]; exact Hrd))
  · exact H1
  · exact H2
  · exact H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 7
  · apply msteps_trans _ _ _ _ Hms
    sym_pc_lit
    step_intro
    · rfl
    · apply step_jalr_x0 (tgt := raM) (hf := SF_111d0) (he := rfl) (hd := SD_111d0)
      s_out HR
    imm_norm
    rw [Hvj]
    exact msteps.mst_refl _
  · sym_regs HR
    change Z_to_bv 64 (bv_unsigned rsp - 64 + 16) = Z_to_bv 64 (bv_unsigned rsp - 48)
    apply congrArg (Z_to_bv 64)
    omega
  · sym_regs HR
    decide +kernel
  all_goals s_out HR

include Hsp_lo Hsp_hi in
theorem src_read_to_write : ∀ regs mem fdin fdout cnt,
  reg_get regs 10 = cnt →
  (1 ≤ bv_unsigned cnt) → (bv_unsigned cnt ≤ 1024) →
  reg_get regs 1 = (0x1109c : word) →
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 3 = (0x13800 : word) →
  reg_get regs 8 = sbuf →
  reg_get regs 9 = fdout → reg_get regs 18 = fdin →
  
  mem_grows (wmem inp rsp rrnd) mem →
  ∃ regs',
    bv_unsigned (getr regs' 17) = 64 ∧
    reg_get regs' 10 = fdout ∧ reg_get regs' 11 = sbuf ∧
    reg_get regs' 12 = cnt ∧ reg_get regs' 8 = sbuf ∧
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs' 1 = (0x110cc : word) ∧
    reg_get regs' 3 = (0x13800 : word) ∧
    reg_get regs' 9 = fdout ∧ reg_get regs' 18 = fdin ∧
    msteps source_segs (mkst regs (0x11180 : word) mem rrom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x1117c : word),
         ms_svc_pending := some (getr regs' 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
         ms_mem := (spill rsp) mem cnt, ms_rom := rrom } := by
  intro regs mem fdin fdout cnt H10 Hc1 Hc2 H1 H2 H3 H8 H9 H18 Hg
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 70016) mem rrom)
    22 [false, false] ([] : List expr)
    [((1 : reg), ELit 0x1109c), ((2 : reg), EVar 32), ((8 : reg), EVar 33),
     ((9 : reg), EVar 34), ((10 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 48), sbuf, fdout, cnt] ([] : List word) R HR Hms
  · unfold wmem at Hg
    repeat' first
    | apply And.intro
    | omega
    | solve | solve_store_ok_inv
    | solve | (apply c_eq_0_false; omega)
    | solve | (apply c_lts_pos_0; omega)
  · exact H1
  · exact H2
  · exact H8
  · exact H9
  · exact H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 10
  · apply msteps_trans _ _ _ _ Hms
    sym_pc_lit
    unfold spill
    sym_mem_norm
    step_intro
    · rfl
    · exact step_ecall _ _ _ _ _ _ SF_1117c rfl
    exact msteps.mst_refl _
  all_goals s_out HR

include Hsp_lo Hsp_hi in
theorem src_write_to_head : ∀ regs mem fdin fdout cnt,
  reg_get regs 10 = cnt →
  (1 ≤ bv_unsigned cnt) → (bv_unsigned cnt ≤ 1024) →
  reg_get regs 1 = (0x110cc : word) →
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 3 = (0x13800 : word) →
  reg_get regs 8 = sbuf →
  reg_get regs 9 = fdout → reg_get regs 18 = fdin →
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8
    = some (word_to_le_bytes 8 cnt) →
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 48)) 8
    = some (word_to_le_bytes 8 sbuf) →
  ∃ regs',
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs' 3 = (0x13800 : word) ∧
    reg_get regs' 8 = sbuf ∧
    reg_get regs' 9 = fdout ∧ reg_get regs' 18 = fdin ∧
    msteps source_segs (mkst regs (0x11180 : word) mem rrom)
      (mkst regs' (0x1107c : word) mem rrom) := by
  intro regs mem fdin fdout cnt H10 Hc1 Hc2 H1 H2 H3 H8 H9 H18 Hrc Hrp
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 70016) mem rrom)
    8 [false, false] [EVar 33, EVar 34]
    [((1 : reg), ELit 0x110cc), ((2 : reg), EVar 32), ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 48), cnt] [sbuf] R HR Hms
  · repeat' first
    | apply And.intro
    | omega
    | exact ⟨_, Hrp, bytes_le_to_Z_8 _⟩
    | exact ⟨_, Hrc, bytes_le_to_Z_8 _⟩
    | (rw [Bool.not_eq_false']; apply c_eq_0_of_u
       rw [v_sub_small _ _ (by omega)]; omega)
    | (rw [Bool.not_eq_false']; apply c_lts_0_pos <;> omega)
  · exact H1
  · exact H2
  · exact H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, Hms⟩
  all_goals s_out HR

set_option hygiene false in
local macro "s_argc_read" : tactic => `(tactic| (
  refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
  rw [show Z_to_bv 64 (bv_unsigned rsp + 0) = rsp from v_addi_0 rsp]
  exact read_argc_w inp Hva Hve rsp rrnd Hsp_hi))

set_option hygiene false in
local macro "s_argc_branch" : tactic => `(tactic| (
  try rw [Bool.not_eq_true']
  try rw [Bool.not_eq_false']
  rw [bv_lts_small _ _ (by u_norm; omega) (by rw [u_argcN inp Hva]; omega)]
  first | rw [decide_eq_true_eq] | rw [decide_eq_false_iff_not]
  u_norm
  rw [u_argcN inp Hva]
  omega))

include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_lt3 : (List.length (in_argv inp) < 3) →
  to_wexit source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    [] (Z_to_bv 64 2) := by
  intro Hlt3
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HargcLe := valid_argv_len (in_argv inp) Hva
  rw [init_mkst]
  norm_pc
  sym_block source_segs 20 [true] [EVar 33]
    [((2 : reg), EVar 32)] [rsp] [argcN inp] R HR
  · repeat' first
    | apply And.intro
    | omega
    | solve | s_argc_branch
    | solve | s_argc_read
    | solve | s_ro
  · getr_resolve; rfl
  apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1115c rfl)
  apply tw_exit_coden
  · s_out HR
  · s_out HR
  · decide +kernel

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_to_open1 :
  ∃ regs1,
    reg_get regs1 1 = (0x11040 : word) ∧
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs1 3 = (0x13800 : word) ∧
    reg_get regs1 8 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
    bv_unsigned (getr regs1 17) = 56 ∧
    reg_get regs1 10 = AT_FDCWD ∧
    reg_get regs1 11 = (psrc inp rsp) ∧
    reg_get regs1 12 = Z_to_bv 64 0 ∧
    msteps source_segs
      (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (mkst regs1 (0x1117c : word) (fmem inp rsp rrnd) rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HargcLe := valid_argv_len (in_argv inp) Hva
  obtain ⟨Hplo, Hphi⟩ := psrc_bounds inp Hva Hve rsp Hsp_hi Hge3
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
      (Z_to_bv 64 69932) (wmem inp rsp rrnd) rrom)
    40 [false] [EVar 33, EVar 34]
    [((2 : reg), EVar 32), ((8 : reg), ELit 0), ((9 : reg), ELit 0), ((18 : reg), ELit 0)]
    [rsp] [argcN inp, psrc inp rsp] R HR Hms
  · repeat' first
    | apply And.intro
    | omega
    | solve | s_argc_branch
    | solve | s_argc_read
    | solve | s_ro
    | (refine ⟨word_le8 (psrc inp rsp), ?_, bytes_le_n_to_le_8 _⟩
       rw [show Z_to_bv 64 (bv_unsigned rsp + 16) = rsp + nat_to_word (8 + 8 * 1) by
         rw [word_add_nat]; congr 1 <;> omega]
       rw [← rdn_emem_above inp rsp rrnd Hsp_lo _ _
         (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
       exact read_psrc_e inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3)
  all_goals try (getr_resolve; rfl)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 8
  · rw [init_mkst]
    apply msteps_trans _ _ _ _ Hms
    sym_pc_lit
    unfold fmem emem
    sym_mem_norm
    rw [v_sll_3, ← envp_val_eq inp Hva rsp Hsp_lo Hsp_hi]
    change msteps source_segs _ _
    exact msteps.mst_refl _
  all_goals s_out HR

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_to_open2 : ∀ regs fdv,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 3 = (0x13800 : word) →
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned rsp + 8) →
  reg_get regs 1 = (0x11040 : word) →
  reg_get regs 10 = fdv → (bv_unsigned fdv < 2 ^ 31) →
  ∃ regs2,
    reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regs2 3 = (0x13800 : word) ∧
    reg_get regs2 18 = fdv ∧
    reg_get regs2 8 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
    reg_get regs2 1 = (0x1106c : word) ∧
    bv_unsigned (getr regs2 17) = 56 ∧
    reg_get regs2 10 = AT_FDCWD ∧
    reg_get regs2 11 = (pdst inp rsp) ∧
    reg_get regs2 12 = Z_to_bv 64 577 ∧
    msteps source_segs (mkst regs (0x11180 : word) (fmem inp rsp rrnd) rrom)
                       (mkst regs2 (0x1117c : word) (fmem inp rsp rrnd) rrom) := by
  intro regs fdv H2 H3 H8 H1 H10 Hlt
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨Hplo, Hphi⟩ := pdst_bounds inp Hva Hve rsp Hsp_hi Hge3
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 70016) (fmem inp rsp rrnd) rrom)
    20 [false] [EVar 34]
    [((1 : reg), ELit 0x11040), ((8 : reg), EVar 32), ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp + 8), fdv] [pdst inp rsp] R HR Hms
  · repeat' first
    | apply And.intro
    | omega
    | (apply c_lts_pos_0; omega)
    | (refine ⟨word_le8 (pdst inp rsp), ?_, bytes_le_n_to_le_8 _⟩
       rw [show Z_to_bv 64 (bv_unsigned rsp + 24) = rsp + nat_to_word (8 + 8 * 2) by
         rw [word_add_nat]; congr 1 <;> omega]
       exact read_pdst_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3)
  · exact H1
  · exact H8
  · exact H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
  all_goals s_out HR

include Hsp_lo Hsp_hi in
theorem src_open1_err_tail : ∀ regs e model fsv,
  (1 ≤ e) → (e ≤ 4095) →
  reg_get regs 10 = errno_ret e →
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 1 = (0x11040 : word) →
  m_fs model = fsv →
  to_fout source_segs (mkst regs (0x11180 : word) (fmem inp rsp rrnd) rrom) model
    (fun o => o = (Z_to_bv 64 3, fsv)) := by
  intro regs e model fsv He1 He2 H10 H2 H1 Hfs
  apply tfo_msteps source_segs
  · stepjr SF_11180 SD_11180 (0x11040 : word) (getr_resolve; exact H1)
    stepiv SF_11040 SD_11040 (errno_ret e)
      (getr_resolve; rw [H10]; imm_norm; exact v_addi_0 _)
    stepiv SF_11044 SD_11044 (Z_to_bv 64 3) (getr_resolve; bveq)
    step_intro
    · rfl
    · apply step_blt_tk (Hf := SF_11048) (He := rfl) (Hd := SD_11048)
      getr_resolve; regupd_resolve; apply c_lts_errno <;> omega
    norm_pc
    exact msteps.mst_refl _
  apply source_fepilogue inp rsp rrnd Hsp_lo Hsp_hi
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · decide +kernel
  · exact smem_inv_fmem inp rsp rrnd Hsp_lo Hsp_hi
  · exact Hfs

include Hsp_lo Hsp_hi in
theorem src_open2_err_tail : ∀ regs e model fsv,
  (1 ≤ e) → (e ≤ 4095) →
  reg_get regs 10 = errno_ret e →
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 1 = (0x1106c : word) →
  m_fs model = fsv →
  to_fout source_segs (mkst regs (0x11180 : word) (fmem inp rsp rrnd) rrom) model
    (fun o => o = (Z_to_bv 64 4, fsv)) := by
  intro regs e model fsv He1 He2 H10 H2 H1 Hfs
  apply tfo_msteps source_segs
  · stepjr SF_11180 SD_11180 (0x1106c : word) (getr_resolve; exact H1)
    stepiv SF_1106c SD_1106c (errno_ret e)
      (getr_resolve; rw [H10]; imm_norm; exact v_addi_0 _)
    stepiv SF_11070 SD_11070 (Z_to_bv 64 4) (getr_resolve; bveq)
    step_intro
    · rfl
    · apply step_blt_tk (Hf := SF_11074) (He := rfl) (Hd := SD_11074)
      getr_resolve; regupd_resolve; apply c_lts_errno <;> omega
    norm_pc
    exact msteps.mst_refl _
  apply source_fepilogue inp rsp rrnd Hsp_lo Hsp_hi
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · decide +kernel
  · exact smem_inv_fmem inp rsp rrnd Hsp_lo Hsp_hi
  · exact Hfs

theorem src_open2_to_loop : ∀ regs fd fd2,
  reg_get regs 10 = fd2 →
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 3 = (0x13800 : word) →
  reg_get regs 18 = fd →
  reg_get regs 1 = (0x1106c : word) →
  (bv_unsigned fd < 2 ^ 31) → (bv_unsigned fd2 < 2 ^ 31) →
  ∃ regsH,
    reg_get regsH 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
    reg_get regsH 3 = (0x13800 : word) ∧
    reg_get regsH 8 = sbuf ∧
    reg_get regsH 18 = fd ∧ reg_get regsH 9 = fd2 ∧
    msteps source_segs (mkst regs (0x11180 : word) (fmem inp rsp rrnd) rrom)
                       (mkst regsH (0x1107c : word) (fmem inp rsp rrnd) rrom) := by
  intro regs fd fd2 H10 H2 H3 H18 H1 Hlt Hlt2
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 70016) (fmem inp rsp rrnd) rrom)
    5 [false] ([] : List expr)
    [((1 : reg), ELit 0x1106c), ((3 : reg), ELit 0x13800), ((10 : reg), EVar 32)]
    [fd2] ([] : List word) R HR Hms
  · apply c_lts_pos_0; omega
  · exact H1
  · exact H3
  · exact H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, Hms⟩
  all_goals s_out HR

/-- Register and model invariants at the bounded copy-loop head. -/
def sLH (rsp fdin fdout : word) (regs : bvmap 5 word) : Prop :=
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
  reg_get regs 3 = (0x13800 : word) ∧ reg_get regs 8 = sbuf ∧
  reg_get regs 18 = fdin ∧ reg_get regs 9 = fdout

def sMI (fs0v : Fs) (srcp dstp : path) (D : List byte) (fdin fdout : word)
    (k : Nat) (model : Model) : Prop :=
  m_halted model = none ∧ m_vm_lazy model = [] ∧
  fd_lookup (m_fds model) fdin = some (FdFile srcp (nat_to_word k)) ∧
  fd_lookup (m_fds model) fdout = some (FdFileW dstp (nat_to_word k)) ∧
  m_fs model = fs_set fs0v dstp (D.take k)

def model0 : Model := init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp

def sX (o : word × Fs) : Prop :=
  o = (Z_to_bv 64 3, in_fs inp) ∨ o = (Z_to_bv 64 4, in_fs inp)

theorem huge_chunk (d0 : List byte) (Hbig : 2^64 ≤ (d0.length : Int)) (off : word) :
    1 ≤ ((file_read d0 off (Z_to_bv 64 1024)).length : Int) ∧
    ((file_read d0 off (Z_to_bv 64 1024)).length : Int) ≤ 1024 := by
  rw [length_file_read, wtn_1024]
  have Hr := u64_range off
  have Hoff : (word_to_nat off : Int) = bv_unsigned off := rfl
  omega

def sO1pins (inp : ProcInput) (rsp : word) (regs : bvmap 5 word) : Prop :=
  bv_unsigned (getr regs 17) = 56 ∧
  reg_get regs 10 = AT_FDCWD ∧ reg_get regs 11 = (psrc inp rsp) ∧
  reg_get regs 12 = Z_to_bv 64 0 ∧
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
  reg_get regs 3 = (0x13800 : word) ∧
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
  reg_get regs 1 = (0x11040 : word)

def o1rec (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (regs : bvmap 5 word) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := (0x1117c : word),
     ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
     ms_mem := (fmem inp rsp rrnd), ms_rom := rrom }

def model1 (inp : ProcInput) (rsp rbrk rmb : word) (fd : word) : Model :=
  with_fds (fd_insert (m_fds (model0 inp rsp rbrk rmb)) fd (FdFile (src inp) (Z_to_bv 64 0))) (model0 inp rsp rbrk rmb)

def sO2pins (inp : ProcInput) (rsp : word) (regs : bvmap 5 word) (fd : word) : Prop :=
  bv_unsigned (getr regs 17) = 56 ∧
  reg_get regs 10 = AT_FDCWD ∧ reg_get regs 11 = (pdst inp rsp) ∧
  reg_get regs 12 = Z_to_bv 64 577 ∧
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
  reg_get regs 3 = (0x13800 : word) ∧
  reg_get regs 18 = fd ∧
  reg_get regs 1 = (0x1106c : word)

def o2rec (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (regs : bvmap 5 word) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := (0x1117c : word),
     ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
     ms_mem := (fmem inp rsp rrnd), ms_rom := rrom }

def sRpins (rsp : word) (regs : bvmap 5 word) (fdin fdout : word) : Prop :=
  bv_unsigned (getr regs 17) = 63 ∧
  reg_get regs 10 = fdin ∧ reg_get regs 11 = sbuf ∧
  reg_get regs 12 = Z_to_bv 64 1024 ∧
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
  reg_get regs 1 = (0x1109c : word) ∧
  reg_get regs 3 = (0x13800 : word) ∧
  reg_get regs 8 = sbuf ∧
  reg_get regs 9 = fdout ∧ reg_get regs 18 = fdin

def rdrec  (regs : bvmap 5 word) (mem : word → Option byte)
    : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := (0x1117c : word),
     ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
     ms_mem := mem,
     ms_rom := rrom }

def sHM (inp : ProcInput) (fdin fdout : word) (model : Model) : Prop :=
  m_halted model = none ∧
  m_vm_lazy model = [] ∧
  ∃ (off : word) (data : List byte),
    fd_lookup (m_fds model) fdin = some (FdFile (src inp) off) ∧
    fd_lookup (m_fds model) fdout = some (FdFileW (dst inp) off) ∧
    m_fs model = fs_set (in_fs inp) (dst inp) data ∧
    (bv_unsigned off ≤ (data.length : Int))

def sAnchor (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (c : config) : Prop :=
  ∃ fdin fdout regs mem model,
    fdin ≠ fdout ∧ fd32 fdin = fdin ∧ fd32 fdout = fdout ∧
    (sRpins rsp) regs fdin fdout ∧ (smem_inv inp rsp rrnd) mem ∧
    (sHM inp) fdin fdout model ∧ c = mkCfg (rdrec regs mem) model

def sHI (inp : ProcInput) (rsp : word) (rrnd : EntryDraw) (rbrk rmb : word) (c : config) : Prop :=
  (∃ ms regs1, (sO1pins inp rsp) regs1 ∧
     msteps source_segs ms ((o1rec inp rsp rrnd) regs1) ∧ c = mkCfg ms (model0 inp rsp rbrk rmb))
  ∨
  (∃ ms regs2 fd, fd_lookup (m_fds (model0 inp rsp rbrk rmb)) fd = none ∧
     (bv_unsigned fd < 2^31) ∧ (sO2pins inp rsp) regs2 fd ∧
     msteps source_segs ms ((o2rec inp rsp rrnd) regs2) ∧ c = mkCfg ms ((model1 inp rsp rbrk rmb) fd))
  ∨
  (∃ c'', dsil source_segs c c'' ∧ (sAnchor inp rsp rrnd) c'')

open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

theorem src_openat_enoent_empty : ∀ ms model x8 p U,
  ms.ms_svc_pending = some x8 →
  bv_unsigned x8 = 56 →
  modeled_open_flags (ms_gpr ms 2) = true →
  ms_gpr ms 0 = AT_FDCWD →
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p →
  path_eqb p [] = true →
  m_halted model = none →
  m_vm_lazy model = [] →
  to_fout source_segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret ENOENT) [] []))))
          model U →
  to_fout source_segs ms model U := by
  intro ms model x8 p U Hsvc Hno Hfl Hdirfd Hpath Hpe Hh Hlazy Hcont
  have Hchk : ∀ eff, check_syscall (sys_input source_segs ms x8) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [] := by
    intro eff
    rw [check_syscall_56 source_segs ms x8 eff model Hno]
    simp only [check_openat, Hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      check_openat_body, in_mem_si, Hpath, Hpe]
    exact check_copyins_after_ret_only _ _ _ _ _
  have Hagree : lookups_agree_at (bv_unsigned (sys_input source_segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]
    rfl
  refine tfo_sys_det source_segs ms model x8
    (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] []))
    model U Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
  · apply check_syscall_sound_ok
    rw [Hchk, check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff2 m2 evs2 Hs
    have H := check_syscall_complete_ok _ _ _ _ _ Hagree Hs
    rw [Hchk, check_ret_only_copyins_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ H

theorem src_open_empty_rec : ∀ regs pc mem model p U,
  bv_unsigned (getr regs 17) = 56 →
  modeled_open_flags (reg_get regs 12) = true →
  reg_get regs 10 = AT_FDCWD →
  read_cstr (mrb source_segs mem) (reg_get regs 11) = CstrOk p →
  path_eqb p [] = true →
  m_halted model = none →
  m_vm_lazy model = [] →
  to_fout source_segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
                     mem (seg_rom source_segs))
          model U →
  to_fout source_segs
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
                  ms_svc_pending := some (getr regs 17),
                  ms_resv := none, ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs }
          model U := by
  intro regs pc mem model p U H17 Hfl H10 Hpath Hpe Hh Hlazy Hcont
  apply src_openat_enoent_empty
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom source_segs } model (getr regs 17) p U rfl H17 Hfl H10 Hpath Hpe Hh Hlazy
  simpa only [adv_eff_ret_copyins] using Hcont

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_empty :
  (List.length (src inp) ≤ 4095) →
  path_eqb (src inp) [] = true →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp))) := by
  intro Hlen Hse

  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl)

  apply src_open_empty_rec (p := src inp)
  · exact H17
  · rw [H12]; decide +kernel
  · exact H10
  · rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen
  · exact Hse
  · rfl
  · rfl

  · norm_pc
    apply src_open1_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENOENT)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact H2
    · regupd_resolve; exact H1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_toolong :
  (4096 ≤ List.length (src inp)) →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp))) := by
  intro Hlen

  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl)

  apply tfo_open_toolong_rec
  · exact H17
  · rw [H12]; decide +kernel
  · rw [H11]; exact source_cstr_src_toolong inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen
  · rfl
  · rfl

  · norm_pc
    apply src_open1_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENAMETOOLONG)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact H2
    · regupd_resolve; exact H1
    · rfl

variable (Hsrc_nodot : openat_plain_name (src inp) = true)

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem source_absent :
  (List.length (src inp) ≤ 4095) →
  fs_lookup (in_fs inp) (src inp) = none →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (cp_outcomes (in_fs inp) (src inp) (dst inp)) := by
  intro Hlen Hnone
  apply tfo_equiv source_segs (U := fun o => o = (Z_to_bv 64 3, in_fs inp))
  rotate_left
  · intro o; simp only [cp_outcomes, Hnone]

  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl)

  apply tfo_open_enoent_rec (p := src inp)
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen
  · exact Hsrc_nodot
  · exact Hnone
  · rfl
  · rfl

  · norm_pc
    apply src_open1_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENOENT)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact H2
    · regupd_resolve; exact H1
    · rfl

include Hsp_lo Hsp_hi in
theorem src_read_err_tail : ∀ regs e model fsv,
  (1 ≤ e) → (e ≤ 4095) →
  reg_get regs 10 = errno_ret e →
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
  reg_get regs 1 = (0x1109c : word) →
  m_fs model = fsv →
  to_fout source_segs (mkst regs (0x11180 : word) (fmem inp rsp rrnd) rrom) model
    (fun o => o = (Z_to_bv 64 5, fsv)) := by
  intro regs e model fsv He1 He2 H10 H2 H1 Hfs
  apply tfo_msteps source_segs
  · stepjr SF_11180 SD_11180 (0x1109c : word) (getr_resolve; exact H1)
    step_intro
    · rfl
    · apply step_blt_tk (Hf := SF_1109c) (He := rfl) (Hd := SD_1109c)
      getr_resolve; rw [H10]; apply c_lts_errno <;> omega
    norm_pc
    stepiv SF_1111c SD_1111c (Z_to_bv 64 5) (getr_resolve; bveq)
    stepj SF_11120 SD_11120
    exact msteps.mst_refl _
  apply source_fepilogue inp rsp rrnd Hsp_lo Hsp_hi
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · decide +kernel
  · exact smem_inv_fmem inp rsp rrnd Hsp_lo Hsp_hi
  · exact Hfs

open LinuxProcessSemantics.Common.SimInv

include Hsp_lo Hsp_hi in
private theorem close_call (regs : bvmap 5 word) (mem : word → Option byte)
    (fdv raM s0v g3 g9 g18 : word) (model : Model) (e : FdEntry) (U : word × Fs → Prop)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H10 : reg_get regs 10 = fdv) (H1 : reg_get regs 1 = raM)
    (H8 : reg_get regs 8 = s0v) (H3 : reg_get regs 3 = g3)
    (H9 : reg_get regs 9 = g9) (H18 : reg_get regs 18 = g18)
    (Hsm : smem_inv inp rsp rrnd mem) (Hra : v_jalr raM 0 = raM)
    (Hfd : fd_lookup (m_fds model) fdv = some e) (Hfd32 : fd32 fdv = fdv)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : ∀ regs',
      reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
      reg_get regs' 10 = Z_to_bv 64 0 → reg_get regs' 1 = raM →
      reg_get regs' 8 = s0v → reg_get regs' 3 = g3 →
      reg_get regs' 9 = g9 → reg_get regs' 18 = g18 →
      smem_inv inp rsp rrnd
        (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 raM)) →
      to_fout source_segs
        (mkst regs' raM
          (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 raM)) rrom)
        (with_fds (fd_remove (m_fds model) fdv) model) U) :
    to_fout source_segs (mkst regs 0x11188 mem rrom) model U := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨regsB, B17, B10, B2, B1, B8, B3, B9, B18, HB⟩ :=
    src_close_entry inp rsp rrnd Hsp_lo Hsp_hi regs mem fdv raM s0v g3 g9 g18
      H2 H10 H1 H8 H3 H9 H18 (smem_inv_grows inp rsp rrnd mem Hsm)
  apply tfo_msteps source_segs _ _ _ _ HB
  apply tfo_close_rec source_segs (fdv := fdv) (e := e)
    (H17 := B17) (H10 := B10) (Hfd := Hfd) (Hfd32 := Hfd32) (Hh := Hh) (Hlazy := Hlazy)
  norm_pc
  obtain ⟨regsC, C2, C10, C1, C8, C3, C9, C18, HC⟩ :=
    src_close_tail rsp Hsp_lo Hsp_hi (regupd regsB 10 (Z_to_bv 64 0))
      (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 raM))
      raM s0v g3 g9 g18
      (by regupd_resolve; exact B2) (by regupd_resolve; rfl)
      (by regupd_resolve; exact B1) (by regupd_resolve; exact B8)
      (by regupd_resolve; exact B3) (by regupd_resolve; exact B9)
      (by regupd_resolve; exact B18) Hra (by apply rdn_wbytes_hit8; u_norm; omega)
  apply tfo_msteps source_segs _ _ _ _ HC
  apply Hcont regsC C2 C10 C1 C8 C3 C9 C18
  obtain ⟨Fra, F16, F24, F32, Fg⟩ := Hsm
  unfold smem_inv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | solve | solve_mem_grows
  | (rw [rdn_wbytes_disjoint _ _ _ _ _ _
      (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]; assumption)


section SourceLoop
variable (fs0v : Fs) (srcp dstp : path) (D : List byte) (fdin fdout : word)
variable (HD : fs_lookup (fs_set fs0v dstp []) srcp = some D)
variable (Hneq : fdin ≠ fdout)
variable (Hfin31 : bv_unsigned fdin < 2^31) (Hfout31 : bv_unsigned fdout < 2^31)
variable (HDlen : (D.length : Int) < 2^64)

include Hsp_lo Hsp_hi HD Hneq Hfin31 Hfout31 HDlen in
theorem source_loop : ∀ rem k regs mem model,
    D.length - k < rem → k ≤ D.length →
    sLH rsp fdin fdout regs → smem_inv inp rsp rrnd mem →
    sMI fs0v srcp dstp D fdin fdout k model →
    to_fout source_segs (mkst regs 0x1107c mem rrom) model
      (fun o => o = (Z_to_bv 64 0, fs_set fs0v dstp D)) := by
  intro rem
  induction rem with
  | zero => intro k regs mem model Hrem; omega
  | succ rem IH =>
    intro k regs mem model Hrem Hk HLH Hsm HMI
    obtain ⟨H2, H3, H8, H18, H9⟩ := HLH
    obtain ⟨Hh, Hlazy, Hfdin, Hfdout, Hfs⟩ := HMI
    have Hlo := rsp_lo_num rsp Hsp_lo
    have Hhi := rsp_hi_num rsp Hsp_hi
    have HkZ : (k : Int) < 2^64 := by omega
    let chunk := file_read D (nat_to_word k) (Z_to_bv 64 1024)
    have Hclen : chunk.length = min 1024 (D.length - k) := cp_chunk_len D k HkZ
    have Hc1024 : chunk.length ≤ 1024 := by omega
    obtain ⟨regsR, R17, R10, R11, R12, R2, R1, R3, R8, R9, R18, HmsR⟩ :=
      src_head_to_read rsp regs mem fdin fdout H2 H3 H8 H18 H9
    apply tfo_msteps source_segs _ _ _ _ HmsR
    apply tfo_read_rec source_segs (p := srcp) (off := nat_to_word k) (data := D)
      (buf := sbuf) (cnt := Z_to_bv 64 1024) (fdv := fdin)
      (H17 := R17) (H10 := R10) (H11 := R11) (H12 := R12) (Hfd := Hfdin)
      (Hfd32 := fd32_lt31 _ Hfin31) (Hh := Hh) (Hlazy := Hlazy)
    · rw [Hfs]; exact cp_lookup_src_k fs0v srcp dstp D k HD Hk
    · exact source_buf_wseg
    · decide +kernel
    · decide +kernel
    · decide +kernel
    change to_fout source_segs
      (mkst (regupd regsR 10 (len_word chunk)) (v_addi 0x1117c 4)
        (write_to_mem mem sbuf chunk) rrom)
      (with_fds (fd_insert (m_fds model) fdin
        (FdFile srcp (nat_to_word k + len_word chunk))) model) _
    norm_pc
    by_cases Heq : k = D.length
    · have Hchn : chunk = [] := by
        apply file_read_nil
        rw [wtn_ntw _ HkZ]; omega
      rw [Hchn]
      simp only [write_to_mem, len_word, List.length_nil, Int.natCast_zero]
      rw [show Z_to_bv 64 (0 : Int) = nat_to_word 0 from rfl, word_add_0]
      sym_block_ex source_segs
        (mkst (regupd regsR 10 (Z_to_bv 64 0)) (Z_to_bv 64 70016) mem rrom)
        5 [false, true] ([] : List expr)
        [((1 : reg), ELit 0x1109c), ((10 : reg), ELit 0), ((18 : reg), EVar 32)]
        [fdin] ([] : List word) RA HRA HA
      · decide +kernel
      all_goals try (getr_resolve; regupd_resolve; first | rfl | exact R1 | exact R18)
      apply tfo_msteps source_segs _ _ _ _ HA
      apply close_call inp rsp rrnd Hsp_lo Hsp_hi (fdv := fdin) (raM := (0x110f0 : word))
        (s0v := sbuf) (g3 := (0x13800 : word)) (g9 := fdout) (g18 := fdin)
      · s_out HRA
      · sym_regs HRA; getr_resolve; exact v_addiw_id fdin Hfin31
      · s_out HRA
      · s_out HRA
      · s_out HRA
      · s_out HRA
      · s_out HRA
      · exact Hsm
      · decide +kernel
      · model_simp; exact fd_lookup_insert_eq _ _ _
      · exact fd32_lt31 _ Hfin31
      · exact Hh
      · exact Hlazy
      · intro regsC C2 C10 C1 C8 C3 C9 C18 HsmC
        sym_block_ex source_segs
          (mkst regsC (Z_to_bv 64 0x110f0)
            (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 (0x110f0 : word))) rrom)
          2 [] ([] : List expr) [((9 : reg), EVar 32)] [fdout] ([] : List word) RC HRC HC
        · exact C9
        apply tfo_msteps source_segs _ _ _ _ HC
        apply close_call inp rsp rrnd Hsp_lo Hsp_hi (fdv := fdout) (raM := (0x110f8 : word))
          (s0v := sbuf) (g3 := (0x13800 : word)) (g9 := fdout) (g18 := fdin)
        · s_out HRC
        · sym_regs HRC; getr_resolve; exact v_addiw_id fdout Hfout31
        · s_out HRC
        · s_out HRC
        · s_out HRC
        · s_out HRC
        · s_out HRC
        · exact HsmC
        · decide +kernel
        · model_simp
          rw [fd_lookup_remove_neq _ _ _ (Ne.symm Hneq), fd_lookup_insert_neq _ _ _ _ (Ne.symm Hneq)]
          exact Hfdout
        · exact fd32_lt31 _ Hfout31
        · exact Hh
        · exact Hlazy
        · intro regsE E2 E10 E1 E8 E3 E9 E18 HsmE
          apply to_fout.tfo_step _ _ _ _ rfl
            (step_addi_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
              SF_110f8 rfl SD_110f8 rfl (by getr_resolve; bveq))
          norm_pc
          apply source_fepilogue inp rsp rrnd Hsp_lo Hsp_hi
          · regupd_resolve; exact E2
          · regupd_resolve; rfl
          · decide +kernel
          · exact HsmE
          · change m_fs model = _
            rw [Hfs, Heq, List.take_length]
    · have Hc1 : 1 ≤ chunk.length := by omega
      have HuLen := u_len_word chunk (by omega)
      obtain ⟨regsW, W17, W10, W11, W12, W8, W2, W1, W3, W9, W18, HmsW⟩ :=
        src_read_to_write inp rsp rrnd Hsp_lo Hsp_hi
          (regupd regsR 10 (len_word chunk)) (write_to_mem mem sbuf chunk) fdin fdout (len_word chunk)
          (by regupd_resolve; rfl) (by omega) (by omega)
          (by regupd_resolve; exact R1) (by regupd_resolve; exact R2)
          (by regupd_resolve; exact R3) (by regupd_resolve; exact R8)
          (by regupd_resolve; exact R9) (by regupd_resolve; exact R18)
          (by apply mem_grows_trans _ _ _ (smem_inv_grows inp rsp rrnd mem Hsm); apply write_to_mem_grows)
      apply tfo_msteps source_segs _ _ _ _ HmsW
      apply tfo_write_rec source_segs (p := dstp) (off := nat_to_word k) (data := D.take k)
        (bs := chunk) (buf := sbuf) (cnt := len_word chunk) (fdv := fdout)
        (H17 := W17) (H10 := W10) (H11 := W11) (H12 := W12)
      · model_simp; rw [fd_lookup_insert_neq _ _ _ _ (Ne.symm Hneq)]; exact Hfdout
      · exact fd32_lt31 _ Hfout31
      · rw [wtn_len_word chunk (by omega)]
        unfold spill
        repeat rw [rdn_wbytes_below _ _ _ _ _ _
          (by rw [u_sbuf]; u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]
        apply rdn_write_to_mem; rw [u_sbuf]; omega
      · rw [HuLen]; unfold rw_bytes_max; omega
      · change fs_lookup (m_fs model) dstp = _
        rw [Hfs]; exact fs_lookup_set_eq _ _ _
      · apply file_gap_in_range
        rw [u_ntw _ HkZ, List.length_take]; unfold rw_bytes_max; omega
      · right; rw [HuLen]; omega
      · exact Hh
      · exact Hlazy
      norm_pc
      obtain ⟨regsH, G2, G3, G8, G9, G18, HmsH⟩ :=
        src_write_to_head rsp Hsp_lo Hsp_hi (regupd regsW 10 (len_word chunk))
          (spill rsp (write_to_mem mem sbuf chunk) (len_word chunk)) fdin fdout (len_word chunk)
          (by regupd_resolve; rfl) (by omega) (by omega)
          (by regupd_resolve; exact W1) (by regupd_resolve; exact W2)
          (by regupd_resolve; exact W3) (by regupd_resolve; exact W8)
          (by regupd_resolve; exact W9) (by regupd_resolve; exact W18)
          (rdn_spill_cnt rsp Hsp_lo Hsp_hi _ _) (rdn_spill_ptr rsp Hsp_lo Hsp_hi _ _)
      apply tfo_msteps source_segs _ _ _ _ HmsH
      apply IH (k + chunk.length)
      · omega
      · omega
      · exact ⟨G2, G3, G8, G18, G9⟩
      · apply smem_inv_spill inp rsp rrnd Hsp_lo Hsp_hi
        exact smem_inv_wtm inp rsp rrnd Hsp_lo Hsp_hi mem chunk Hsm (by omega)
      · refine ⟨Hh, Hlazy, ?_, ?_, ?_⟩
        · model_simp
          rw [fd_lookup_insert_neq _ _ _ _ Hneq, fd_lookup_insert_eq, len_word_ntw, ntw_add]
        · model_simp
          rw [fd_lookup_insert_eq, len_word_ntw, ntw_add]
        · change fs_set (m_fs model) dstp (file_write (D.take k) (nat_to_word k) chunk) = _
          rw [Hfs, cp_fs_write_step fs0v dstp D k Hk HDlen]
          rw [← Hclen]

end SourceLoop

include Hva Hve Hsp_lo Hsp_hi Hge3 in
private theorem source_open_first (entry : FdEntry) (V : word × Fs → Prop)
    (Hopen : ∀ regs,
      bv_unsigned (getr regs 17) = 56 → reg_get regs 10 = AT_FDCWD →
      reg_get regs 11 = psrc inp rsp → reg_get regs 12 = Z_to_bv 64 0 →
      (∀ e, e ∈ openat_errnos → to_fout source_segs
        (mkst (regupd regs 10 (errno_ret e)) (v_addi 0x1117c 4) (fmem inp rsp rrnd) rrom)
        (model0 inp rsp rbrk rmb) (fun o => o = (Z_to_bv 64 3, in_fs inp))) →
      (∀ fd, fd_lookup (m_fds (model0 inp rsp rbrk rmb)) fd = none →
        fd = alloc_fd (m_fds (model0 inp rsp rbrk rmb)) →
        to_fout source_segs
          (mkst (regupd regs 10 fd) (v_addi 0x1117c 4) (fmem inp rsp rrnd) rrom)
          (with_fds (fd_insert (m_fds (model0 inp rsp rbrk rmb)) fd entry)
            (model0 inp rsp rbrk rmb)) V) →
      to_fout source_segs (o1rec inp rsp rrnd regs) (model0 inp rsp rbrk rmb)
        (fun o => o = (Z_to_bv 64 3, in_fs inp) ∨ V o))
    (Hcont : ∀ regs, sO2pins inp rsp regs (Z_to_bv 64 3) →
      to_fout source_segs (o2rec inp rsp rrnd regs)
        (with_fds (fd_insert (m_fds (model0 inp rsp rbrk rmb)) (Z_to_bv 64 3) entry)
          (model0 inp rsp rbrk rmb)) V) :
    to_fout source_segs
      (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd
        (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (model0 inp rsp rbrk rmb) (fun o => o = (Z_to_bv 64 3, in_fs inp) ∨ V o) := by
  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl)
  apply Hopen regs1 H17 H10 H11 H12
  · intro e He
    obtain ⟨He1, He2⟩ := openat_errno_range e He
    norm_pc
    exact src_open1_err_tail inp rsp rrnd Hsp_lo Hsp_hi _ e _ _ He1 He2
      (by regupd_resolve; rfl) (by regupd_resolve; exact H2)
      (by regupd_resolve; exact H1) rfl
  · intro fd Hlk Hfd
    have Hfd3 : fd = Z_to_bv 64 3 := by rw [Hfd]; rfl
    subst fd
    obtain ⟨regs2, K2, K3, K18, K8, K1, K17, K10, K11, K12, Hms2⟩ :=
      source_to_open2 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
        (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        (by regupd_resolve; exact H2) (by regupd_resolve; exact H3)
        (by regupd_resolve; exact H8) (by regupd_resolve; exact H1)
        (by regupd_resolve; rfl) (by decide +kernel)
    norm_pc
    apply tfo_msteps source_segs _ _ _ _ Hms2
    apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl)
    exact Hcont regs2 ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
private theorem source_open_file (d0 : List byte) (V : word × Fs → Prop)
    (Hlen : (src inp).length ≤ 4095) (Hsne : path_eqb (src inp) [] = false)
    (Hsome : fs_lookup (in_fs inp) (src inp) = some d0)
    (Hcont : ∀ regs, sO2pins inp rsp regs (Z_to_bv 64 3) →
      to_fout source_segs (o2rec inp rsp rrnd regs) (model1 inp rsp rbrk rmb (Z_to_bv 64 3)) V) :
    to_fout source_segs
      (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd
        (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (model0 inp rsp rbrk rmb) (fun o => o = (Z_to_bv 64 3, in_fs inp) ∨ V o) := by
  apply source_open_first inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3
    (FdFile (src inp) (Z_to_bv 64 0)) V
  · intro regs H17 H10 H11 H12 Herr Hok
    apply tfo_open_rd_rec source_segs (model := model0 inp rsp rbrk rmb) (p := src inp) (d := d0)
      (Te := fun _ o => o = (Z_to_bv 64 3, in_fs inp)) (Ts := fun _ => V)
      (H17 := H17) (H10 := H10) (H12 := H12)
      (Hpe := Hsne) (Hdot := Hsrc_nodot) (Hfs := Hsome)
      (Hh := rfl) (Hlazy := rfl) (Herr := Herr) (Hok := Hok)
    · rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen
    · intro o; constructor
      · intro H; rcases H with H | H
        · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
        · exact Or.inr ⟨Z_to_bv 64 3, rfl, rfl, H⟩
      · intro H; rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
        · exact Or.inl H
        · exact Or.inr H
  · exact Hcont

include Hva Hve Hsp_lo Hsp_hi Hge3 in
private theorem source_open_dot (V : word × Fs → Prop)
    (Hsdot : path_eqb (src inp) dot_path = true)
    (Hcont : ∀ regs, sO2pins inp rsp regs (Z_to_bv 64 3) →
      to_fout source_segs (o2rec inp rsp rrnd regs)
        (with_fds (fd_insert (m_fds (model0 inp rsp rbrk rmb)) (Z_to_bv 64 3) FdDir)
          (model0 inp rsp rbrk rmb)) V) :
    to_fout source_segs
      (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd
        (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (model0 inp rsp rbrk rmb) (fun o => o = (Z_to_bv 64 3, in_fs inp) ∨ V o) := by
  have Hsrc : src inp = dot_path := (path_eqb_eq _ _).mp Hsdot
  apply source_open_first inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 FdDir V
  · intro regs H17 H10 H11 H12 Herr Hok
    apply tfo_open_rd_dot_rec source_segs (model := model0 inp rsp rbrk rmb) (p := src inp)
      (Te := fun _ o => o = (Z_to_bv 64 3, in_fs inp)) (Ts := fun _ => V)
      (H17 := H17) (H10 := H10) (H12 := H12)
      (Hpe := by rw [Hsrc]; decide +kernel) (Hdot := Hsdot)
      (Hh := rfl) (Hlazy := rfl) (Herr := Herr) (Hok := Hok)
    · rw [H11]; apply source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
      rw [Hsrc]; decide +kernel
    · intro o; constructor
      · intro H; rcases H with H | H
        · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
        · exact Or.inr ⟨Z_to_bv 64 3, rfl, rfl, H⟩
      · intro H; rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
        · exact Or.inl H
        · exact Or.inr H
  · exact Hcont

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem source_present_dst_empty : ∀ d0,
  (List.length (src inp) ≤ 4095) → (List.length (dst inp) ≤ 4095) →
  path_eqb (src inp) [] = false → path_eqb (dst inp) [] = true →
  fs_lookup (in_fs inp) (src inp) = some d0 →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp))) := by
  intro d0 Hlen1 Hlen2 Hsne Hde Hsome
  apply source_open_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 Hsrc_nodot d0 _ Hlen1 Hsne Hsome
  intro regs Hpins
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  apply src_open_empty_rec (p := dst inp)
  · exact K17
  · rw [K12]; decide +kernel
  · exact K10
  · rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
  · exact Hde
  · rfl
  · rfl
  · norm_pc
    apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENOENT)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact K2
    · regupd_resolve; exact K1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem source_present_dst_dot : ∀ d0,
  (List.length (src inp) ≤ 4095) → (List.length (dst inp) ≤ 4095) →
  path_eqb (src inp) [] = false → path_eqb (dst inp) dot_path = true →
  fs_lookup (in_fs inp) (src inp) = some d0 →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp))) := by
  intro d0 Hlen1 Hlen2 Hsne Hde Hsome
  have Hdne : path_eqb (dst inp) [] = false := by
    rw [(path_eqb_eq _ _).mp Hde]; decide +kernel
  apply source_open_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 Hsrc_nodot d0 _ Hlen1 Hsne Hsome
  intro regs Hpins
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  apply tfo_open_wr_dot_rec source_segs (p := dst inp)
  · exact K17
  · exact K10
  · rw [K12]; decide +kernel
  · rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
  · exact Hdne
  · exact Hde
  · rfl
  · rfl
  · norm_pc
    apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := EISDIR)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact K2
    · regupd_resolve; exact K1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem source_present_dst_toolong : ∀ d0,
  (List.length (src inp) ≤ 4095) → (4096 ≤ List.length (dst inp)) →
  path_eqb (src inp) [] = false →
  fs_lookup (in_fs inp) (src inp) = some d0 →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp))) := by
  intro d0 Hlen1 Hlen2 Hsne Hsome
  apply source_open_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 Hsrc_nodot d0 _ Hlen1 Hsne Hsome
  intro regs Hpins
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  apply tfo_open_toolong_rec source_segs
  · exact K17
  · rw [K12]; decide +kernel
  · rw [K11]; exact source_cstr_dst_toolong inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
  · rfl
  · rfl
  · norm_pc
    apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENAMETOOLONG)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact K2
    · regupd_resolve; exact K1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot_dstempty :
  path_eqb (src inp) dot_path = true → path_eqb (dst inp) [] = true →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp))) := by
  intro Hsdot Hde
  have Hdst := (path_eqb_eq _ _).mp Hde
  have Hlen2 : (dst inp).length ≤ 4095 := by rw [Hdst]; decide +kernel
  apply source_open_dot inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  intro regs Hpins
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  apply src_open_empty_rec (p := dst inp)
  · exact K17
  · rw [K12]; decide +kernel
  · exact K10
  · rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
  · exact Hde
  · rfl
  · rfl
  · norm_pc
    apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENOENT)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact K2
    · regupd_resolve; exact K1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot_dstdot :
  path_eqb (src inp) dot_path = true → path_eqb (dst inp) dot_path = true →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp))) := by
  intro Hsdot Hde
  have Hdst := (path_eqb_eq _ _).mp Hde
  have Hlen2 : (dst inp).length ≤ 4095 := by rw [Hdst]; decide +kernel
  have Hdne : path_eqb (dst inp) [] = false := by
    rw [(path_eqb_eq _ _).mp Hde]; decide +kernel
  apply source_open_dot inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  intro regs Hpins
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  apply tfo_open_wr_dot_rec source_segs (p := dst inp)
  · exact K17
  · exact K10
  · rw [K12]; decide +kernel
  · rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
  · exact Hdne
  · exact Hde
  · rfl
  · rfl
  · norm_pc
    apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := EISDIR)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact K2
    · regupd_resolve; exact K1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot_dst_toolong :
  path_eqb (src inp) dot_path = true → (4096 ≤ List.length (dst inp)) →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp))) := by
  intro Hsdot Hlen2
  apply source_open_dot inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  intro regs Hpins
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  apply tfo_open_toolong_rec source_segs
  · exact K17
  · rw [K12]; decide +kernel
  · rw [K11]; exact source_cstr_dst_toolong inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
  · rfl
  · rfl
  · norm_pc
    apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENAMETOOLONG)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact K2
    · regupd_resolve; exact K1
    · rfl

private def opened_source (entry : FdEntry) : Model :=
  with_fds (fd_insert (m_fds (model0 inp rsp rbrk rmb)) (Z_to_bv 64 3) entry)
    (model0 inp rsp rbrk rmb)

private def opened_both (entry : FdEntry) : Model :=
  with_fds (fd_insert (m_fds (opened_source inp rsp rbrk rmb entry)) (Z_to_bv 64 4)
    (FdFileW (dst inp) (Z_to_bv 64 0)))
    (with_fs (fs_set (in_fs inp) (dst inp) []) (opened_source inp rsp rbrk rmb entry))

include Hva Hve Hsp_lo Hsp_hi Hge3 in
private theorem source_open_second (entry : FdEntry) (V : word × Fs → Prop)
    (Hlen2 : (dst inp).length ≤ 4095) (Hdne : path_eqb (dst inp) [] = false)
    (Hplain : openat_plain_name (dst inp) = true)
    (Hsuccess : ∀ regs, sLH rsp (Z_to_bv 64 3) (Z_to_bv 64 4) regs →
      to_fout source_segs (mkst regs 0x1107c (fmem inp rsp rrnd) rrom)
        (opened_both inp rsp rbrk rmb entry) V)
    (regs : bvmap 5 word) (Hpins : sO2pins inp rsp regs (Z_to_bv 64 3)) :
    to_fout source_segs (o2rec inp rsp rrnd regs) (opened_source inp rsp rbrk rmb entry)
      (fun o => o = (Z_to_bv 64 4, in_fs inp) ∨
        (fs_under (in_fs inp) (dst inp) = false ∧ V o)) := by
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  cases Hun : fs_under (in_fs inp) (dst inp) with
  | true =>
    apply tfo_open_wr_isdir_rec source_segs (model := opened_source inp rsp rbrk rmb entry) (p := dst inp)
      (H17 := K17) (H10 := K10) (H12 := K12) (Hpe := Hdne) (Hdot := Hplain)
      (Hun := Hun) (Hh := rfl) (Hlazy := rfl)
    · rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
    · apply tfo_equiv source_segs (U := fun o => o = (Z_to_bv 64 4, in_fs inp))
      · norm_pc
        apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := EISDIR)
        · decide +kernel
        · decide +kernel
        · regupd_resolve; rfl
        · regupd_resolve; exact K2
        · regupd_resolve; exact K1
        · rfl
      · intro o; simp only [Bool.true_eq_false, false_and, or_false]
  | false =>
    apply tfo_open_wr_rec source_segs (model := opened_source inp rsp rbrk rmb entry) (p := dst inp)
      (Te := fun _ o => o = (Z_to_bv 64 4, in_fs inp)) (Ts := fun _ => V)
      (H17 := K17) (H10 := K10) (H12 := K12) (Hpe := Hdne) (Hdot := Hplain)
      (Hun := Hun) (Hh := rfl) (Hlazy := rfl)
    · rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2
    · intro e He
      obtain ⟨He1, He2⟩ := openat_errno_range e He
      norm_pc
      apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := e) <;>
        first | exact He1 | exact He2 | (regupd_resolve; rfl) |
          (regupd_resolve; exact K2) | (regupd_resolve; exact K1) | rfl
    · intro fd Hlk Hfd
      have Hfd4 : fd = Z_to_bv 64 4 := by rw [Hfd]; rfl
      subst fd
      obtain ⟨regsH, G2, G3, G8, G18, G9, HmsH⟩ :=
        src_open2_to_loop inp rsp rrnd (regupd regs 10 (Z_to_bv 64 4))
          (Z_to_bv 64 3) (Z_to_bv 64 4)
          (by regupd_resolve; rfl) (by regupd_resolve; exact K2)
          (by regupd_resolve; exact K3) (by regupd_resolve; exact K18)
          (by regupd_resolve; exact K1) (by decide +kernel) (by decide +kernel)
      norm_pc
      apply tfo_msteps source_segs _ _ _ _ HmsH
      exact Hsuccess regsH ⟨G2, G3, G8, G18, G9⟩
    · intro o; constructor
      · intro H; rcases H with H | ⟨_, H⟩
        · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
        · exact Or.inr ⟨Z_to_bv 64 4, rfl, rfl, H⟩
      · intro H; rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
        · exact Or.inl H
        · exact Or.inr ⟨rfl, H⟩

variable (Hdst_nodot : openat_plain_name (dst inp) = true)

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot in
theorem source_present : ∀ d0,
  (List.length (src inp) ≤ 4095) → (List.length (dst inp) ≤ 4095) →
  path_eqb (src inp) [] = false → path_eqb (dst inp) [] = false →
  fs_lookup (in_fs inp) (src inp) = some d0 →
  (((cp_read_data (in_fs inp) (src inp) (dst inp)).length : Int) < 2^64) →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (cp_outcomes (in_fs inp) (src inp) (dst inp)) := by
  intro d0 Hlen1 Hlen2 Hsne Hdne Hsome Hrep
  apply tfo_equiv source_segs
  · apply source_open_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 Hsrc_nodot
      d0 _ Hlen1 Hsne Hsome
    apply source_open_second inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3
      (FdFile (src inp) (Z_to_bv 64 0))
      (fun o => o = (Z_to_bv 64 0, cp_final_fs (in_fs inp) (src inp) (dst inp))) Hlen2 Hdne Hdst_nodot
    intro regs Hregs
    unfold cp_final_fs
    apply source_loop inp rsp rrnd Hsp_lo Hsp_hi
      (in_fs inp) (src inp) (dst inp) (cp_read_data (in_fs inp) (src inp) (dst inp))
      (Z_to_bv 64 3) (Z_to_bv 64 4)
      (cp_read_data_lookup _ _ _ d0 Hsome) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) Hrep
      ((cp_read_data (in_fs inp) (src inp) (dst inp)).length + 1) 0
    · omega
    · omega
    · exact Hregs
    · exact smem_inv_fmem inp rsp rrnd Hsp_lo Hsp_hi
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro o; simp only [cp_outcomes, Hsome]

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot_normal :
  path_eqb (src inp) dot_path = true →
  (List.length (dst inp) ≤ 4095) →
  path_eqb (dst inp) [] = false → openat_plain_name (dst inp) = true →
  to_fout source_segs
    (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (fun o => o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp))
              ∨ (fs_under (in_fs inp) (dst inp) = false
                  ∧ o = (Z_to_bv 64 5, fs_set (in_fs inp) (dst inp) []))) := by
  intro Hsdot Hlen2 Hdne Hplain
  apply source_open_dot inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  apply source_open_second inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3
    FdDir (fun o => o = (Z_to_bv 64 5, fs_set (in_fs inp) (dst inp) [])) Hlen2 Hdne Hplain
  intro regs Hregs
  obtain ⟨G2, G3, G8, G18, G9⟩ := Hregs
  obtain ⟨regsR, R17, R10, R11, R12, R2, R1, R3, R8, R9, R18, HR⟩ :=
    src_head_to_read rsp regs (fmem inp rsp rrnd) (Z_to_bv 64 3) (Z_to_bv 64 4)
      G2 G3 G8 G18 G9
  apply tfo_msteps source_segs _ _ _ _ HR
  apply tfo_read_dir_rec source_segs
  · exact R17
  · rw [R10]; rfl
  · rw [R10]; decide +kernel
  · rw [R11, R12]; decide +kernel
  · rfl
  · rfl
  · norm_pc
    apply src_read_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := EISDIR)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact R2
    · regupd_resolve; exact R1
    · rfl

section Huge
variable (d0 : List byte)
variable (Hplen1 : (src inp).length ≤ 4095) (Hplen2 : (dst inp).length ≤ 4095)
variable (Hsd : src inp ≠ dst inp)
variable (Hsome0 : fs_lookup (in_fs inp) (src inp) = some d0)
variable (Hbig : 2^64 ≤ (d0.length : Int))
variable (Hsne0 : path_eqb (src inp) [] = false) (Hdne0 : path_eqb (dst inp) [] = false)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem src_huge_start :
  (sHI inp rsp rrnd rbrk rmb) (mkCfg (init_machine_state source_segs 0x1112c source_phdrs rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (model0 inp rsp rbrk rmb)) := by
  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  refine Or.inl ⟨_, regs1, ⟨H17, H10, H11, H12, H2, H3, H8, H1⟩, ?_, rfl⟩
  apply msteps_trans _ _ _ _ Hms
  exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl) (msteps.mst_refl _)

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hplen1 Hsome0 Hsne0 in
theorem src_huge_open1_anchor : ∀ regs1 evs st,
  (sO1pins inp rsp) regs1 →
  sstep source_segs (mkCfg ((o1rec inp rsp rrnd) regs1) (model0 inp rsp rbrk rmb)) evs st →
  fdiv_resp source_segs (sHI inp rsp rrnd rbrk rmb) (sX inp) evs st := by
  intro regs1 evs st Hpins Hss
  obtain ⟨H17, H10, H11, H12, H2, H3, H8, H1⟩ := Hpins
  obtain ⟨Hne, Herr, Hok, Hinv⟩ := open_rd_branches source_segs
    (o1rec inp rsp rrnd regs1) (getr regs1 17) (model0 inp rsp rbrk rmb) (src inp) d0
    H17 H10
    (by change read_cstr (mrb source_segs (fmem inp rsp rrnd)) (reg_get regs1 11) = _
        rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hplen1)
    Hsne0
    (by change bv_unsigned (bv_and (reg_get regs1 12) (bv_not (Z_to_bv 64 open_ignored_flags))) = 0
        rw [H12]; decide +kernel)
    Hsrc_nodot Hsome0
  have Hshape : ∀ eff m' evs', syscall_spec
      (sys_input source_segs (o1rec inp rsp rrnd regs1) (getr regs1 17))
      (model0 inp rsp rbrk rmb) (Ok eff m' evs') →
      evs' = [] ∧ m_halted m' = none ∧ m_vm_lazy m' = [] := by
    intro eff m' evs' Hs
    obtain ⟨Hevs, H⟩ := Hinv eff m' evs' Hs
    rcases H with ⟨e, _, _, rfl⟩ | ⟨fd, _, _, _, rfl⟩ <;> exact ⟨Hevs, rfl, rfl⟩
  obtain ⟨eff, m2, Hspec, rfl, rfl⟩ := sstep_fsys_inv source_segs _ _ _ evs st
    rfl rfl rfl Hne Hshape Hss
  refine ⟨rfl, _, rfl, ?_⟩
  obtain ⟨_, H⟩ := Hinv eff m2 [] Hspec
  rcases H with ⟨e, He, rfl, rfl⟩ | ⟨fd, Hlk, Hfd, rfl, rfl⟩
  · obtain ⟨He1, He2⟩ := openat_errno_range e He
    refine Or.inr ⟨rfl, rfl, (fun o => o = (Z_to_bv 64 3, in_fs inp)), ?_, ?_⟩
    · dsimp only [config.cfg_ms, config.cfg_model, o1rec]
      rw [adv_eff_ret_copyins]
      norm_pc
      apply src_open1_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := e)
      · exact He1
      · exact He2
      · regupd_resolve; rfl
      · regupd_resolve; exact H2
      · regupd_resolve; exact H1
      · rfl
    · intro o Ho; exact Or.inl Ho
  · have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K2, K3, K18, K8, K1, K17, K10, K11, K12, Hms2⟩ :=
      source_to_open2 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; exact H2) (by regupd_resolve; exact H3)
        (by regupd_resolve; exact H8) (by regupd_resolve; exact H1)
        (by regupd_resolve; rfl) Hlt
    refine Or.inl (Or.inr (Or.inl ⟨mkst (regupd regs1 10 fd) 0x11180 (fmem inp rsp rrnd) rrom, regs2, fd, Hlk, Hlt,
      ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩, ?_, ?_⟩))
    · apply msteps_trans _ _ _ _ Hms2
      exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl) (msteps.mst_refl _)
    · unfold o1rec; rw [adv_eff_ret_copyins]; rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 Hdst_nodot Hplen2 Hdne0 in
theorem src_huge_open2_anchor : ∀ regs2 fd evs st,
  fd_lookup (m_fds (model0 inp rsp rbrk rmb)) fd = none → (bv_unsigned fd < 2^31) →
  (sO2pins inp rsp) regs2 fd →
  sstep source_segs (mkCfg ((o2rec inp rsp rrnd) regs2) ((model1 inp rsp rbrk rmb) fd)) evs st →
  fdiv_resp source_segs (sHI inp rsp rrnd rbrk rmb) (sX inp) evs st := by
  intro regs2 fd evs st Hlk Hlt Hpins Hss
  obtain ⟨K17, K10, K11, K12, K2, K3, K18, K1⟩ := Hpins
  let ms := o2rec inp rsp rrnd regs2
  let m1 := model1 inp rsp rbrk rmb fd
  let mk := fun fd2 => with_fds (fd_insert (m_fds m1) fd2 (FdFileW (dst inp) (Z_to_bv 64 0)))
    (with_fs (fs_set (m_fs m1) (dst inp) []) m1)
  have Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk (dst inp) := by
    change read_cstr (mrb source_segs (fmem inp rsp rrnd)) (reg_get regs2 11) = _
    rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hplen2
  have Hfl : bv_unsigned (bv_and (ms_gpr ms 2) (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags := by
    change bv_unsigned (bv_and (reg_get regs2 12) (bv_not (Z_to_bv 64 open_ignored_flags))) = _
    rw [K12]; decide +kernel
  have Hb : (¬ syscall_spec (sys_input source_segs ms (getr regs2 17)) m1 Unmodeled) ∧
      (∀ eff m' es, syscall_spec (sys_input source_segs ms (getr regs2 17)) m1 (Ok eff m' es) →
        es = [] ∧ ((∃ e, 1 ≤ e ∧ e ≤ 4095 ∧
          eff = with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] []) ∧ m' = m1) ∨
        (∃ fd2, fd_lookup (m_fds m1) fd2 = none ∧ fd2 = alloc_fd (m_fds m1) ∧
          eff = with_copyins (open_copyins ms) (mkEffect fd2 [] []) ∧ m' = mk fd2))) := by
    cases Hun : fs_under (in_fs inp) (dst inp) with
    | true =>
      obtain ⟨_, Hu, Hn⟩ := open_wr_isdir source_segs ms (getr regs2 17) m1 (dst inp)
        K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
      refine ⟨Hn, ?_⟩
      intro eff m' es Hs
      obtain ⟨rfl, rfl, rfl⟩ := Hu eff m' es Hs
      exact ⟨rfl, Or.inl ⟨EISDIR, by decide +kernel, by decide +kernel, rfl, rfl⟩⟩
    | false =>
      obtain ⟨Hn, _, _, Hi⟩ := open_wr_branches source_segs ms (getr regs2 17) m1 (dst inp)
        K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
      refine ⟨Hn, ?_⟩
      intro eff m' es Hs
      obtain ⟨Hes, H⟩ := Hi eff m' es Hs
      refine ⟨Hes, ?_⟩
      rcases H with ⟨e, He, Heff, Hm⟩ | H
      · obtain ⟨He1, He2⟩ := openat_errno_range e He
        exact Or.inl ⟨e, He1, He2, Heff, Hm⟩
      · exact Or.inr H
  obtain ⟨Hne, Hinv⟩ := Hb
  have Hshape : ∀ eff m' es, syscall_spec (sys_input source_segs ms (getr regs2 17)) m1 (Ok eff m' es) →
      es = [] ∧ m_halted m' = none ∧ m_vm_lazy m' = [] := by
    intro eff m' es Hs
    obtain ⟨Hes, H⟩ := Hinv eff m' es Hs
    rcases H with ⟨e, _, _, _, rfl⟩ | ⟨fd2, _, _, _, rfl⟩ <;> exact ⟨Hes, rfl, rfl⟩
  obtain ⟨eff, m2, Hspec, rfl, rfl⟩ := sstep_fsys_inv source_segs ms m1 (getr regs2 17)
    evs st rfl rfl rfl Hne Hshape Hss
  refine ⟨rfl, _, rfl, ?_⟩
  obtain ⟨_, H⟩ := Hinv eff m2 [] Hspec
  rcases H with ⟨e, He1, He2, rfl, rfl⟩ | ⟨fd2, Hlk2, Hfd2, rfl, rfl⟩
  · refine Or.inr ⟨rfl, rfl, (fun o => o = (Z_to_bv 64 4, in_fs inp)), ?_, ?_⟩
    · dsimp only [config.cfg_ms, config.cfg_model, ms, o2rec]
      rw [adv_eff_ret_copyins]; norm_pc
      apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := e)
      · exact He1
      · exact He2
      · regupd_resolve; rfl
      · regupd_resolve; exact K2
      · regupd_resolve; exact K1
      · rfl
    · intro o Ho; exact Or.inr Ho
  · have Hlt2 : bv_unsigned fd2 < 2^31 := by rw [Hfd2]; exact alloc_fd_lt_2_31 _
    have Hnefd : fd ≠ fd2 := fd_lookup_some_none_neq _ _ _ _ (fd_lookup_insert_eq _ _ _) Hlk2
    obtain ⟨regsH, G2, G3, G8, G18, G9, HmsH⟩ :=
      src_open2_to_loop inp rsp rrnd (regupd regs2 10 fd2) fd fd2
        (by regupd_resolve; rfl) (by regupd_resolve; exact K2)
        (by regupd_resolve; exact K3) (by regupd_resolve; exact K18)
        (by regupd_resolve; exact K1) Hlt Hlt2
    obtain ⟨regsR, R17, R10, R11, R12, R2, R1, R3, R8, R9, R18, HmsR⟩ :=
      src_head_to_read rsp regsH (fmem inp rsp rrnd) fd fd2 G2 G3 G8 G18 G9
    refine Or.inl (Or.inr (Or.inr ⟨mkCfg (rdrec regsR (fmem inp rsp rrnd)) (mk fd2), ?_, ?_⟩))
    · dsimp only [ms, o2rec]
      rw [adv_eff_ret_copyins]
      apply dsil_msteps source_segs _ _ _ _ (msteps_trans _ _ _ _ HmsH HmsR) rfl
      exact dsil.dsil_refl _
    · refine ⟨fd, fd2, regsR, fmem inp rsp rrnd, mk fd2, Hnefd,
        fd32_lt31 _ Hlt, fd32_lt31 _ Hlt2,
        ⟨R17, R10, R11, R12, R2, R1, R3, R8, R9, R18⟩,
        smem_inv_fmem inp rsp rrnd Hsp_lo Hsp_hi, ?_, rfl⟩
      refine ⟨rfl, rfl, Z_to_bv 64 0, [], ?_, ?_, rfl, by decide +kernel⟩
      · dsimp only [mk, m1, model1]; model_simp
        rw [fd_lookup_insert_neq _ _ _ _ Hnefd, fd_lookup_insert_eq]
      · exact fd_lookup_insert_eq _ _ _

include Hsp_lo Hsp_hi Hsd Hsome0 Hbig in
theorem src_huge_loop_anchor : ∀ c evs st,
  (sAnchor inp rsp rrnd) c →
  sstep source_segs c evs st →
  fdiv_resp source_segs (sHI inp rsp rrnd rbrk rmb) (sX inp) evs st := by
  intro c evs st HA Hss
  obtain ⟨fdin, fdout, regs, mem, model, Hnefd, Hfin32, Hfout32, Hpins, Hsm, HM, rfl⟩ := HA
  obtain ⟨R17, R10, R11, R12, R2, R1, R3, R8, R9, R18⟩ := Hpins
  obtain ⟨Hh, Hlazy, off, data, Hfin, Hfout, Hfsm, Hoff⟩ := HM
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  let chunk := file_read d0 off (Z_to_bv 64 1024)
  obtain ⟨Hc1, Hc2⟩ := huge_chunk d0 Hbig off
  change 1 ≤ (chunk.length : Int) at Hc1
  change (chunk.length : Int) ≤ 1024 at Hc2
  have HuLen : bv_unsigned (len_word chunk) = (chunk.length : Int) := u_len_word _ (by omega)
  have Hg0 : ms_gpr (rdrec regs mem) 0 = fdin := R10
  have Hg1 : ms_gpr (rdrec regs mem) 1 = sbuf := R11
  have Hg2 : ms_gpr (rdrec regs mem) 2 = Z_to_bv 64 1024 := R12
  obtain ⟨w, Hw⟩ := wseg_ok_wdef source_segs sbuf (Z_to_bv 64 1024) (rdrec regs mem) source_buf_wseg
  obtain ⟨Hok, Huniq, Hne⟩ := read_file_uniq source_segs (rdrec regs mem) (getr regs 17)
    model (src inp) off d0 w R17 (by rw [Hg0]; exact Hfin) (by rw [Hg0]; exact Hfin32)
    (by rw [Hfsm, fs_lookup_set_neq _ _ _ _ Hsd]; exact Hsome0)
    (by rw [Hg1, Hg2]; exact Hw)
    (by rw [Hg2]; decide +kernel) (by rw [Hg2]; decide +kernel)
    (by rw [Hg1, Hg2]; apply access_okb_intro; rw [u_sbuf]; decide +kernel)
  try dsimp only at Hok Huniq
  rw [Hg0, Hg1, Hg2] at Hok Huniq
  have Hchunk_ne : chunk ≠ [] := by intro H; simp only [H, List.length_nil] at Hc1; omega
  change syscall_spec _ _ (Ok (mkEffect (len_word chunk) (delivered_writes sbuf chunk) []) _ []) at Hok
  change ∀ eff2 m2 evs2, syscall_spec _ _ (Ok eff2 m2 evs2) →
    eff2 = mkEffect (len_word chunk) (delivered_writes sbuf chunk) [] ∧
    m2 = with_fds (fd_insert (m_fds model) fdin (FdFile (src inp) (off + len_word chunk))) model ∧
    evs2 = [] at Huniq
  rw [delivered_writes_ne sbuf chunk Hchunk_ne] at Hok Huniq
  have Hshape : ∀ eff m' evs',
      syscall_spec (sys_input source_segs (rdrec regs mem) (getr regs 17)) model (Ok eff m' evs') →
      evs' = [] ∧ m_halted m' = none ∧ m_vm_lazy m' = [] := by
    intro eff m' evs' Hs
    obtain ⟨_, rfl, rfl⟩ := Huniq eff m' evs' Hs
    exact ⟨rfl, Hh, Hlazy⟩
  obtain ⟨eff, m2, Hspec, rfl, rfl⟩ := sstep_fsys_inv source_segs (rdrec regs mem) model
    (getr regs 17) evs st Hh Hlazy rfl Hne Hshape Hss
  obtain ⟨rfl, rfl, _⟩ := Huniq eff m2 [] Hspec
  refine ⟨rfl, _, rfl, Or.inl (Or.inr (Or.inr ?_))⟩
  let model' := with_fds (fd_insert (m_fds model) fdin (FdFile (src inp) (off + len_word chunk))) model
  obtain ⟨regsW, W17, W10, W11, W12, W8, W2, W1, W3, W9, W18, HmsW⟩ :=
    src_read_to_write inp rsp rrnd Hsp_lo Hsp_hi
      (regupd regs 10 (len_word chunk)) (write_to_mem mem sbuf chunk) fdin fdout (len_word chunk)
      (by regupd_resolve; rfl) (by omega) (by omega)
      (by regupd_resolve; exact R1) (by regupd_resolve; exact R2)
      (by regupd_resolve; exact R3) (by regupd_resolve; exact R8)
      (by regupd_resolve; exact R9) (by regupd_resolve; exact R18)
      (by apply mem_grows_trans _ _ _ (smem_inv_grows inp rsp rrnd mem Hsm); apply write_to_mem_grows)
  let wrec := rdrec regsW (spill rsp (write_to_mem mem sbuf chunk) (len_word chunk))
  have HgW0 : ms_gpr wrec 0 = fdout := W10
  have HgW1 : ms_gpr wrec 1 = sbuf := W11
  have HgW2 : ms_gpr wrec 2 = len_word chunk := W12
  obtain ⟨HokW, HuniqW, HneW⟩ := write_file_uniq source_segs wrec (getr regsW 17)
    model' (dst inp) off data chunk W17
    (by rw [HgW0]; change fd_lookup (fd_insert _ fdin _) fdout = _
        rw [fd_lookup_insert_neq _ _ _ _ (Ne.symm Hnefd)]; exact Hfout)
    (by rw [HgW0]; exact Hfout32)
    (by rw [HgW1, HgW2, read_bytes_map_read_byte, ms_read_bytes_rdn source_segs wrec _ _ rfl]
        change rdn source_segs (spill rsp (write_to_mem mem sbuf chunk) (len_word chunk)) sbuf (word_to_nat (len_word chunk)) = _
        rw [wtn_len_word chunk (by omega)]
        unfold spill
        repeat rw [rdn_wbytes_below _ _ _ _ _ _
          (by rw [u_sbuf]; u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]
        apply rdn_write_to_mem; rw [u_sbuf]; omega)
    (by rw [HgW2, HuLen]; unfold rw_bytes_max; omega)
    (by change fs_lookup (m_fs model) (dst inp) = _; rw [Hfsm]; exact fs_lookup_set_eq _ _ _)
    (by apply file_gap_in_range; unfold rw_bytes_max; omega)
    (by apply w_is0_pos; rw [HgW2, HuLen]; omega)
  try dsimp only at HokW HuniqW
  rw [HgW0, HgW2] at HokW HuniqW
  let model'' := with_fds (fd_insert (m_fds model') fdout (FdFileW (dst inp) (off + len_word chunk)))
    (with_fs (fs_set (m_fs model') (dst inp) (file_write data off chunk)) model')
  obtain ⟨regsH, G2, G3, G8, G9, G18, HmsH⟩ :=
    src_write_to_head rsp Hsp_lo Hsp_hi (regupd regsW 10 (len_word chunk))
      (spill rsp (write_to_mem mem sbuf chunk) (len_word chunk)) fdin fdout (len_word chunk)
      (by regupd_resolve; rfl) (by omega) (by omega)
      (by regupd_resolve; exact W1) (by regupd_resolve; exact W2)
      (by regupd_resolve; exact W3) (by regupd_resolve; exact W8)
      (by regupd_resolve; exact W9) (by regupd_resolve; exact W18)
      (rdn_spill_cnt rsp Hsp_lo Hsp_hi _ _) (rdn_spill_ptr rsp Hsp_lo Hsp_hi _ _)
  obtain ⟨regsR2, Q17, Q10, Q11, Q12, Q2, Q1, Q3, Q8, Q9, Q18, HmsR2⟩ :=
    src_head_to_read rsp regsH (spill rsp (write_to_mem mem sbuf chunk) (len_word chunk)) fdin fdout
      G2 G3 G8 G18 G9
  refine ⟨mkCfg (rdrec regsR2 (spill rsp (write_to_mem mem sbuf chunk) (len_word chunk))) model'', ?_,
    fdin, fdout, regsR2, spill rsp (write_to_mem mem sbuf chunk) (len_word chunk), model'',
    Hnefd, Hfin32, Hfout32, ⟨Q17, Q10, Q11, Q12, Q2, Q1, Q3, Q8, Q9, Q18⟩, ?_, ?_, rfl⟩
  · dsimp only [rdrec]
    rw [adv_apply_write]
    norm_pc
    apply dsil_msteps _ _ _ model' _ HmsW Hlazy
    apply dsil.dsil_sys (ms := wrec) (model := model') (c'' := _) (x8 := getr regsW 17)
      (eff := with_copyins [(ms_gpr wrec 1, chunk.length)] (mkEffect (len_word chunk) [] []))
      (model' := model'') rfl Hh Hlazy HokW HuniqW HneW Hh Hlazy
    dsimp only [wrec, rdrec]
    rw [adv_eff_ret_copyins]
    norm_pc
    apply dsil_msteps _ _ _ model'' _ HmsH Hlazy
    apply dsil_msteps _ _ _ model'' _ HmsR2 Hlazy
    exact dsil.dsil_refl _
  · apply smem_inv_spill inp rsp rrnd Hsp_lo Hsp_hi
    exact smem_inv_wtm inp rsp rrnd Hsp_lo Hsp_hi mem chunk Hsm Hc2
  · refine ⟨Hh, Hlazy, off + len_word chunk, file_write data off chunk, ?_, ?_, ?_, ?_⟩
    · change fd_lookup (fd_insert _ fdout _) fdin = _
      rw [fd_lookup_insert_neq _ _ _ _ Hnefd]
      exact fd_lookup_insert_eq _ _ _
    · exact fd_lookup_insert_eq _ _ _
    · change fs_set (m_fs model) (dst inp) (file_write data off chunk) = _
      rw [Hfsm]; exact fs_set_set _ _ _ _
    · exact file_write_off_bound data off chunk (by omega) Hoff

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsd Hsome0 Hbig Hsne0 Hdne0 in
theorem src_huge_ok : fdiv_ok source_segs (sHI inp rsp rrnd rbrk rmb) (sX inp) := by
  intro c Hc evs st Hss
  rcases Hc with ⟨ms, regs1, Hpins, Hm, rfl⟩ | ⟨ms, regs2, fd, Hlk, Hlt, Hpins, Hm, rfl⟩ |
    ⟨c'', Hd, HA⟩
  · rcases msteps_region_inv source_segs ms (o1rec inp rsp rrnd regs1) (model0 inp rsp rbrk rmb)
      evs st Hm rfl Hss with rfl | ⟨Hevs, ms1, rfl, Hm1⟩
    · apply src_huge_open1_anchor (d0 := d0) <;> assumption
    · exact ⟨Hevs, _, rfl, Or.inl (Or.inl ⟨ms1, regs1, Hpins, Hm1, rfl⟩)⟩
  · rcases msteps_region_inv source_segs ms (o2rec inp rsp rrnd regs2) (model1 inp rsp rbrk rmb fd)
      evs st Hm rfl Hss with rfl | ⟨Hevs, ms1, rfl, Hm1⟩
    · exact src_huge_open2_anchor (inp := inp) (Hva := Hva) (Hve := Hve)
        (rsp := rsp) (rrnd := rrnd) (Hsp_lo := Hsp_lo) (Hsp_hi := Hsp_hi)
        (rbrk := rbrk) (rmb := rmb) (Hge3 := Hge3) (Hdst_nodot := Hdst_nodot)
        (Hplen2 := Hplen2) (Hdne0 := Hdne0) regs2 fd evs st Hlk Hlt Hpins Hss
    · exact ⟨Hevs, _, rfl, Or.inl (Or.inr (Or.inl ⟨ms1, regs2, fd, Hlk, Hlt, Hpins, Hm1, rfl⟩))⟩
  · apply dsil_region_inv source_segs (sAnchor inp rsp rrnd) (sHI inp rsp rrnd rbrk rmb) (sX inp)
      _ _ _ _ c c'' Hd HA evs st Hss
    · rintro c0 ⟨fdin, fdout, regs, mem, model, _, _, _, _, _, ⟨Hh, _, _⟩, rfl⟩
      exact Hh
    · rintro c0 ⟨fdin, fdout, regs, mem, model, _, _, _, _, _, ⟨_, Hlazy, _⟩, rfl⟩
      exact Hlazy
    · intro c0 HA0 evs0 st0 Hss0
      apply src_huge_loop_anchor (d0 := d0) <;> assumption
    · intro c0 c1 Hd0 HA0
      exact Or.inr (Or.inr ⟨c1, Hd0, HA0⟩)

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsome0 Hsne0 Hdne0 in
theorem src_huge_admits : ∀ o, (sX inp) o →
  ∃ c,
    star source_segs
      (init_config source_segs 0x1112c source_phdrs rsp rbrk rmb rrnd source_alloc_limit inp)
      (fout_trace o) c := by
  intro o Ho
  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  have Hstar1 : star source_segs
      (init_config source_segs 0x1112c source_phdrs rsp rbrk rmb rrnd source_alloc_limit inp)
      [] (mkCfg (o1rec inp rsp rrnd regs1) (model0 inp rsp rbrk rmb)) := by
    apply msteps_star_nil _ _ _ _ rfl rfl
    apply msteps_trans _ _ _ _ Hms
    exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl) (msteps.mst_refl _)
  obtain ⟨Hne, Herr, Hok, Hinv⟩ := open_rd_branches source_segs (o1rec inp rsp rrnd regs1)
    (getr regs1 17) (model0 inp rsp rbrk rmb) (src inp) d0 H17 H10
    (by change read_cstr (mrb source_segs (fmem inp rsp rrnd)) (reg_get regs1 11) = _
        rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hplen1)
    Hsne0 (by change bv_unsigned (bv_and (reg_get regs1 12) _) = 0; rw [H12]; decide +kernel)
    Hsrc_nodot Hsome0
  rcases Ho with rfl | rfl
  · have Hto : to_fout source_segs
        (advance_past_svc (apply_effect (o1rec inp rsp rrnd regs1)
          (with_copyins (open_copyins (o1rec inp rsp rrnd regs1)) (mkEffect (errno_ret ENOMEM) [] []))))
        (model0 inp rsp rbrk rmb) (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
      rw [o1rec, adv_eff_ret_copyins]
      norm_pc
      apply src_open1_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := ENOMEM)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact H2
      · regupd_resolve; exact H1
      · rfl
    obtain ⟨c, Hstar3⟩ := to_fout_star_admits source_segs _ _ _ Hto rfl rfl
      (Z_to_bv 64 3, inp.in_fs) rfl
    refine ⟨c, ?_⟩
    exact star_trans source_segs _ [] _ _ _ Hstar1
      (star_trans source_segs _ [] _ _ _
        (star_syscall_nil source_segs _ _ _ _ _ rfl rfl (Herr ENOMEM ENOMEM_in_openat_errnos) rfl rfl)
        Hstar3)
  · obtain ⟨regs2, K2, K3, K18, K8, K1, K17, K10, K11, K12, Hms2⟩ :=
      source_to_open2 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
        (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        (by regupd_resolve; exact H2) (by regupd_resolve; exact H3)
        (by regupd_resolve; exact H8) (by regupd_resolve; exact H1)
        (by regupd_resolve; rfl) (by decide +kernel)
    have Hstar2 : star source_segs (mkCfg (o1rec inp rsp rrnd regs1) (model0 inp rsp rbrk rmb))
        [] (mkCfg (o2rec inp rsp rrnd regs2) (model1 inp rsp rbrk rmb (Z_to_bv 64 3))) := by
      apply star_trans source_segs _ [] _ [] _
        (star_syscall_nil source_segs _ _ _ _ _ rfl rfl (Hok (Z_to_bv 64 3) rfl rfl) rfl rfl)
      rw [o1rec, adv_eff_ret_copyins]
      apply msteps_star_nil _ _ _ _ rfl rfl
      apply msteps_trans _ _ _ _ Hms2
      exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1117c rfl) (msteps.mst_refl _)
    have Hpath : read_cstr (ms_read_byte (o2rec inp rsp rrnd regs2))
        (ms_gpr (o2rec inp rsp rrnd regs2) 1) = CstrOk (dst inp) := by
      change read_cstr (mrb source_segs (fmem inp rsp rrnd)) (reg_get regs2 11) = _
      rw [K11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hplen2
    have Hfl : bv_unsigned (bv_and (ms_gpr (o2rec inp rsp rrnd regs2) 2)
        (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags := by
      change bv_unsigned (bv_and (reg_get regs2 12) _) = _
      rw [K12]; decide +kernel
    have Herr2 : ∃ e, 1 ≤ e ∧ e ≤ 4095 ∧
        syscall_spec (sys_input source_segs (o2rec inp rsp rrnd regs2) (getr regs2 17))
          (model1 inp rsp rbrk rmb (Z_to_bv 64 3))
          (Ok (with_copyins (open_copyins (o2rec inp rsp rrnd regs2)) (mkEffect (errno_ret e) [] []))
            (model1 inp rsp rbrk rmb (Z_to_bv 64 3)) []) := by
      cases Hun : fs_under inp.in_fs (dst inp) with
      | true =>
        obtain ⟨HokB, _, _⟩ := open_wr_isdir source_segs (o2rec inp rsp rrnd regs2) (getr regs2 17)
          (model1 inp rsp rbrk rmb (Z_to_bv 64 3)) (dst inp) K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
        exact ⟨EISDIR, by decide +kernel, by decide +kernel, HokB⟩
      | false =>
        obtain ⟨_, HerrB, _, _⟩ := open_wr_branches source_segs (o2rec inp rsp rrnd regs2) (getr regs2 17)
          (model1 inp rsp rbrk rmb (Z_to_bv 64 3)) (dst inp) K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
        exact ⟨ENOMEM, by decide +kernel, by decide +kernel, HerrB ENOMEM ENOMEM_in_openat_errnos⟩
    obtain ⟨e, He1, He2, Hspec⟩ := Herr2
    have Hto : to_fout source_segs
        (advance_past_svc (apply_effect (o2rec inp rsp rrnd regs2)
          (with_copyins (open_copyins (o2rec inp rsp rrnd regs2)) (mkEffect (errno_ret e) [] []))))
        (model1 inp rsp rbrk rmb (Z_to_bv 64 3)) (fun o => o = (Z_to_bv 64 4, inp.in_fs)) := by
      rw [o2rec, adv_eff_ret_copyins]
      norm_pc
      apply src_open2_err_tail inp rsp rrnd Hsp_lo Hsp_hi (e := e)
      · exact He1
      · exact He2
      · regupd_resolve; rfl
      · regupd_resolve; exact K2
      · regupd_resolve; exact K1
      · rfl
    obtain ⟨c, Hstar4⟩ := to_fout_star_admits source_segs _ _ _ Hto rfl rfl
      (Z_to_bv 64 4, inp.in_fs) rfl
    refine ⟨c, ?_⟩
    exact star_trans source_segs _ [] _ _ _ Hstar1
      (star_trans source_segs _ [] _ _ _ Hstar2
        (star_trans source_segs _ [] _ _ _
          (star_syscall_nil source_segs _ _ _ _ _ rfl rfl Hspec rfl rfl) Hstar4))

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsd Hsome0 Hbig Hsne0 Hdne0 in
theorem source_huge_obs : ∀ tr,
  obs_trace source_segs
    (init_config source_segs 0x1112c source_phdrs rsp rbrk rmb rrnd source_alloc_limit inp) tr
  ↔ ∃ o, (o = (Z_to_bv 64 3, (in_fs inp)) ∨ o = (Z_to_bv 64 4, (in_fs inp)))
                ∧ is_prefix tr (fout_trace o) := by
  intro tr
  have Hok : fdiv_ok source_segs (sHI inp rsp rrnd rbrk rmb) (sX inp) := by
    apply src_huge_ok (d0 := d0) <;> assumption
  have Hstart := src_huge_start inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    rcases fdiv_star_only source_segs _ _ Hok _ _ _ Hstar Hstart with Hnil | ⟨o, Ho, Hp'⟩
    · subst tr'
      cases tr with
      | nil => exact ⟨(Z_to_bv 64 3, inp.in_fs), Or.inl rfl, is_prefix_nil _⟩
      | cons x tr => exact False.elim Hp
    · exact ⟨o, Ho, is_prefix_trans _ _ _ Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    have Hex : ∃ c, star source_segs
        (init_config source_segs 0x1112c source_phdrs rsp rbrk rmb rrnd source_alloc_limit inp)
        (fout_trace o) c := by
      apply src_huge_admits (d0 := d0) <;> assumption
    obtain ⟨c, Hstar⟩ := Hex
    exact ⟨fout_trace o, c, Hstar, Hp⟩

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsd Hsome0 Hbig Hsne0 Hdne0 in
theorem source_huge_no_error :
  ¬ reaches_error source_segs
      (init_config source_segs 0x1112c source_phdrs rsp rbrk rmb rrnd source_alloc_limit inp) := by
  apply fdiv_no_error source_segs (sHI inp rsp rrnd rbrk rmb) (sX inp)
  · apply src_huge_ok (d0 := d0) <;> assumption
  · apply src_huge_start <;> assumption

end Huge

end LinuxProcessSemantics.Examples.cp_ns.cp_ns_source
