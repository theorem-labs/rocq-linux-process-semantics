import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.FileSim.Base
import LinuxProcessSemantics.Common.FileSim.Decode
import LinuxProcessSemantics.Common.FileSim.Algebra
import LinuxProcessSemantics.Common.FileSim.Tree
import LinuxProcessSemantics.Common.FileSim.Glue
import LinuxProcessSemantics.Common.FileSim.Open
import LinuxProcessSemantics.Common.FileSim.ReadWrite
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_defs

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # headcp-ns: source binary

PROOF-SIDE FILE (not part of the trusted specification).
Twins `theories/Examples/headcp_ns/headcp_ns_source.v`.
Section parameters are explicit; shared facts are supplied by the common libraries.
-/

namespace LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.State.FdEntry
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.FileSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_code
open LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_defs

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

def rrom : word → Option byte := seg_rom source_segs
def sbuf : word := 0x13008

theorem u_sbuf : bv_unsigned sbuf = 0x13008 := rfl

theorem v_sll_3 (x : word) : v_sll x (Z_to_bv 64 3) = v_slli x 3 := by
  rfl

section SourceProof
variable (inp : ProcInput)
variable (Hva : valid_argv inp.in_argv) (Hve : valid_envp inp.in_envp)
variable (rsp : word) (rrnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
variable (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)
variable (rbrk rmb : word)

include Hsp_lo in
theorem rsp_lo_num : 0x7fff80000000 ≤ bv_unsigned rsp := Hsp_lo
include Hsp_hi in
theorem rsp_hi_num : bv_unsigned rsp ≤ 0x800000000000 := Hsp_hi

def argcN : word := Common.ArgvEnv.argcN inp.in_argv

def wmem : word → Option byte :=
  wrap_mem source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd

include Hva in
theorem u_argcN : bv_unsigned (argcN inp) = (inp.in_argv.length : Int) :=
  Common.ArgvEnv.u_argcN inp.in_argv Hva

include Hva Hve Hsp_hi in
theorem source_bsb_nw :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap rrnd).length : Int) < 2 ^ 64 :=
  Common.ArgvEnv.bsb_nw source_phdrs rsp inp.in_argv inp.in_envp inp.in_uid
    inp.in_hwcap rrnd Hva Hve Hsp_hi

def envp_ptr : word := Common.ArgvEnv.envp_ptr rsp inp.in_argv

include Hva Hsp_lo Hsp_hi in
theorem envp_ptr_eq :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN inp) 3)) 8 =
      envp_ptr inp rsp :=
  Common.ArgvEnv.envp_ptr_eq rsp inp.in_argv Hva Hsp_lo Hsp_hi

def emem : word → Option byte :=
  wbytes (wmem inp rsp rrnd) (0x13000 : word) (word_to_le_bytes 8 (envp_ptr inp rsp))

include Hva Hsp_lo Hsp_hi in
theorem envp_ptr_eq_sym :
    Z_to_bv 64 (bv_unsigned (alu64 .ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (argcN inp) (Z_to_bv 64 3))) + 8) = envp_ptr inp rsp := by
  rw [alu_add, v_sll_3]
  exact envp_ptr_eq inp Hva rsp Hsp_lo Hsp_hi

def fmem : word → Option byte :=
  wbytes (wbytes (wbytes (emem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x1112c : word))

include Hsp_lo in
theorem rdn_emem_above (a : word) (n : Nat)
    (Ha : bv_unsigned rsp ≤ bv_unsigned a) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (emem inp rsp rrnd) a n = rdn source_segs (wmem inp rsp rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  unfold emem
  rw [rdn_wbytes_disjoint]
  all_goals try rw [length_N_to_le_bytes]
  all_goals imm_norm; u_norm; omega

include Hsp_lo Hsp_hi in
theorem rdn_fmem_above (a : word) (n : Nat)
    (Ha : bv_unsigned rsp ≤ bv_unsigned a) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (fmem inp rsp rrnd) a n = rdn source_segs (wmem inp rsp rrnd) a n := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  rw [rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wbytes_disjoint]
  · exact rdn_emem_above inp rsp rrnd Hsp_lo a n Ha Hn
  all_goals try rw [length_N_to_le_bytes]
  all_goals u_norm; omega

theorem rdn_wmem_stack (a : word) (n : Nat)
    (Ha : bv_unsigned rsp ≤ bv_unsigned a) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn source_segs (wmem inp rsp rrnd) a n =
      rdn source_segs (stack_to_mem rsp (entry_stack_image source_phdrs rsp
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd)) a n :=
  rdn_wrap_stack_above source_segs source_phdrs rsp inp.in_argv inp.in_envp a n
    inp.in_uid inp.in_hwcap rrnd Ha Hn

include Hva Hve Hsp_hi in
theorem read_argc_w :
    rdn source_segs (wmem inp rsp rrnd) rsp 8 = some (word_le8 (argcN inp)) :=
  Common.ArgvEnv.read_argc_w source_segs source_phdrs rsp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap rrnd Hva Hve Hsp_hi

include Hsp_lo Hsp_hi in
theorem fmem_ra_slot :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x1112c : word)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  apply rdn_wbytes_hit8
  u_norm; omega

include Hsp_lo Hsp_hi in
theorem fmem_s0_slot :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 16)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  rw [rdn_wbytes_below, rdn_wbytes_disjoint]
  · apply rdn_wbytes_hit8; u_norm; omega
  all_goals try rw [length_N_to_le_bytes]
  all_goals u_norm; omega

include Hsp_lo Hsp_hi in
theorem fmem_s1_slot :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 24)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  rw [rdn_wbytes_below]
  · apply rdn_wbytes_hit8; u_norm; omega
  all_goals try rw [length_N_to_le_bytes]
  all_goals u_norm; omega

def src : path := inp.in_argv.getD 1 []
def dst : path := inp.in_argv.getD 2 []
def psrc : word := cat_argv_ptr rsp inp.in_argv inp.in_envp 1
def pdst : word := cat_argv_ptr rsp inp.in_argv inp.in_envp 2


local elab "headcp_eq_goal" : tactic => do
  let t ← Lean.Elab.Tactic.getMainTarget
  unless t.isAppOfArity ``Eq 3 do
    throwError "expected an equality goal"

local macro "headcp_pin " h:ident : tactic => `(tactic| (
  headcp_eq_goal
  first | exact $h | (rw [getr_nz _ _ (by reg_neq_tac)]; exact $h)))

local macro "headcp_out " h:ident : tactic => `(tactic| (
  headcp_eq_goal
  sym_regs $h
  all_goals try rw [getr_nz _ _ (by reg_neq_tac)]
  all_goals first
    | assumption
    | rfl
    | exact v_addi_0 _
    | (congr 1; omega)
    | sym_close
    | (apply bv_eq_of_unsigned; u_norm; omega)
  all_goals done))

include Hsp_lo Hsp_hi in
theorem source_exit_tail (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (code : word) (fsv : Fs)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H10 : reg_get regs 10 = code) (Hc : bv_unsigned code < 256)
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x1112c : word)))
    (Hs0 : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Hs1 : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Hfs : m_fs model = fsv) :
    to_fout source_segs (mkst regs 0x110e4 mem rrom) model (fun o => o = (code, fsv)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69860) mem rrom) 8
    [] [ELit 0x1112c, ELit 0, ELit 0] [(2, EVar 32)]
    [Z_to_bv 64 (bv_unsigned rsp - 48)] [] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | exact ⟨_, Hs1, bytes_le_to_Z_8 _⟩
    | exact ⟨_, Hs0, bytes_le_to_Z_8 _⟩
    | exact ⟨_, Hra, bytes_le_to_Z_8 _⟩
    | (u_norm; omega))
  all_goals try (exact (getr_nz regs 2 (by decide)).trans H2)
  apply tfo_msteps source_segs _ _ model _ Hms
  sym_pc_lit
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ SF_11130 rfl
  apply tfo_exit_rec
  · headcp_out HR
  · headcp_out HR
  · exact Hc
  · exact Hfs

def spill (mem : word → Option byte) (cnt : word) : word → Option byte :=
  wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 cnt)

include Hsp_lo Hsp_hi in
theorem rdn_spill_cnt (mem : word → Option byte) (cnt : word) :
    rdn source_segs (spill rsp mem cnt) (Z_to_bv 64 (bv_unsigned rsp - 40)) 8 =
      some (word_to_le_bytes 8 cnt) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  apply rdn_wbytes_hit8
  u_norm; omega

theorem src_open2_to_read (regs : bvmap 5 word) (mem : word → Option byte)
    (fdin fdout spv : word)
    (H1 : reg_get regs 1 = (0x11068 : word)) (H2 : reg_get regs 2 = spv)
    (H3 : reg_get regs 3 = (0x13800 : word)) (H9 : reg_get regs 9 = fdin)
    (H10 : reg_get regs 10 = fdout) (Hlt : bv_unsigned fdout < 2 ^ 31) :
    ∃ regs', bv_unsigned (getr regs' 17) = 63 ∧
      reg_get regs' 10 = fdin ∧ reg_get regs' 11 = sbuf ∧
      reg_get regs' 12 = Z_to_bv 64 128 ∧ reg_get regs' 1 = (0x11094 : word) ∧
      reg_get regs' 2 = spv ∧ reg_get regs' 3 = (0x13800 : word) ∧
      reg_get regs' 8 = fdout ∧ reg_get regs' 9 = fdin ∧
      msteps source_segs (mkst regs (0x11154 : word) mem rrom)
        { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x11150 : word),
          ms_svc_pending := some (getr regs' 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rrom } := by
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69972) mem rrom)
    20 [false] [] [(1, ELit 0x11068), (3, ELit 0x13800), (9, EVar 32), (10, EVar 33)]
    [fdin, fdout] [] R HR Hms
  · apply c_lts_pos_0; omega
  all_goals try (solve | exact (getr_nz regs 1 (by decide)).trans H1 | exact (getr_nz regs 3 (by decide)).trans H3 | exact (getr_nz regs 9 (by decide)).trans H9 | exact (getr_nz regs 10 (by decide)).trans H10)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ SF_11150 rfl
       exact msteps.mst_refl _)

include Hsp_lo Hsp_hi in
theorem src_read_to_write (regs : bvmap 5 word) (mem : word → Option byte)
    (fdin fdout cnt : word)
    (H1 : reg_get regs 1 = (0x11094 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H3 : reg_get regs 3 = (0x13800 : word)) (H8 : reg_get regs 8 = fdout)
    (H9 : reg_get regs 9 = fdin) (H10 : reg_get regs 10 = cnt)
    (Hc : bv_unsigned cnt ≤ 128) (Hg : mem_grows (wmem inp rsp rrnd) mem) :
    ∃ regs', bv_unsigned (getr regs' 17) = 64 ∧
      reg_get regs' 10 = fdout ∧ reg_get regs' 11 = sbuf ∧ reg_get regs' 12 = cnt ∧
      reg_get regs' 1 = (0x110c0 : word) ∧
      reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs' 8 = fdout ∧ reg_get regs' 9 = fdin ∧
      msteps source_segs (mkst regs (0x11154 : word) mem rrom)
        { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x11150 : word),
          ms_svc_pending := some (getr regs' 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := spill rsp mem cnt, ms_rom := rrom } := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69972) mem rrom)
    20 [false] [] [(1, ELit 0x11094), (2, EVar 32), (3, ELit 0x13800),
      (8, EVar 33), (10, EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 48), fdout, cnt] [] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | (apply c_lts_pos_0; omega)
    | (apply store_ok_mono _ _ _ _ _ Hg
       apply store_ok_wrap_window
       all_goals try rw [stack_max_size_val]
       all_goals u_norm; omega)
    | (u_norm; omega))
  all_goals try (solve | exact (getr_nz regs 1 (by decide)).trans H1 | exact (getr_nz regs 2 (by decide)).trans H2 | exact (getr_nz regs 3 (by decide)).trans H3 | exact (getr_nz regs 8 (by decide)).trans H8 | exact (getr_nz regs 10 (by decide)).trans H10)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       unfold spill
       sym_mem_norm
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ SF_11150 rfl
       exact msteps.mst_refl _)

include Hsp_lo Hsp_hi in
theorem src_write_to_ret (regs : bvmap 5 word) (mem : word → Option byte)
    (fdin fdout cnt : word)
    (H1 : reg_get regs 1 = (0x110c0 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H8 : reg_get regs 8 = fdout) (H9 : reg_get regs 9 = fdin)
    (H10 : reg_get regs 10 = cnt)
    (Hrd : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8 =
      some (word_to_le_bytes 8 cnt)) :
    ∃ regs', reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs' 8 = fdout ∧ reg_get regs' 9 = fdin ∧
      msteps source_segs (mkst regs (0x11154 : word) mem rrom)
        (mkst regs' (0x110d0 : word) mem rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69972) mem rrom)
    5 [false] [EVar 35]
    [(1, ELit 0x110c0), (2, EVar 32), (9, EVar 33), (10, EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 48), fdin, cnt] [cnt] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | (simp only [bv_eqb_refl, Bool.not_true])
    | (change (!c_eq (v_addi cnt 0) cnt) = false; rw [v_addi_0, c_eq_refl]; rfl)
    | (change (!c_eq cnt (v_addi cnt 0)) = false; rw [v_addi_0, c_eq_refl]; rfl)
    | (refine ⟨word_to_le_bytes 8 cnt, ?_, bytes_le_to_Z_8 cnt⟩
       sym_addr_norm
       first | exact Hrd | (simpa only [Int.sub_add_cancel, Int.sub_add_eq_add_sub, Int.add_assoc] using Hrd))
    | (u_norm; omega))
  all_goals try (solve | exact (getr_nz regs 1 (by decide)).trans H1 | exact (getr_nz regs 2 (by decide)).trans H2 | exact (getr_nz regs 9 (by decide)).trans H9 | exact (getr_nz regs 10 (by decide)).trans H10)
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  all_goals first | headcp_out HR | exact Hms

include Hsp_lo Hsp_hi in
theorem src_close_call (regs : bvmap 5 word) (mem : word → Option byte)
    (fdv raM s0v s1v : word) (H1 : reg_get regs 1 = raM)
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H8 : reg_get regs 8 = s0v) (H9 : reg_get regs 9 = s1v)
    (H10 : reg_get regs 10 = fdv) (Hg : mem_grows (wmem inp rsp rrnd) mem) :
    ∃ regs', bv_unsigned (getr regs' 17) = 57 ∧ reg_get regs' 10 = fdv ∧
      reg_get regs' 1 = (0x11188 : word) ∧
      reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ∧
      reg_get regs' 8 = s0v ∧ reg_get regs' 9 = s1v ∧
      msteps source_segs (mkst regs (0x1115c : word) mem rrom)
        { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x11204 : word),
          ms_svc_pending := some (getr regs' 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0,
          ms_mem := wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 raM),
          ms_rom := rrom } := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69980) mem rrom)
    21 [] [] [(1, EVar 32), (2, EVar 33), (10, EVar 34)]
    [raM, Z_to_bv 64 (bv_unsigned rsp - 48), fdv] [] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | (apply store_ok_mono _ _ _ _ _ Hg
       apply store_ok_wrap_window
       all_goals try rw [stack_max_size_val]
       all_goals u_norm; omega)
    | (u_norm; omega))
  all_goals try (solve | exact (getr_nz regs 1 (by decide)).trans H1 | exact (getr_nz regs 2 (by decide)).trans H2 | exact (getr_nz regs 10 (by decide)).trans H10)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       sym_mem_norm
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ SF_11204 rfl
       exact msteps.mst_refl _)

include Hsp_lo Hsp_hi in
theorem src_close_tail (regs : bvmap 5 word) (mem : word → Option byte)
    (raM s0v s1v : word) (H1 : reg_get regs 1 = (0x11188 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    (H8 : reg_get regs 8 = s0v) (H9 : reg_get regs 9 = s1v)
    (H10 : reg_get regs 10 = Z_to_bv 64 0)
    (Hrd : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8 =
      some (word_to_le_bytes 8 raM)) :
    ∃ regs', reg_get regs' 1 = raM ∧
      reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs' 8 = s0v ∧ reg_get regs' 9 = s1v ∧ reg_get regs' 10 = Z_to_bv 64 0 ∧
      msteps source_segs (mkst regs (0x11208 : word) mem rrom)
        (mkst regs' (0x111a4 : word) mem rrom) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 70152) mem rrom)
    12 [false, false] [EVar 33]
    [(1, ELit 0x11188), (2, EVar 32), (10, ELit 0)]
    [Z_to_bv 64 (bv_unsigned rsp - 64)] [raM] R HR Hms
  all_goals repeat' apply And.intro
  · omega
  · omega
  · omega
  · exact ⟨_, Hrd, bytes_le_to_Z_8 raM⟩
  · decide +kernel
  · decide +kernel
  · exact (getr_nz regs 1 (by decide)).trans H1
  · exact (getr_nz regs 2 (by decide)).trans H2
  · exact (getr_nz regs 10 (by decide)).trans H10
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, Hms⟩
  · rw [← getr_nz R 1 (by decide)]
    exact HR 1
  · sym_regs HR
    congr 1
    change bv_unsigned rsp - 64 + 16 = bv_unsigned rsp - 48
    omega
  · sym_regs HR
    rw [getr_nz regs 8 (by decide)]
    exact H8
  · sym_regs HR
    rw [getr_nz regs 9 (by decide)]
    exact H9
  · rw [← getr_nz R 10 (by decide)]
    exact HR 10

section Ge3
variable (Hge3 : 3 ≤ inp.in_argv.length)

include Hva Hve Hsp_hi Hge3 in
theorem psrc_bounds :
    bv_unsigned rsp ≤ bv_unsigned (psrc inp rsp) ∧
      bv_unsigned (psrc inp rsp) + ((src inp).length : Int) + 1 < 2 ^ 64 :=
  Common.ArgvEnv.argv_ptr_bounds_at rsp inp.in_argv inp.in_envp Hva Hve Hsp_hi 1 (by omega)

include Hva Hve Hsp_hi Hge3 in
theorem pdst_bounds :
    bv_unsigned rsp ≤ bv_unsigned (pdst inp rsp) ∧
      bv_unsigned (pdst inp rsp) + ((dst inp).length : Int) + 1 < 2 ^ 64 :=
  Common.ArgvEnv.argv_ptr_bounds_at rsp inp.in_argv inp.in_envp Hva Hve Hsp_hi 2 (by omega)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_psrc_e :
    rdn source_segs (emem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp + 16)) 8 =
      some (word_le8 (psrc inp rsp)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_emem_above inp rsp rrnd Hsp_lo]
  · have H := Common.ArgvEnv.read_argv_ptr_w source_segs source_phdrs rsp
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd Hva Hve Hsp_lo Hsp_hi 1 (by omega)
    rw [word_add_nat] at H
    exact H
  all_goals u_norm; omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_pdst_f :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp + 24)) 8 =
      some (word_le8 (pdst inp rsp)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi]
  · have H := Common.ArgvEnv.read_argv_ptr_w source_segs source_phdrs rsp
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap rrnd Hva Hve Hsp_lo Hsp_hi 2 (by omega)
    rw [word_add_nat] at H
    exact H
  all_goals u_norm; omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_src (Hlen : (src inp).length ≤ 4095) :
    read_cstr (mrb source_segs (fmem inp rsp rrnd)) (psrc inp rsp) = cstr_result.CstrOk (src inp) := by
  obtain ⟨Hplo, Hphi⟩ := psrc_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz inp.in_argv 1 Hva (by omega)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_cstr_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 1
        inp.in_uid inp.in_hwcap rrnd (by omega) (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_dst (Hlen : (dst inp).length ≤ 4095) :
    read_cstr (mrb source_segs (fmem inp rsp rrnd)) (pdst inp rsp) = cstr_result.CstrOk (dst inp) := by
  obtain ⟨Hplo, Hphi⟩ := pdst_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz inp.in_argv 2 Hva (by omega)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_cstr_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 2
        inp.in_uid inp.in_hwcap rrnd (by omega) (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_src_long (Hlen : 4096 ≤ (src inp).length) :
    read_cstr (mrb source_segs (fmem inp rsp rrnd)) (psrc inp rsp) = cstr_result.CstrTooLong := by
  obtain ⟨Hplo, Hphi⟩ := psrc_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn source_segs _ _ ((src inp).take 4096)
  · rw [List.length_take, Nat.min_eq_left Hlen]
  · intro H
    exact valid_argv_str_nz inp.in_argv 1 Hva (by omega) (List.mem_of_mem_take H)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_prefix_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 1 4096
        inp.in_uid inp.in_hwcap rrnd (by omega) Hlen (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_cstr_dst_long (Hlen : 4096 ≤ (dst inp).length) :
    read_cstr (mrb source_segs (fmem inp rsp rrnd)) (pdst inp rsp) = cstr_result.CstrTooLong := by
  obtain ⟨Hplo, Hphi⟩ := pdst_bounds inp Hva Hve rsp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn source_segs _ _ ((dst inp).take 4096)
  · rw [List.length_take, Nat.min_eq_left Hlen]
  · intro H
    exact valid_argv_str_nz inp.in_argv 2 Hva (by omega) (List.mem_of_mem_take H)
  · rw [rdn_fmem_above inp rsp rrnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_prefix_k source_phdrs source_segs rsp inp.in_argv inp.in_envp 2 4096
        inp.in_uid inp.in_hwcap rrnd (by omega) Hlen (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_to_open1 :
    ∃ regs1, reg_get regs1 1 = (0x1103c : word) ∧
      reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs1 3 = (0x13800 : word) ∧
      reg_get regs1 8 = Z_to_bv 64 (bv_unsigned rsp + 8) ∧
      bv_unsigned (getr regs1 17) = 56 ∧ reg_get regs1 10 = AT_FDCWD ∧
      reg_get regs1 11 = psrc inp rsp ∧ reg_get regs1 12 = Z_to_bv 64 0 ∧
      msteps source_segs
        (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        { ms_regs := regs1, ms_fregs := bvmap_empty, ms_pc_val := 0x11150,
          ms_svc_pending := some (getr regs1 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := fmem inp rsp rrnd, ms_rom := rrom } := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  have Hu := u_argcN inp Hva
  have Hbr : c_lts (Z_to_bv 64 2) (argcN inp) = true := by
    rw [c_lts_small _ _ (by decide) (by rw [Hu]; omega)]
    change BitVec.ult _ _ = true
    rw [BitVec.ult_iff_lt, BitVec.lt_def]
    change 2 < (argcN inp).toNat
    unfold bv_unsigned at Hu
    omega
  obtain ⟨Hplo, Hphi⟩ := psrc_bounds inp Hva Hve rsp Hsp_hi Hge3
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
      (Z_to_bv 64 69888) (wmem inp rsp rrnd) rrom)
    40 [false] [EVar 33, EVar 34]
    [(2, EVar 32), (8, ELit 0), (9, ELit 0)]
    [rsp] [argcN inp, psrc inp rsp] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | (apply source_store_ok <;> (imm_norm; u_norm; omega))
    | (apply store_ok_wrap_window
       all_goals try rw [stack_max_size_val]
       all_goals u_norm; omega)
    | (refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
       change rdn source_segs (wmem inp rsp rrnd) (v_addi rsp 0) 8 = _
       rw [v_addi_0]
       exact read_argc_w inp Hva Hve rsp rrnd Hsp_hi)
    | (refine ⟨word_le8 (psrc inp rsp), ?_, bytes_le_n_to_le_8 _⟩
       have H := read_psrc_e inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
       rw [rdn_emem_above inp rsp rrnd Hsp_lo] at H
       · exact H
       all_goals u_norm; omega)
    | (change (!c_lts (Z_to_bv 64 2) (argcN inp)) = false; rw [Hbr]; rfl)
    | (u_norm; omega))
  all_goals try (solve | headcp_eq_goal; getr_resolve; regupd_resolve; rfl)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (rw [init_mkst]
       apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       unfold fmem emem
       sym_mem_norm
       have Henv := envp_ptr_eq_sym inp Hva rsp Hsp_lo Hsp_hi
       rw [alu_add] at Henv
       rw [Henv]
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ SF_11150 rfl
       exact msteps.mst_refl _)

include Hsp_lo Hsp_hi in
theorem source_exit3 (regs : bvmap 5 word) (model : Model) (X : word) (fsv : Fs)
    (H1 : reg_get regs 1 = (0x1103c : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H10 : reg_get regs 10 = X) (Hneg : c_lts X (Z_to_bv 64 0) = true)
    (Hfs : m_fs model = fsv) :
    to_fout source_segs (mkst regs 0x11154 (fmem inp rsp rrnd) rrom) model
      (fun o => o = (Z_to_bv 64 3, fsv)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69972) (fmem inp rsp rrnd) rrom)
    4 [true] [] [(1, ELit 0x1103c), (10, EVar 32)] [X] [] R HR Hms
  all_goals try (first | exact Hneg | exact (getr_nz regs 1 (by decide)).trans H1 | exact (getr_nz regs 10 (by decide)).trans H10)
  apply tfo_msteps source_segs _ _ model _ Hms
  sym_pc_lit
  apply source_exit_tail rsp Hsp_lo Hsp_hi
  · headcp_out HR
  · headcp_out HR
  · decide +kernel
  · exact fmem_ra_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact fmem_s0_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact fmem_s1_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact Hfs

include Hsp_lo Hsp_hi in
theorem source_exit4 (regs : bvmap 5 word) (model : Model) (e : Int) (fsv : Fs)
    (H1 : reg_get regs 1 = (0x11068 : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H10 : reg_get regs 10 = errno_ret e) (He1 : 1 ≤ e) (He2 : e ≤ 4095)
    (Hfs : m_fs model = fsv) :
    to_fout source_segs (mkst regs 0x11154 (fmem inp rsp rrnd) rrom) model
      (fun o => o = (Z_to_bv 64 4, fsv)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69972) (fmem inp rsp rrnd) rrom)
    4 [true] [] [(1, ELit 0x11068), (10, EVar 32)] [errno_ret e] [] R HR Hms
  all_goals try (first | exact c_lts_errno e He1 He2 | exact (getr_nz regs 1 (by decide)).trans H1 | exact (getr_nz regs 10 (by decide)).trans H10)
  apply tfo_msteps source_segs _ _ model _ Hms
  sym_pc_lit
  apply source_exit_tail rsp Hsp_lo Hsp_hi
  · headcp_out HR
  · headcp_out HR
  · decide +kernel
  · exact fmem_ra_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact fmem_s0_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact fmem_s1_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact Hfs

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_open1_to_open2 (regs : bvmap 5 word) (fd : word)
    (H1 : reg_get regs 1 = (0x1103c : word))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (H3 : reg_get regs 3 = (0x13800 : word))
    (H8 : reg_get regs 8 = Z_to_bv 64 (bv_unsigned rsp + 8))
    (H10 : reg_get regs 10 = fd) (Hlt : bv_unsigned fd < 2 ^ 31) :
    ∃ regs2, reg_get regs2 1 = (0x11068 : word) ∧
      reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ∧
      reg_get regs2 3 = (0x13800 : word) ∧ reg_get regs2 9 = fd ∧
      bv_unsigned (getr regs2 17) = 56 ∧ reg_get regs2 10 = AT_FDCWD ∧
      reg_get regs2 11 = pdst inp rsp ∧ reg_get regs2 12 = Z_to_bv 64 577 ∧
      msteps source_segs (mkst regs 0x11154 (fmem inp rsp rrnd) rrom)
        { ms_regs := regs2, ms_fregs := bvmap_empty, ms_pc_val := 0x11150,
          ms_svc_pending := some (getr regs2 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := fmem inp rsp rrnd, ms_rom := rrom } := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨Hplo, Hphi⟩ := pdst_bounds inp Hva Hve rsp Hsp_hi Hge3
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 69972) (fmem inp rsp rrnd) rrom)
    24 [false] [EVar 34] [(1, ELit 0x1103c), (8, EVar 32), (10, EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp + 8), fd] [pdst inp rsp] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | exact ⟨_, read_pdst_f inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3, bytes_le_n_to_le_8 _⟩
    | (apply c_lts_pos_0; omega)
    | (u_norm; omega))
  all_goals try (solve | exact (getr_nz regs 1 (by decide)).trans H1 | exact (getr_nz regs 8 (by decide)).trans H8 | exact (getr_nz regs 10 (by decide)).trans H10)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ SF_11150 rfl
       exact msteps.mst_refl _)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_absent (Hsrc_nodot : openat_plain_name (src inp) = true)
    (Hlen : (src inp).length ≤ 4095) (Hnone : fs_lookup inp.in_fs (src inp) = none) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (hc_outcomes inp.in_fs (src inp) (dst inp)) := by
  apply tfo_equiv source_segs _ _ (fun o => o = (Z_to_bv 64 3, inp.in_fs))
  · obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
      source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
    apply tfo_msteps source_segs _ _ _ _ Hms
    apply tfo_open_enoent_rec source_segs _ _ _
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) (src inp) _ H17 H10 H12
      (by rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen)
      Hsrc_nodot Hnone rfl rfl
    apply source_exit3 inp rsp rrnd Hsp_lo Hsp_hi
    · regupd_resolve; exact H1
    · regupd_resolve; exact H2
    · regupd_resolve; rfl
    · exact c_lts_errno ENOENT (by decide) (by decide)
    · rfl
  · intro o; simp only [hc_outcomes, Hnone]

theorem src_openat_enoent_empty (ms : machine_state) (model : Model)
    (x8 : word) (p : path) (U : word × Fs → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 56)
    (Hfl : modeled_open_flags (ms_gpr ms 2) = true)
    (_Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = cstr_result.CstrOk p)
    (Hpe : path_eqb p [] = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout source_segs (advance_past_svc (apply_effect ms
      (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] [])))) model U) :
    to_fout source_segs ms model U := by
  have Hchk : ∀ eff, check_syscall (sys_input source_segs ms x8) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [] := by
    intro eff
    rw [check_syscall_56 source_segs ms x8 eff model Hno]
    simp only [check_openat, Hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      check_openat_body, in_mem_si, Hpath, Hpe]
    exact check_copyins_after_ret_only _ _ _ _ _
  have Hagree : lookups_agree_at (bv_unsigned (sys_input source_segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_openat
  refine tfo_sys_det source_segs ms model x8 _ model U Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
  · apply check_syscall_sound_ok
    rw [Hchk, check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m evs Hs
    have H := check_syscall_complete_ok _ _ _ _ _ Hagree Hs
    rw [Hchk, check_ret_only_copyins_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ H

theorem src_open_empty_rec (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (p : path) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (Hfl : modeled_open_flags (reg_get regs 12) = true)
    (H10 : reg_get regs 10 = AT_FDCWD)
    (Hpath : read_cstr (mrb source_segs mem) (reg_get regs 11) = cstr_result.CstrOk p)
    (Hpe : path_eqb p [] = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout source_segs (mkst (regupd regs 10 (errno_ret ENOENT))
      (v_addi pc 4) mem (seg_rom source_segs)) model U) :
    to_fout source_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs } model U := by
  apply src_openat_enoent_empty
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none,
      ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs } model (getr regs 17) p U rfl H17 Hfl H10 Hpath Hpe Hh Hlazy
  simpa only [adv_eff_ret_copyins] using Hcont

theorem src_read_dir_eisdir (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (fdv : word) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 63) (H10 : reg_get regs 10 = fdv)
    (Hfd : fd_lookup (m_fds model) fdv = some FdDir) (Hfd32 : fd32 fdv = fdv)
    (Hdr : (!access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12))) = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout source_segs (mkst (regupd regs 10 (errno_ret EISDIR))
      (v_addi pc 4) mem (seg_rom source_segs)) model U) :
    to_fout source_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs } model U := by
  let ms : machine_state :=
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs }
  have Hchk : ∀ eff, check_syscall (sys_input source_segs ms (getr regs 17)) eff model =
      check_ret_only eff (errno_ret EISDIR) model [] := by
    intro eff
    rw [check_syscall_63 source_segs ms (getr regs 17) eff model H17]
    change check_read _ (fd32 (reg_get regs 10)) (reg_get regs 11) (reg_get regs 12) eff model = _
    simp only [check_read, H10, Hfd32, Hfd, Hdr, Bool.false_eq_true, ↓reduceIte]
  have Hagree : lookups_agree_at (bv_unsigned (sys_input source_segs ms (getr regs 17)).in_sysno) := by
    rw [in_sysno_si, H17]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_read
  refine tfo_sys_det source_segs ms model (getr regs 17) (mkEffect (errno_ret EISDIR) [] []) model U rfl ?_ ?_ ?_ Hh Hlazy ?_
  · apply check_syscall_sound_ok
    rw [Hchk, check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m evs Hs
    have H := check_syscall_complete_ok _ _ _ _ _ Hagree Hs
    rw [Hchk, check_ret_only_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_no_unmodeled _ _ _ _ H
  · simpa only [ms, adv_eff_ret] using Hcont

theorem src_open_dot_wr_eisdir (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 577)
    (Hpath : read_cstr (mrb source_segs mem) (reg_get regs 11) = cstr_result.CstrOk dot_path)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout source_segs (mkst (regupd regs 10 (errno_ret EISDIR))
      (v_addi pc 4) mem (seg_rom source_segs)) model U) :
    to_fout source_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs } model U := by
  let ms : machine_state :=
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs }
  have Hd0 : ms_gpr ms 0 = AT_FDCWD := H10
  have Hp : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = cstr_result.CstrOk dot_path := Hpath
  have Hf : ms_gpr ms 2 = Z_to_bv 64 577 := H12
  have Hchk : ∀ eff, check_syscall (sys_input source_segs ms (getr regs 17)) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model [] := by
    intro eff
    rw [check_syscall_56 source_segs ms (getr regs 17) eff model H17]
    simp only [check_openat, Hf, show modeled_open_flags (Z_to_bv 64 577) = true by decide,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, check_openat_body, in_mem_si, Hp,
      show path_eqb dot_path [] = false by decide, Hd0,
      show bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true by decide,
      check_openat_resolved, show path_has_slash dot_path = false by decide,
      show bv_unsigned (bv_and (Z_to_bv 64 577) (bv_not (Z_to_bv 64 open_ignored_flags))) = 577 by decide,
      show ((577 : Int) == 0) = false by decide,
      show ((577 : Int) == wr_create_flags) = true by decide,
      check_openat_create, show path_is_dirref dot_path = true by decide, Bool.true_or]
    exact check_copyins_after_ret_only _ _ _ _ _
  have Hagree : lookups_agree_at (bv_unsigned (sys_input source_segs ms (getr regs 17)).in_sysno) := by
    rw [in_sysno_si, H17]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_openat
  refine tfo_sys_det source_segs ms model (getr regs 17)
    (with_copyins (open_copyins ms) (mkEffect (errno_ret EISDIR) [] [])) model U rfl ?_ ?_ ?_ Hh Hlazy ?_
  · apply check_syscall_sound_ok
    rw [Hchk, check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m evs Hs
    have H := check_syscall_complete_ok _ _ _ _ _ Hagree Hs
    rw [Hchk, check_ret_only_copyins_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ H
  · simpa only [ms, adv_eff_ret_copyins] using Hcont

theorem src_open_dot_rd_rec (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (Te : Int → word × Fs → Prop) (Ts : word → word × Fs → Prop)
    (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 0)
    (Hpath : read_cstr (mrb source_segs mem) (reg_get regs 11) = cstr_result.CstrOk dot_path)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ openat_errnos →
      to_fout source_segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
        mem (seg_rom source_segs)) model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout source_segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom source_segs))
        (with_fds (fd_insert (m_fds model) fd FdDir) model) (Ts fd))
    (HU : ∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) :
    to_fout source_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs } model U := by
  let ms : machine_state :=
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom source_segs }
  have Hd0 : ms_gpr ms 0 = AT_FDCWD := H10
  have Hp : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = cstr_result.CstrOk dot_path := Hpath
  have Hf : ms_gpr ms 2 = Z_to_bv 64 0 := H12
  apply tfo_open_core source_segs ms model
    (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)
    (getr regs 17) (open_copyins ms) Te Ts U rfl Hh Hlazy
  · intro eff
    rw [check_syscall_56 source_segs ms (getr regs 17) eff model H17]
    simp only [check_openat, Hf, show modeled_open_flags (Z_to_bv 64 0) = true by decide,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, check_openat_body, in_mem_si, Hp,
      show path_eqb dot_path [] = false by decide, Hd0,
      show bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true by decide,
      check_openat_resolved, show path_has_slash dot_path = false by decide,
      show bv_unsigned (bv_and (Z_to_bv 64 0) (bv_not (Z_to_bv 64 open_ignored_flags))) = 0 by decide,
      beq_self_eq_true, check_openat_read, show path_is_dirref dot_path = true by decide]
    unfold check_open_result_copyins open_copyins
    cases Hresult : check_open_result (clear_copyins eff) model
        (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model) with
    | CheckOk m evs => rfl
    | CheckReject => rfl
    | CheckUnmodeled => exact False.elim (check_open_result_never_unmodeled _ _ _ Hresult)
  · intro fd; exact ⟨Hh, Hlazy⟩
  · intro e He; simpa only [ms, adv_eff_ret_copyins] using Herr e He
  · intro fd Hlk Heq; simpa only [ms, adv_eff_ret_copyins] using Hok fd Hlk Heq
  · exact HU

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_empty (Hlen : (src inp).length ≤ 4095) (Hse : path_eqb (src inp) [] = true) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply src_open_empty_rec _ _ _ _ (src inp) _ H17 (by rw [H12]; decide) H10
    (by rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen) Hse rfl rfl
  apply source_exit3 inp rsp rrnd Hsp_lo Hsp_hi
  · regupd_resolve; exact H1
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · exact c_lts_errno ENOENT (by decide) (by decide)
  · rfl

private def headcp_pending (regs : bvmap 5 word) (pc : word) (mem : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
    ms_svc_pending := some (getr regs 17), ms_resv := none,
    ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rrom }

include Hva Hve Hsp_lo Hsp_hi Hge3 in
private theorem headcp_first_file (d0 : List byte) (U : word × Fs → Prop)
    (Hsrc_nodot : openat_plain_name (src inp) = true)
    (Hlen : (src inp).length ≤ 4095) (Hsne : path_eqb (src inp) [] = false)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0)
    (Hcont : ∀ regs2, reg_get regs2 1 = (0x11068 : word) →
      reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
      reg_get regs2 3 = (0x13800 : word) → reg_get regs2 9 = Z_to_bv 64 3 →
      bv_unsigned (getr regs2 17) = 56 → reg_get regs2 10 = AT_FDCWD →
      reg_get regs2 11 = pdst inp rsp → reg_get regs2 12 = Z_to_bv 64 577 →
      to_fout source_segs (headcp_pending regs2 0x11150 (fmem inp rsp rrnd))
        (with_fds (fd_insert (m_fds (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
          (Z_to_bv 64 3) (FdFile (src inp) (Z_to_bv 64 0)))
          (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)) U) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ U o) := by
  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply tfo_open_rd_rec source_segs _ _ _
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) (src inp) d0
    (fun _ o => o = (Z_to_bv 64 3, inp.in_fs)) (fun _ => U) _ H17 H10 H12
    (by rw [H11]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen)
    Hsne Hsrc_nodot Hsome rfl rfl
  · intro e He
    obtain ⟨He1, He2⟩ := openat_errno_range e He
    apply source_exit3 inp rsp rrnd Hsp_lo Hsp_hi
    · regupd_resolve; exact H1
    · regupd_resolve; exact H2
    · regupd_resolve; rfl
    · exact c_lts_errno e He1 He2
    · rfl
  · intro fd Hlk Hfd
    have Hfd3 : fd = Z_to_bv 64 3 := Hfd
    subst fd
    obtain ⟨regs2, G1, G2, G3, G9, G17, G10, G11, G12, Hms2⟩ :=
      source_open1_to_open2 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
        (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        (by regupd_resolve; exact H1) (by regupd_resolve; exact H2)
        (by regupd_resolve; exact H3) (by regupd_resolve; exact H8)
        (by regupd_resolve; rfl) (by decide)
    exact tfo_msteps source_segs _ _ _ _ Hms2 (Hcont regs2 G1 G2 G3 G9 G17 G10 G11 G12)
  · intro o
    constructor
    · rintro (H | H)
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, rfl, H⟩
    · rintro (⟨e, _, H⟩ | ⟨fd, _, _, H⟩)
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 in
private theorem headcp_first_dir (U : word × Fs → Prop)
    (Hsdot : path_eqb (src inp) dot_path = true)
    (Hcont : ∀ regs2, reg_get regs2 1 = (0x11068 : word) →
      reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
      reg_get regs2 3 = (0x13800 : word) → reg_get regs2 9 = Z_to_bv 64 3 →
      bv_unsigned (getr regs2 17) = 56 → reg_get regs2 10 = AT_FDCWD →
      reg_get regs2 11 = pdst inp rsp → reg_get regs2 12 = Z_to_bv 64 577 →
      to_fout source_segs (headcp_pending regs2 0x11150 (fmem inp rsp rrnd))
        (with_fds (fd_insert (m_fds (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
          (Z_to_bv 64 3) FdDir)
          (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)) U) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ U o) := by
  have Hsd := (path_eqb_eq _ _).mp Hsdot
  have Hlen : (src inp).length ≤ 4095 := by rw [Hsd]; decide
  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply src_open_dot_rd_rec _ _ _ _
    (fun _ o => o = (Z_to_bv 64 3, inp.in_fs)) (fun _ => U) _ H17 H10 H12
    (by rw [H11, ← Hsd]; exact source_cstr_src inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen)
    rfl rfl
  · intro e He
    obtain ⟨He1, He2⟩ := openat_errno_range e He
    apply source_exit3 inp rsp rrnd Hsp_lo Hsp_hi
    · regupd_resolve; exact H1
    · regupd_resolve; exact H2
    · regupd_resolve; rfl
    · exact c_lts_errno e He1 He2
    · rfl
  · intro fd Hlk Hfd
    have Hfd3 : fd = Z_to_bv 64 3 := Hfd
    subst fd
    obtain ⟨regs2, G1, G2, G3, G9, G17, G10, G11, G12, Hms2⟩ :=
      source_open1_to_open2 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
        (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        (by regupd_resolve; exact H1) (by regupd_resolve; exact H2)
        (by regupd_resolve; exact H3) (by regupd_resolve; exact H8)
        (by regupd_resolve; rfl) (by decide)
    exact tfo_msteps source_segs _ _ _ _ Hms2 (Hcont regs2 G1 G2 G3 G9 G17 G10 G11 G12)
  · intro o
    constructor
    · rintro (H | H)
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, rfl, H⟩
    · rintro (⟨e, _, H⟩ | ⟨fd, _, _, H⟩)
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 in
private theorem headcp_second_file (entry : FdEntry) (regs2 : bvmap 5 word)
    (U : word × Fs → Prop)
    (Hlen : (dst inp).length ≤ 4095) (Hdne : path_eqb (dst inp) [] = false)
    (Hdst_nodot : openat_plain_name (dst inp) = true)
    (G1 : reg_get regs2 1 = (0x11068 : word))
    (G2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (G3 : reg_get regs2 3 = (0x13800 : word)) (G9 : reg_get regs2 9 = Z_to_bv 64 3)
    (G17 : bv_unsigned (getr regs2 17) = 56) (G10 : reg_get regs2 10 = AT_FDCWD)
    (G11 : reg_get regs2 11 = pdst inp rsp) (G12 : reg_get regs2 12 = Z_to_bv 64 577)
    (Hcont : ∀ regs3, bv_unsigned (getr regs3 17) = 63 →
      reg_get regs3 10 = Z_to_bv 64 3 → reg_get regs3 11 = sbuf →
      reg_get regs3 12 = Z_to_bv 64 128 → reg_get regs3 1 = (0x11094 : word) →
      reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 48) →
      reg_get regs3 3 = (0x13800 : word) → reg_get regs3 8 = Z_to_bv 64 4 →
      reg_get regs3 9 = Z_to_bv 64 3 →
      to_fout source_segs (headcp_pending regs3 0x11150 (fmem inp rsp rrnd))
        (with_fds (fd_insert (fd_insert (m_fds (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
          (Z_to_bv 64 3) entry) (Z_to_bv 64 4) (FdFileW (dst inp) (Z_to_bv 64 0)))
          (with_fs (fs_set inp.in_fs (dst inp) [])
            (with_fds (fd_insert (m_fds (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
              (Z_to_bv 64 3) entry)
              (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)))) U) :
    to_fout source_segs (headcp_pending regs2 0x11150 (fmem inp rsp rrnd))
      (with_fds (fd_insert (m_fds (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
        (Z_to_bv 64 3) entry)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
      (fun o => o = (Z_to_bv 64 4, inp.in_fs) ∨ (fs_under inp.in_fs (dst inp) = false ∧ U o)) := by
  cases Hun : fs_under inp.in_fs (dst inp) with
  | true =>
    apply tfo_open_wr_isdir_rec source_segs _ _ _ (with_fds (fd_insert (m_fds (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
        (Z_to_bv 64 3) entry)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)) (dst inp) _ G17 G10 G12
      (by rw [G11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen)
      Hdne Hdst_nodot Hun rfl rfl
    apply tfo_equiv source_segs _ _ (fun o => o = (Z_to_bv 64 4, inp.in_fs))
    · apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi
      · regupd_resolve; exact G1
      · regupd_resolve; exact G2
      · regupd_resolve; rfl
      · decide
      · decide
      · rfl
    · intro o; simp only [Bool.true_eq_false, false_and, or_false]
  | false =>
    apply tfo_open_wr_rec source_segs _ _ _ (with_fds (fd_insert (m_fds (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
        (Z_to_bv 64 3) entry)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)) (dst inp)
      (fun _ o => o = (Z_to_bv 64 4, inp.in_fs)) (fun _ => U) _ G17 G10 G12
      (by rw [G11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen)
      Hdne Hdst_nodot Hun rfl rfl
    · intro e He
      obtain ⟨He1, He2⟩ := openat_errno_range e He
      apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi
      · regupd_resolve; exact G1
      · regupd_resolve; exact G2
      · regupd_resolve; rfl
      · exact He1
      · exact He2
      · rfl
    · intro fd2 Hlk Hfd
      have Hfd4 : fd2 = Z_to_bv 64 4 := Hfd
      subst fd2
      obtain ⟨regs3, K17, K10, K11, K12, K1, K2, K3, K8, K9, Hms3⟩ :=
        src_open2_to_read (regupd regs2 10 (Z_to_bv 64 4)) (fmem inp rsp rrnd)
          (Z_to_bv 64 3) (Z_to_bv 64 4) (Z_to_bv 64 (bv_unsigned rsp - 48))
          (by regupd_resolve; exact G1) (by regupd_resolve; exact G2)
          (by regupd_resolve; exact G3) (by regupd_resolve; exact G9)
          (by regupd_resolve; rfl) (by decide)
      exact tfo_msteps source_segs _ _ _ _ Hms3 (Hcont regs3 K17 K10 K11 K12 K1 K2 K3 K8 K9)
    · intro o
      constructor
      · rintro (H | ⟨_, H⟩)
        · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
        · exact Or.inr ⟨Z_to_bv 64 4, rfl, rfl, H⟩
      · rintro (⟨e, _, H⟩ | ⟨fd, _, _, H⟩)
        · exact Or.inl H
        · exact Or.inr ⟨rfl, H⟩

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_present (Hsrc_nodot : openat_plain_name (src inp) = true)
    (Hdst_nodot : openat_plain_name (dst inp) = true) (d0 : List byte)
    (Hlen1 : (src inp).length ≤ 4095) (Hlen2 : (dst inp).length ≤ 4095)
    (Hsne : path_eqb (src inp) [] = false) (Hdne : path_eqb (dst inp) [] = false)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (hc_outcomes inp.in_fs (src inp) (dst inp)) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  let chunk := file_read (hc_data inp.in_fs (src inp) (dst inp)) (Z_to_bv 64 0) (Z_to_bv 64 128)
  let Nc := len_word chunk
  have Hclen : chunk.length ≤ 128 := hc_chunk_le _
  have HNc : bv_unsigned Nc = (chunk.length : Int) := u_len_word chunk (by omega)
  let mr := write_to_mem (fmem inp rsp rrnd) sbuf chunk
  let mw := spill rsp mr Nc
  let mc1 := wbytes mw (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 (0x110d8 : word))
  let mc2 := wbytes mc1 (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 (0x110e0 : word))
  have HgrowR : mem_grows (wmem inp rsp rrnd) mr := by
    unfold mr fmem emem; solve_mem_grows
  have HgrowW : mem_grows (wmem inp rsp rrnd) mw := by
    unfold mw spill; solve_mem_grows
  have HgrowC1 : mem_grows (wmem inp rsp rrnd) mc1 := by
    unfold mc1; solve_mem_grows
  apply tfo_equiv source_segs _ _
    (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs) ∨
      (fs_under inp.in_fs (dst inp) = false ∧ o = (Z_to_bv 64 0, hc_final_fs inp.in_fs (src inp) (dst inp))))
  · apply headcp_first_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
    intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
    apply headcp_second_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3
      (FdFile (src inp) (Z_to_bv 64 0)) regs2
      (fun o => o = (Z_to_bv 64 0, hc_final_fs inp.in_fs (src inp) (dst inp)))
      Hlen2 Hdne Hdst_nodot G1 G2 G3 G9 G17 G10 G11 G12
    intro regs3 K17 K10 K11 K12 K1 K2 K3 K8 K9
    refine tfo_read_rec source_segs regs3 0x11150 (fmem inp rsp rrnd) rrom _
      (Z_to_bv 64 3) (src inp) (Z_to_bv 64 0) (hc_data inp.in_fs (src inp) (dst inp))
      sbuf (Z_to_bv 64 128) _ K17 K10 K11 K12 ?_ rfl ?_ source_buf_wseg
      (by decide) (by decide) (by decide) rfl rfl ?_
    · rfl
    · exact hc_data_lookup inp.in_fs (src inp) (dst inp) d0 Hsome
    obtain ⟨regs4, L17, L10, L11, L12, L1, L2, L8, L9, Hms4⟩ :=
      src_read_to_write inp rsp rrnd Hsp_lo Hsp_hi (regupd regs3 10 Nc) mr
        (Z_to_bv 64 3) (Z_to_bv 64 4) Nc
        (by regupd_resolve; exact K1) (by regupd_resolve; exact K2)
        (by regupd_resolve; exact K3) (by regupd_resolve; exact K8)
        (by regupd_resolve; exact K9) (by regupd_resolve; rfl)
        (by rw [HNc]; omega) HgrowR
    apply tfo_msteps source_segs _ _ _ _ Hms4
    refine tfo_write_rec source_segs regs4 0x11150 mw _ (Z_to_bv 64 4)
      (dst inp) (Z_to_bv 64 0) [] chunk sbuf Nc _ L17 L10 L11 L12
      ?_ rfl ?_ ?_ ?_ ?_ ?_ rfl rfl ?_
    · rfl
    · have Hnat : word_to_nat Nc = chunk.length := by
        unfold word_to_nat; unfold bv_unsigned at HNc; omega
      rw [Hnat]
      unfold mw spill mr
      rw [rdn_wbytes_below]
      · apply rdn_write_to_mem; rw [u_sbuf]; omega
      all_goals try rw [length_N_to_le_bytes]
      all_goals try rw [u_sbuf]
      all_goals u_norm; omega
    · rw [HNc]; unfold rw_bytes_max; omega
    · exact fs_lookup_set_eq _ _ _
    · apply file_gap_in_range; decide
    · left
      apply access_okb_intro
      rw [u_sbuf, HNc]
      unfold TASK_SIZE
      omega
    obtain ⟨regs5, M2, M8, M9, Hms5⟩ :=
      src_write_to_ret rsp Hsp_lo Hsp_hi (regupd regs4 10 Nc) mw
        (Z_to_bv 64 3) (Z_to_bv 64 4) Nc
        (by regupd_resolve; exact L1) (by regupd_resolve; exact L2)
        (by regupd_resolve; exact L8) (by regupd_resolve; exact L9)
        (by regupd_resolve; rfl) (rdn_spill_cnt rsp Hsp_lo Hsp_hi mr Nc)
    apply tfo_msteps source_segs _ _ _ _ Hms5
    apply to_fout.tfo_step _ _ _ _ rfl
    · apply step_addiw_at (v := Z_to_bv 64 3)
        (hf := SF_110d0) (he := rfl) (hd := SD_110d0) (hrd := rfl)
      getr_resolve; rw [M9]; decide
    norm_pc
    apply to_fout.tfo_step _ _ _ _ rfl
    · exact step_jal_link _ _ _ _ _ _ _ _ SF_110d4 rfl SD_110d4
    norm_pc
    obtain ⟨regs6, N17, N10, N1, N2, N8, N9, Hms6⟩ :=
      src_close_call inp rsp rrnd Hsp_lo Hsp_hi
        (regupd (regupd regs5 10 (Z_to_bv 64 3)) 1 (0x110d8 : word)) mw
        (Z_to_bv 64 3) (0x110d8 : word) (Z_to_bv 64 4) (Z_to_bv 64 3)
        (by regupd_resolve; rfl) (by regupd_resolve; exact M2)
        (by regupd_resolve; exact M8) (by regupd_resolve; exact M9)
        (by regupd_resolve; rfl) HgrowW
    apply tfo_msteps source_segs _ _ _ _ Hms6
    refine tfo_close_rec source_segs _ _ _ _ _ (Z_to_bv 64 3) (FdFile (src inp) (Z_to_bv 64 0 + Nc)) _ N17 N10 ?_ rfl rfl rfl ?_
    · rfl
    obtain ⟨regs7, P1, P2, P8, P9, P10, Hms7⟩ :=
      src_close_tail rsp Hsp_lo Hsp_hi (regupd regs6 10 (Z_to_bv 64 0)) mc1
        (0x110d8 : word) (Z_to_bv 64 4) (Z_to_bv 64 3)
        (by regupd_resolve; exact N1) (by regupd_resolve; exact N2)
        (by regupd_resolve; exact N8) (by regupd_resolve; exact N9)
        (by regupd_resolve; rfl) (by apply rdn_wbytes_hit8; u_norm; omega)
    apply tfo_msteps source_segs _ _ _ _ Hms7
    apply to_fout.tfo_step _ _ _ _ rfl
    · apply step_jalr_x0 (tgt := (0x110d8 : word))
        (hf := SF_111a4) (he := rfl) (hd := SD_111a4)
      getr_resolve; exact P1
    norm_pc
    apply to_fout.tfo_step _ _ _ _ rfl
    · apply step_addiw_at (v := Z_to_bv 64 4)
        (hf := SF_110d8) (he := rfl) (hd := SD_110d8) (hrd := rfl)
      getr_resolve; rw [P8]; decide
    norm_pc
    apply to_fout.tfo_step _ _ _ _ rfl
    · exact step_jal_link _ _ _ _ _ _ _ _ SF_110dc rfl SD_110dc
    norm_pc
    obtain ⟨regs8, Q17, Q10, Q1, Q2, Q8, Q9, Hms8⟩ :=
      src_close_call inp rsp rrnd Hsp_lo Hsp_hi
        (regupd (regupd regs7 10 (Z_to_bv 64 4)) 1 (0x110e0 : word)) mc1
        (Z_to_bv 64 4) (0x110e0 : word) (Z_to_bv 64 4) (Z_to_bv 64 3)
        (by regupd_resolve; rfl) (by regupd_resolve; exact P2)
        (by regupd_resolve; exact P8) (by regupd_resolve; exact P9)
        (by regupd_resolve; rfl) HgrowC1
    apply tfo_msteps source_segs _ _ _ _ Hms8
    refine tfo_close_rec source_segs _ _ _ _ _ (Z_to_bv 64 4) (FdFileW (dst inp) (Z_to_bv 64 0 + Nc)) _ Q17 Q10 ?_ rfl rfl rfl ?_
    · rfl
    obtain ⟨regs9, S1, S2, S8, S9, S10, Hms9⟩ :=
      src_close_tail rsp Hsp_lo Hsp_hi (regupd regs8 10 (Z_to_bv 64 0)) mc2
        (0x110e0 : word) (Z_to_bv 64 4) (Z_to_bv 64 3)
        (by regupd_resolve; exact Q1) (by regupd_resolve; exact Q2)
        (by regupd_resolve; exact Q8) (by regupd_resolve; exact Q9)
        (by regupd_resolve; rfl) (by apply rdn_wbytes_hit8; u_norm; omega)
    apply tfo_msteps source_segs _ _ _ _ Hms9
    apply to_fout.tfo_step _ _ _ _ rfl
    · apply step_jalr_x0 (tgt := (0x110e0 : word))
        (hf := SF_111a4) (he := rfl) (hd := SD_111a4)
      getr_resolve; exact S1
    norm_pc
    apply to_fout.tfo_step _ _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 0)
        (hf := SF_110e0) (he := rfl) (hd := SD_110e0) (hrd := rfl)
      getr_resolve; rfl
    norm_pc
    apply source_exit_tail rsp Hsp_lo Hsp_hi
    · regupd_resolve; exact S2
    · regupd_resolve; rfl
    · decide
    · unfold mc2 mc1 mw spill mr
      rw [rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wtm_out]
      · exact fmem_ra_slot inp rsp rrnd Hsp_lo Hsp_hi
      all_goals try rw [length_N_to_le_bytes]
      all_goals try rw [u_sbuf]
      all_goals u_norm; omega
    · unfold mc2 mc1 mw spill mr
      rw [rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wtm_out]
      · exact fmem_s0_slot inp rsp rrnd Hsp_lo Hsp_hi
      all_goals try rw [length_N_to_le_bytes]
      all_goals try rw [u_sbuf]
      all_goals u_norm; omega
    · unfold mc2 mc1 mw spill mr
      rw [rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wtm_out]
      · exact fmem_s1_slot inp rsp rrnd Hsp_lo Hsp_hi
      all_goals try rw [length_N_to_le_bytes]
      all_goals try rw [u_sbuf]
      all_goals u_norm; omega
    · exact hc_final_collapse inp.in_fs (src inp) (dst inp)
  · intro o; simp only [hc_outcomes, Hsome]

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_present_dst_empty (Hsrc_nodot : openat_plain_name (src inp) = true)
    (d0 : List byte) (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : (dst inp).length ≤ 4095)
    (Hsne : path_eqb (src inp) [] = false) (Hde : path_eqb (dst inp) [] = true)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
  intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
  apply src_open_empty_rec _ _ _ _ (dst inp) _ G17 (by rw [G12]; decide) G10
    (by rw [G11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2) Hde rfl rfl
  apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi (e := ENOENT)
  · regupd_resolve; exact G1
  · regupd_resolve; exact G2
  · regupd_resolve; rfl
  · decide
  · decide
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_dst_dot (Hsrc_nodot : openat_plain_name (src inp) = true)
    (d0 : List byte) (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : (dst inp).length ≤ 4095)
    (Hsne : path_eqb (src inp) [] = false) (Hddot : path_eqb (dst inp) dot_path = true)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
  intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
  apply src_open_dot_wr_eisdir _ _ _ _ _ G17 G10 G12
    (by rw [G11, ← (path_eqb_eq _ _).mp Hddot]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi (e := EISDIR)
  · regupd_resolve; exact G1
  · regupd_resolve; exact G2
  · regupd_resolve; rfl
  · decide
  · decide
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_toolong (Hlen : 4096 ≤ (src inp).length) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
  obtain ⟨regs1, H1, H2, H3, H8, H17, H10, H11, H12, Hms⟩ :=
    source_to_open1 inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps source_segs _ _ _ _ Hms
  apply tfo_open_toolong_rec source_segs _ _ _ _ _ H17 (by rw [H12]; decide)
    (by rw [H11]; exact source_cstr_src_long inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen) rfl rfl
  apply source_exit3 inp rsp rrnd Hsp_lo Hsp_hi
  · regupd_resolve; exact H1
  · regupd_resolve; exact H2
  · regupd_resolve; rfl
  · exact c_lts_errno ENAMETOOLONG (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_present_dst_toolong (Hsrc_nodot : openat_plain_name (src inp) = true)
    (d0 : List byte) (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : 4096 ≤ (dst inp).length)
    (Hsne : path_eqb (src inp) [] = false)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
  intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
  apply tfo_open_toolong_rec source_segs _ _ _ _ _ G17 (by rw [G12]; decide)
    (by rw [G11]; exact source_cstr_dst_long inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi (e := ENAMETOOLONG)
  · regupd_resolve; exact G1
  · regupd_resolve; exact G2
  · regupd_resolve; rfl
  · decide
  · decide
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot (Hlen2 : (dst inp).length ≤ 4095)
    (Hsdot : path_eqb (src inp) dot_path = true)
    (Hdne : path_eqb (dst inp) [] = false) (Hddot : openat_plain_name (dst inp) = true) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs) ∨
        (fs_under inp.in_fs (dst inp) = false ∧ o = (Z_to_bv 64 5, fs_set inp.in_fs (dst inp) []))) := by
  apply headcp_first_dir inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
  apply headcp_second_file inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 FdDir regs2
    (fun o => o = (Z_to_bv 64 5, fs_set inp.in_fs (dst inp) [])) Hlen2 Hdne Hddot
    G1 G2 G3 G9 G17 G10 G11 G12
  intro regs3 K17 K10 K11 K12 K1 K2 K3 K8 K9
  refine src_read_dir_eisdir regs3 0x11150 (fmem inp rsp rrnd) _ (Z_to_bv 64 3) _
    K17 K10 ?_ rfl ?_ rfl rfl ?_
  · rfl
  · rw [K11, K12]; decide
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  sym_block_ex source_segs
    (mkst (regupd regs3 10 (errno_ret EISDIR)) (Z_to_bv 64 69972) (fmem inp rsp rrnd) rrom)
    4 [true] [] [(1, ELit 0x11094), (10, EVar 32)] [errno_ret EISDIR] [] R HR Hms
  all_goals try (solve
    | exact c_lts_errno EISDIR (by decide) (by decide)
    | (headcp_eq_goal; getr_resolve; regupd_resolve; exact K1)
    | (headcp_eq_goal; getr_resolve; regupd_resolve; rfl))
  apply tfo_msteps source_segs _ _ _ _ Hms
  sym_pc_lit
  apply source_exit_tail rsp Hsp_lo Hsp_hi
  · sym_regs HR; getr_resolve; regupd_resolve; exact K2
  · headcp_out HR
  · decide
  · exact fmem_ra_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact fmem_s0_slot inp rsp rrnd Hsp_lo Hsp_hi
  · exact fmem_s1_slot inp rsp rrnd Hsp_lo Hsp_hi
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot_dstempty
    (Hlen2 : (dst inp).length ≤ 4095) (Hsdot : path_eqb (src inp) dot_path = true) (Hde : path_eqb (dst inp) [] = true) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_dir inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
  apply src_open_empty_rec _ _ _ _ (dst inp) _ G17 (by rw [G12]; decide) G10
    (by rw [G11]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2) Hde rfl rfl
  apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi (e := ENOENT)
  · regupd_resolve; exact G1
  · regupd_resolve; exact G2
  · regupd_resolve; rfl
  · decide
  · decide
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot_dstdot
    (Hlen2 : (dst inp).length ≤ 4095) (Hsdot : path_eqb (src inp) dot_path = true) (Hddot : path_eqb (dst inp) dot_path = true) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_dir inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
  apply src_open_dot_wr_eisdir _ _ _ _ _ G17 G10 G12
    (by rw [G11, ← (path_eqb_eq _ _).mp Hddot]; exact source_cstr_dst inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi (e := EISDIR)
  · regupd_resolve; exact G1
  · regupd_resolve; exact G2
  · regupd_resolve; rfl
  · decide
  · decide
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem source_src_dot_dst_toolong
    (Hlen2 : 4096 ≤ (dst inp).length) (Hsdot : path_eqb (src inp) dot_path = true) :
    to_fout source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_dir inp Hva Hve rsp rrnd Hsp_lo Hsp_hi rbrk rmb Hge3 _ Hsdot
  intro regs2 G1 G2 G3 G9 G17 G10 G11 G12
  apply tfo_open_toolong_rec source_segs _ _ _ _ _ G17 (by rw [G12]; decide)
    (by rw [G11]; exact source_cstr_dst_long inp Hva Hve rsp rrnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply source_exit4 inp rsp rrnd Hsp_lo Hsp_hi (e := ENAMETOOLONG)
  · regupd_resolve; exact G1
  · regupd_resolve; exact G2
  · regupd_resolve; rfl
  · decide
  · decide
  · rfl

end Ge3
include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_lt3 (Hlt3 : inp.in_argv.length < 3) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11100 source_phdrs rsp rrnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      [] (Z_to_bv 64 2) := by
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hargc := valid_argv_len inp.in_argv Hva
  have Hbr : c_lts (Z_to_bv 64 2) (argcN inp) = false := by
    rw [c_lts_small _ _ (by decide +kernel) (by rw [u_argcN inp Hva]; omega)]
    rw [Bool.eq_false_iff]
    intro H
    change BitVec.ult _ _ = true at H
    rw [BitVec.ult_iff_lt, BitVec.lt_def] at H
    have Hu := u_argcN inp Hva
    unfold bv_unsigned at Hu
    change 2 < (argcN inp).toNat at H
    omega
  rw [init_mkst]
  sym_block source_segs 30 [true] [EVar 33] [(2, EVar 32)]
    [rsp] [argcN inp] R HR
  all_goals repeat' apply And.intro
  all_goals try (solve
    | (apply source_store_ok <;> decide +kernel)
    | (refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
       change rdn source_segs (wmem inp rsp rrnd) (v_addi rsp 0) 8 = _
       rw [v_addi_0]
       exact read_argc_w inp Hva Hve rsp rrnd Hsp_hi)
    | (change (!c_lts (Z_to_bv 64 2) (argcN inp)) = true; rw [Hbr]; rfl)
    | (u_norm; omega))
  · exact getr_same _ 2 rsp (by decide)
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ SF_11130 rfl
  apply tw_exit_coden
  · headcp_out HR
  · headcp_out HR
  · decide +kernel

end SourceProof
end LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_source
