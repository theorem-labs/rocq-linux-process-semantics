import LinuxProcessSemantics.Examples.cp_ns.cp_ns_defs
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.ArgvEnv

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

namespace LinuxProcessSemantics.Examples.cp_ns.cp_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.cp_ns.SourceMemImage
open LinuxProcessSemantics.Examples.cp_ns.TargetMemImage
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 800000

open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
open LinuxProcessSemantics.Common.FileSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.ErrEscape
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open FdEntry
open config

open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Common.ArgvEnv
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_defs

def trom : word → Option byte := seg_rom target_segs
def tbuf : word := 0x1002298

theorem u_tbuf : bv_unsigned tbuf = 0x1002298 := rfl

theorem c_eq_bu_true (b : byte) (h : b = Z_to_bv 8 0) :
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = true := by
  subst b; rfl

theorem c_eq_bu_false (b : byte) (h : b ≠ Z_to_bv 8 0) :
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false := by
  apply c_eq_0_false
  rw [u_Z2bv _ (by have := u8_range b; omega) (by have := u8_range b; omega)]
  intro hz
  apply h
  apply bv_eq_of_unsigned
  exact hz

theorem In_firstn_incl (A : Type) (x : A) (n : Nat) (l : List A)
    (h : x ∈ l.take n) : x ∈ l := List.mem_of_mem_take h

theorem c_eq_0_of_u (x : word) (h : bv_unsigned x = 0) :
    c_eq x (Z_to_bv 64 0) = true := by
  have hx : x = Z_to_bv 64 0 := bv_eq_of_unsigned _ _ h
  rw [hx]; rfl

local macro "t_out" h:ident : tactic => `(tactic| (
  sym_regs $h
  repeat rw [getr_nz _ _ (by decide)]
  try simp only [Int.ofNat_zero, Int.add_zero]
  try (change v_addi _ 0 = _; rw [v_addi_0])
  all_goals first | assumption | sym_close | rfl))

theorem tgt_head_to_read (regs : bvmap 5 word) (mem : word → Option byte) (fdin fdout : word) :
  reg_get regs 1 = (0x10011b0 : word) →
  reg_get regs 13 = fdout → reg_get regs 14 = fdin →
  reg_get regs 15 = tbuf →
  ∃ regs',
    bv_unsigned (getr regs' 17) = 63 ∧
    reg_get regs' 10 = fdin ∧ reg_get regs' 11 = tbuf ∧
    reg_get regs' 12 = Z_to_bv 64 1024 ∧
    reg_get regs' 1 = (0x10011b0 : word) ∧
    reg_get regs' 13 = fdout ∧ reg_get regs' 14 = fdin ∧
    reg_get regs' 15 = tbuf ∧
    msteps target_segs (mkst regs (0x100120c : word) mem trom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x100121c : word),
         ms_svc_pending := some (getr regs' 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
         ms_mem := mem, ms_rom := trom } := by
  intro H1 H13 H14 H15
  sym_pc_Z
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781836) mem trom)
    5 ([] : List Bool) ([] : List expr) ([] : List (reg × expr)) ([] : List word)
    ([] : List word) R HR Hms
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · t_out HR
  · t_out HR
  · t_out HR
  · t_out HR
  · t_out HR
  · t_out HR
  · t_out HR
  · t_out HR
  · apply msteps_trans _ _ _ _ Hms
    sym_pc_lit
    exact msteps.mst_step _ _ _ rfl
      (step_ecall _ _ _ _ _ _ TF_100121c rfl) (msteps.mst_refl _)

theorem tgt_read_to_write (regs : bvmap 5 word) (mem : word → Option byte) (fdin fdout cnt : word) :
  reg_get regs 10 = cnt →
  (1 ≤ bv_unsigned cnt) → (bv_unsigned cnt ≤ 1024) →
  reg_get regs 1 = (0x10011b0 : word) →
  reg_get regs 13 = fdout → reg_get regs 14 = fdin →
  reg_get regs 15 = tbuf →
  ∃ regs',
    bv_unsigned (getr regs' 17) = 64 ∧
    reg_get regs' 10 = fdout ∧ reg_get regs' 11 = tbuf ∧
    reg_get regs' 12 = cnt ∧
    reg_get regs' 1 = (0x10011b0 : word) ∧
    reg_get regs' 13 = fdout ∧ reg_get regs' 14 = fdin ∧
    reg_get regs' 15 = tbuf ∧
    msteps target_segs (mkst regs (0x1001220 : word) mem trom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x100123c : word),
         ms_svc_pending := some (getr regs' 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
         ms_mem := mem, ms_rom := trom } := by
  intro H10 Hc1 Hc2 H1 H13 H14 H15
  sym_pc_Z
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781856) mem trom)
    8 [false, false, false] ([] : List expr) [((10 : reg), EVar 32)] [cnt]
    ([] : List word) R HR Hms
  · repeat' apply And.intro
    all_goals first | (apply c_eq_0_false; omega) | (apply c_lts_pos_0; omega)
  · exact H10
  · refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · apply msteps_trans _ _ _ _ Hms
      sym_pc_lit
      exact msteps.mst_step _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_100123c rfl) (msteps.mst_refl _)

theorem tgt_write_to_head (regs : bvmap 5 word) (mem : word → Option byte) (fdin fdout cnt : word) :
  reg_get regs 10 = cnt → reg_get regs 12 = cnt →
  (1 ≤ bv_unsigned cnt) → (bv_unsigned cnt ≤ 1024) →
  reg_get regs 1 = (0x10011b0 : word) →
  reg_get regs 13 = fdout → reg_get regs 14 = fdin →
  reg_get regs 15 = tbuf →
  ∃ regs',
    reg_get regs' 1 = (0x10011b0 : word) ∧
    reg_get regs' 13 = fdout ∧ reg_get regs' 14 = fdin ∧
    reg_get regs' 15 = tbuf ∧
    msteps target_segs (mkst regs (0x1001240 : word) mem trom)
      (mkst regs' (0x100120c : word) mem trom) := by
  intro H10 H12 Hc1 Hc2 H1 H13 H14 H15
  sym_pc_Z
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781888) mem trom)
    4 [false, true] ([] : List expr)
    [((10 : reg), EVar 32), ((12 : reg), EVar 32)] [cnt]
    ([] : List word) R HR Hms
  · repeat' apply And.intro
    all_goals first
      | (apply c_eq_0_of_u; rw [v_sub_small _ _ (by omega)]; omega)
      | (rw [Bool.not_eq_false']; apply c_lts_0_pos <;> omega)
  · exact H10
  · exact H12
  · refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · apply msteps_trans _ _ _ _ Hms
      sym_pc_lit
      exact msteps.mst_refl _

theorem tgt_eof_to_close (regs : bvmap 5 word) (mem : word → Option byte) (fdin fdout : word) :
  reg_get regs 1 = (0x10011b0 : word) →
  reg_get regs 10 = Z_to_bv 64 0 →
  reg_get regs 13 = fdout → reg_get regs 14 = fdin →
  ∃ regs',
    bv_unsigned (getr regs' 17) = 57 ∧
    reg_get regs' 10 = fdin ∧
    reg_get regs' 1 = (0x10011b0 : word) ∧
    reg_get regs' 13 = fdout ∧
    msteps target_segs (mkst regs (0x1001220 : word) mem trom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x1001280 : word),
         ms_svc_pending := some (getr regs' 17), ms_resv := none,
         ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom } := by
  intro H1 H10 H13 H14
  sym_pc_Z
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781856) mem trom)
    6 [false, true] ([] : List expr)
    [((10 : reg), ELit 0), ((14 : reg), EVar 32)] [fdin]
    ([] : List word) R HR Hms
  · decide +kernel
  · exact H10
  · exact H14
  · refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · apply msteps_trans _ _ _ _ Hms
      sym_pc_lit
      exact msteps.mst_step _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_1001280 rfl) (msteps.mst_refl _)

theorem tgt_close_to_close (regs : bvmap 5 word) (mem : word → Option byte) (fdout : word) :
  reg_get regs 1 = (0x10011b0 : word) →
  reg_get regs 13 = fdout →
  ∃ regs',
    bv_unsigned (getr regs' 17) = 57 ∧
    reg_get regs' 10 = fdout ∧
    reg_get regs' 1 = (0x10011b0 : word) ∧
    msteps target_segs (mkst regs (0x1001284 : word) mem trom)
      { ms_regs := regs', ms_fregs := bvmap_empty, ms_pc_val := (0x100128c : word),
         ms_svc_pending := some (getr regs' 17), ms_resv := none,
         ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom } := by
  intro H1 H13
  sym_pc_Z
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781956) mem trom)
    3 ([] : List Bool) ([] : List expr)
    [((13 : reg), EVar 32)] [fdout] ([] : List word) R HR Hms
  · exact H13
  · refine ⟨R, ?_, ?_, ?_, ?_⟩
    · t_out HR
    · t_out HR
    · t_out HR
    · apply msteps_trans _ _ _ _ Hms
      sym_pc_lit
      exact msteps.mst_step _ _ _ rfl
        (step_ecall _ _ _ _ _ _ TF_100128c rfl) (msteps.mst_refl _)

theorem tgt_loop_exit0 (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (fsv : Fs)
    (H1 : reg_get regs 1 = (0x10011b0 : word)) (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x1001290 mem trom) model
      (fun o => o = (Z_to_bv 64 0, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781968) mem trom)
    6 [] [] [(1, ELit 0x10011b0)] [] [] R HR Hms
  · exact H1
  · apply tfo_msteps _ _ _ _ _ Hms
    sym_pc_lit
    apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011b4 rfl)
    apply tfo_exit_rec
    · t_out HR
    · t_out HR
    · decide +kernel
    · exact Hfs

def tLH (fdin fdout : word) (regs : bvmap 5 word) : Prop :=
  reg_get regs 1 = (0x10011b0 : word) ∧
  reg_get regs 13 = fdout ∧ reg_get regs 14 = fdin ∧ reg_get regs 15 = tbuf

def tMI (fs0v : Fs) (srcp dstp : path) (D : List byte) (fdin fdout : word)
    (k : Nat) (model : Model) : Prop :=
  m_halted model = none ∧ m_vm_lazy model = [] ∧
  fd_lookup (m_fds model) fdin = some (FdFile srcp (nat_to_word k)) ∧
  fd_lookup (m_fds model) fdout = some (FdFileW dstp (nat_to_word k)) ∧
  m_fs model = fs_set fs0v dstp (D.take k)

theorem target_loop (fs0v : Fs) (srcp dstp : path) (D : List byte) (fdin fdout : word)
    (HD : fs_lookup (fs_set fs0v dstp []) srcp = some D) (Hneq : fdin ≠ fdout)
    (Hfin31 : bv_unsigned fdin < 2^31) (Hfout31 : bv_unsigned fdout < 2^31)
    (HDlen : (D.length : Int) < 2^64) (rem k : Nat) (regs : bvmap 5 word)
    (mem : word → Option byte) (model : Model)
    (Hrem : D.length - k < rem) (Hk : k ≤ D.length)
    (HLH : tLH fdin fdout regs) (HMI : tMI fs0v srcp dstp D fdin fdout k model) :
    to_fout target_segs (mkst regs 0x100120c mem trom) model
      (fun o => o = (Z_to_bv 64 0, fs_set fs0v dstp D)) := by
  induction rem generalizing k regs mem model with
  | zero => omega
  | succ rem IH =>
    obtain ⟨H1, H13, H14, H15⟩ := HLH
    obtain ⟨Hh, Hlazy, Hfdin, Hfdout, Hfs⟩ := HMI
    have HkZ : (k : Int) < 2^64 := by omega
    let chunk := file_read D (nat_to_word k) (Z_to_bv 64 1024)
    have Hclen : chunk.length = min 1024 (D.length - k) := cp_chunk_len D k HkZ
    have Hc1024 : chunk.length ≤ 1024 := by omega
    obtain ⟨regsR, R17, R10, R11, R12, R1, R13, R14, R15, HmsR⟩ :=
      tgt_head_to_read regs mem fdin fdout H1 H13 H14 H15
    apply tfo_msteps _ _ _ _ _ HmsR
    apply tfo_read_rec (p := srcp) (off := nat_to_word k) (data := D)
      (buf := tbuf) (cnt := Z_to_bv 64 1024) (fdv := fdin)
      (H17 := R17) (H10 := R10) (H11 := R11) (H12 := R12)
      (Hfd := Hfdin) (Hfd32 := fd32_lt31 fdin Hfin31)
      (Hh := Hh) (Hlazy := Hlazy)
    · rw [Hfs]; exact cp_lookup_src_k fs0v srcp dstp D k HD Hk
    · exact target_buf_wseg
    · decide +kernel
    · decide +kernel
    · apply access_okb_intro; rw [u_tbuf]; decide +kernel
    · change to_fout target_segs
        (mkst (regupd regsR 10 (len_word chunk)) 0x1001220 (write_to_mem mem tbuf chunk) trom)
        (with_fds (fd_insert (m_fds model) fdin (FdFile srcp (nat_to_word k + len_word chunk))) model) _
      by_cases Heq : k = D.length
      · have Hchn : chunk = [] := by
          apply file_read_nil
          rw [wtn_ntw _ HkZ]; omega
        rw [Hchn]
        simp only [write_to_mem]
        change to_fout target_segs (mkst (regupd regsR 10 (Z_to_bv 64 0)) 0x1001220 mem trom)
          (with_fds (fd_insert (m_fds model) fdin (FdFile srcp (nat_to_word k + 0))) model) _
        obtain ⟨regsE, E17, E10, E1, E13, HmsE⟩ :=
          tgt_eof_to_close (regupd regsR 10 (Z_to_bv 64 0)) mem fdin fdout
            (by regupd_resolve; exact R1) (by regupd_resolve; rfl)
            (by regupd_resolve; exact R13) (by regupd_resolve; exact R14)
        apply tfo_msteps _ _ _ _ _ HmsE
        apply tfo_close_rec (fdv := fdin) (H17 := E17) (H10 := E10)
          (Hfd32 := fd32_lt31 fdin Hfin31)
        · exact fd_lookup_insert_eq _ _ _
        · exact Hh
        · exact Hlazy
        · obtain ⟨regsF, F17, F10, F1, HmsF⟩ :=
            tgt_close_to_close (regupd regsE 10 (Z_to_bv 64 0)) mem fdout
              (by regupd_resolve; exact E1) (by regupd_resolve; exact E13)
          apply tfo_msteps _ _ _ _ _ HmsF
          apply tfo_close_rec (fdv := fdout) (H17 := F17) (H10 := F10)
            (Hfd32 := fd32_lt31 fdout Hfout31)
          · model_simp
            rw [fd_lookup_remove_neq _ _ _ (Ne.symm Hneq),
              fd_lookup_insert_neq _ _ _ _ (Ne.symm Hneq)]
            exact Hfdout
          · exact Hh
          · exact Hlazy
          · apply tgt_loop_exit0
            · regupd_resolve; exact F1
            · change m_fs model = _
              rw [Hfs, Heq, List.take_length]
      · have HkltD : k < D.length := by omega
        have Hc1 : 1 ≤ chunk.length := by omega
        have HuLen : bv_unsigned (len_word chunk) = (chunk.length : Int) := u_len_word _ (by omega)
        obtain ⟨regsW, W17, W10, W11, W12, W1, W13, W14, W15, HmsW⟩ :=
          tgt_read_to_write (regupd regsR 10 (len_word chunk)) (write_to_mem mem tbuf chunk)
            fdin fdout (len_word chunk) (by regupd_resolve; rfl) (by omega) (by omega)
            (by regupd_resolve; exact R1) (by regupd_resolve; exact R13)
            (by regupd_resolve; exact R14) (by regupd_resolve; exact R15)
        apply tfo_msteps _ _ _ _ _ HmsW
        apply tfo_write_rec (p := dstp) (off := nat_to_word k) (data := D.take k)
          (bs := chunk) (buf := tbuf) (cnt := len_word chunk) (fdv := fdout)
          (H17 := W17) (H10 := W10) (H11 := W11) (H12 := W12)
          (Hfd32 := fd32_lt31 fdout Hfout31)
        · model_simp
          rw [fd_lookup_insert_neq _ _ _ _ (Ne.symm Hneq)]
          exact Hfdout
        · rw [wtn_len_word chunk (by omega)]
          apply rdn_write_to_mem
          rw [u_tbuf]; omega
        · rw [HuLen]; unfold rw_bytes_max; omega
        · change fs_lookup (m_fs model) dstp = _
          rw [Hfs]; exact fs_lookup_set_eq _ _ _
        · apply file_gap_in_range
          rw [u_ntw _ HkZ, List.length_take]
          unfold rw_bytes_max; omega
        · exact Or.inr (by omega)
        · exact Hh
        · exact Hlazy
        · obtain ⟨regsH, G1, G13, G14, G15, HmsH⟩ :=
            tgt_write_to_head (regupd regsW 10 (len_word chunk)) (write_to_mem mem tbuf chunk)
              fdin fdout (len_word chunk) (by regupd_resolve; rfl)
              (by regupd_resolve; exact W12) (by omega) (by omega)
              (by regupd_resolve; exact W1) (by regupd_resolve; exact W13)
              (by regupd_resolve; exact W14) (by regupd_resolve; exact W15)
          apply tfo_msteps _ _ _ _ _ HmsH
          apply IH (k + chunk.length) _ _ _ (by omega) (by omega) ⟨G1, G13, G14, G15⟩
          refine ⟨Hh, Hlazy, ?_, ?_, ?_⟩
          · model_simp
            rw [fd_lookup_insert_neq _ _ _ _ Hneq, fd_lookup_insert_eq, len_word_ntw, ntw_add]
          · model_simp
            rw [fd_lookup_insert_eq, len_word_ntw, ntw_add]
          · change fs_set (m_fs model) dstp (file_write (D.take k) (nat_to_word k) chunk) = _
            rw [Hfs, cp_fs_write_step fs0v dstp D k Hk HDlen]
            rw [Hclen]

section TargetProof
variable (inp : ProcInput)
variable (Hva : valid_argv inp.in_argv) (Hve : valid_envp inp.in_envp)
variable (asp : word) (arnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned asp)
variable (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)
variable (abrk amb : word)

include Hsp_lo in
theorem asp_lo_num : 0x7fff80000000 ≤ bv_unsigned asp := Hsp_lo
include Hsp_hi in
theorem asp_hi_num : bv_unsigned asp ≤ 0x800000000000 := Hsp_hi

def argcN : word := len_word inp.in_argv
def wmem : word → Option byte :=
  wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd

include Hva in
theorem u_argcN : bv_unsigned (argcN inp) = (inp.in_argv.length : Int) :=
  LinuxProcessSemantics.Common.ArgvEnv.u_argcN inp.in_argv Hva

include Hva Hve Hsp_hi in
theorem target_bsb_nw :
    bv_unsigned asp + ((build_stack_bytes target_phdrs asp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap arnd).length : Int) < 2^64 :=
  bsb_nw target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd Hva Hve Hsp_hi

def fmem : word → Option byte :=
  wbytes (wbytes (wmem inp asp arnd) (Z_to_bv 64 (bv_unsigned asp - 8))
    (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned asp - 16))
    (word_to_le_bytes 8 (Z_to_bv 64 0))

include Hsp_lo in
theorem rdn_fmem_above (a : word) (n : Nat)
    (Ha : bv_unsigned asp ≤ bv_unsigned a) (Hnw : bv_unsigned a + (n : Int) ≤ 2^64) :
    rdn target_segs (fmem inp asp arnd) a n = rdn target_segs (wmem inp asp arnd) a n := by
  have Hlo := asp_lo_num asp Hsp_lo
  unfold fmem
  repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; u_norm; omega) Hnw]

theorem rdn_wmem_stack (a : word) (n : Nat)
    (Ha : bv_unsigned asp ≤ bv_unsigned a) (Hnw : bv_unsigned a + (n : Int) ≤ 2^64) :
    rdn target_segs (wmem inp asp arnd) a n =
      rdn target_segs (stack_to_mem asp (entry_stack_image target_phdrs asp
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd)) a n :=
  rdn_wrap_stack_above target_segs _ _ _ _ _ _ _ _ _ Ha Hnw

include Hva Hve Hsp_hi in
theorem read_argc_w : rdn target_segs (wmem inp asp arnd) asp 8 = some (word_le8 (argcN inp)) := by
  have Hhi := asp_hi_num asp Hsp_hi
  rw [rdn_wmem_stack inp asp arnd asp 8 (by omega) (by omega)]
  exact read_argc _ _ _ _ _ _ _ _ (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

def src : path := inp.in_argv.getD 1 []
def dst : path := inp.in_argv.getD 2 []
def psrc : word := cat_argv_ptr asp inp.in_argv inp.in_envp 1
def pdst : word := cat_argv_ptr asp inp.in_argv inp.in_envp 2

variable (Hge3 : 3 ≤ inp.in_argv.length)
variable (Hsrc_nodot : openat_plain_name (src inp) = true)
variable (Hdst_nodot : openat_plain_name (dst inp) = true)

include Hva Hve Hsp_hi Hge3 in
theorem psrc_bounds :
    bv_unsigned asp ≤ bv_unsigned (psrc inp asp) ∧
    bv_unsigned (psrc inp asp) + ((src inp).length : Int) + 1 < 2^64 :=
  argv_ptr_bounds_at asp inp.in_argv inp.in_envp Hva Hve Hsp_hi 1 (by omega)

include Hva Hve Hsp_hi Hge3 in
theorem pdst_bounds :
    bv_unsigned asp ≤ bv_unsigned (pdst inp asp) ∧
    bv_unsigned (pdst inp asp) + ((dst inp).length : Int) + 1 < 2^64 :=
  argv_ptr_bounds_at asp inp.in_argv inp.in_envp Hva Hve Hsp_hi 2 (by omega)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_psrc_f :
    rdn target_segs (fmem inp asp arnd) (asp + nat_to_word (8 + 8 * 1)) 8 =
      some (word_le8 (psrc inp asp)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  rw [rdn_fmem_above inp asp arnd Hsp_lo _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_wmem_stack inp asp arnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k _ _ _ _ _ 1 _ _ _ (by omega)
    (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_pdst_f :
    rdn target_segs (fmem inp asp arnd) (asp + nat_to_word (8 + 8 * 2)) 8 =
      some (word_le8 (pdst inp asp)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  rw [rdn_fmem_above inp asp arnd Hsp_lo _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  rw [rdn_wmem_stack inp asp arnd _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_argv_ptr_k _ _ _ _ _ 2 _ _ _ (by omega)
    (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_src (Hlen : (src inp).length ≤ 4095) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (psrc inp asp) = CstrOk (src inp) := by
  obtain ⟨Hlo, Hhi⟩ := psrc_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz inp.in_argv 1 Hva (by omega)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp asp arnd _ _ (by omega) (by omega)]
    exact read_argv_cstr_k _ _ _ _ _ 1 _ _ _ (by omega)
      (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_src_toolong (Hlen : 4096 ≤ (src inp).length) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (psrc inp asp) = CstrTooLong := by
  obtain ⟨Hlo, Hhi⟩ := psrc_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn target_segs (fmem inp asp arnd) (psrc inp asp) ((src inp).take 4096)
  · rw [List.length_take]; omega
  · intro Hin
    exact valid_argv_str_nz inp.in_argv 1 Hva (by omega) (List.mem_of_mem_take Hin)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp asp arnd _ _ (by omega) (by omega)]
    exact read_argv_prefix_k _ _ _ _ _ 1 4096 _ _ _ (by omega) Hlen
      (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_dst (Hlen : (dst inp).length ≤ 4095) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (pdst inp asp) = CstrOk (dst inp) := by
  obtain ⟨Hlo, Hhi⟩ := pdst_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz inp.in_argv 2 Hva (by omega)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp asp arnd _ _ (by omega) (by omega)]
    exact read_argv_cstr_k _ _ _ _ _ 2 _ _ _ (by omega)
      (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_dst_toolong (Hlen : 4096 ≤ (dst inp).length) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (pdst inp asp) = CstrTooLong := by
  obtain ⟨Hlo, Hhi⟩ := pdst_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn target_segs (fmem inp asp arnd) (pdst inp asp) ((dst inp).take 4096)
  · rw [List.length_take]; omega
  · intro Hin
    exact valid_argv_str_nz inp.in_argv 2 Hva (by omega) (List.mem_of_mem_take Hin)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo _ _ (by omega) (by omega)]
    rw [rdn_wmem_stack inp asp arnd _ _ (by omega) (by omega)]
    exact read_argv_prefix_k _ _ _ _ _ 2 4096 _ _ _ (by omega) Hlen
      (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)

theorem target_err_exit (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (code : word) (fsv : Fs)
    (H11 : reg_get regs 11 = code) (H1 : reg_get regs 1 = (0x10011b0 : word))
    (Hc : bv_unsigned code < 256) (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x1001268 mem trom) model (fun o => o = (code, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781928) mem trom)
    5 [] [] [(1, ELit 0x10011b0), (11, EVar 32)] [code] [] R HR Hms
  · exact H1
  · exact H11
  · apply tfo_msteps _ _ _ _ _ Hms
    sym_pc_lit
    apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011b4 rfl)
    apply tfo_exit_rec
    · t_out HR
    · t_out HR
    · exact Hc
    · exact Hfs

theorem tgt_open1_err_tail (regs : bvmap 5 word) (e : Int) (mem : word → Option byte)
    (model : Model) (fsv : Fs) (He1 : 1 ≤ e) (He2 : e ≤ 4095)
    (H10 : reg_get regs 10 = errno_ret e) (H1 : reg_get regs 1 = (0x10011b0 : word))
    (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x10011dc mem trom) model
      (fun o => o = (Z_to_bv 64 3, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781788) mem trom)
    3 [true] [] [(10, EVar 32)] [errno_ret e] [] R HR Hms
  · apply c_lts_errno <;> omega
  · exact H10
  · apply tfo_msteps _ _ _ _ _ Hms
    sym_pc_lit
    apply target_err_exit
    · t_out HR
    · t_out HR
    · decide +kernel
    · exact Hfs

theorem tgt_open2_err_tail (regs : bvmap 5 word) (e : Int) (mem : word → Option byte)
    (model : Model) (fsv : Fs) (He1 : 1 ≤ e) (He2 : e ≤ 4095)
    (H10 : reg_get regs 10 = errno_ret e) (H1 : reg_get regs 1 = (0x10011b0 : word))
    (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x10011fc mem trom) model
      (fun o => o = (Z_to_bv 64 4, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781820) mem trom)
    2 [true] [] [(10, EVar 32)] [errno_ret e] [] R HR Hms
  · apply c_lts_errno <;> omega
  · exact H10
  · apply tfo_msteps _ _ _ _ _ Hms
    sym_pc_lit
    apply target_err_exit
    · t_out HR
    · t_out HR
    · decide +kernel
    · exact Hfs

theorem tgt_read_err_tail (regs : bvmap 5 word) (e : Int) (mem : word → Option byte)
    (model : Model) (fsv : Fs) (He1 : 1 ≤ e) (He2 : e ≤ 4095)
    (H10 : reg_get regs 10 = errno_ret e) (H1 : reg_get regs 1 = (0x10011b0 : word))
    (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x1001220 mem trom) model
      (fun o => o = (Z_to_bv 64 5, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781856) mem trom)
    3 [true] [] [(10, EVar 32)] [errno_ret e] [] R HR Hms
  · apply c_lts_errno <;> omega
  · exact H10
  · apply tfo_msteps _ _ _ _ _ Hms
    sym_pc_lit
    apply target_err_exit
    · t_out HR
    · t_out HR
    · decide +kernel
    · exact Hfs

set_option hygiene false in
local macro "cp_entry_sc" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first
    | (rw [show Z_to_bv 64 (bv_unsigned asp + 0) = asp by
         apply bv_eq_of_unsigned; u_norm; omega]
       refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
       repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
         (by rw [length_N_to_le_bytes]; u_norm; omega) (by omega)]
       exact read_argc_w inp Hva Hve asp arnd Hsp_hi)
    | (rw [show Z_to_bv 64 (bv_unsigned asp + 16) = asp + nat_to_word (8 + 8 * 1) by
         rw [word_add_nat]; congr 1 <;> omega]
       refine ⟨word_le8 (psrc inp asp), ?_, bytes_le_n_to_le_8 _⟩
       rw [← rdn_fmem_above inp asp arnd Hsp_lo _ _
         (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
       exact read_psrc_f inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3)
    | (rw [Bool.not_eq_false', bv_ltu_Z, decide_eq_true_eq]
       change (2 : Int) < bv_unsigned (argcN inp)
       rw [u_argcN inp Hva]; omega)
    | (rw [Bool.not_eq_true', bv_ltu_Z, decide_eq_false_iff_not]
       change ¬ (2 : Int) < bv_unsigned (argcN inp)
       rw [u_argcN inp Hva]; omega)
    | solve_store_ok
    | omega))

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_to_open1 :
    ∃ regs1, reg_get regs1 1 = (0x10011b0 : word) ∧
      reg_get regs1 15 = Z_to_bv 64 (bv_unsigned asp + 8) ∧
      bv_unsigned (getr regs1 17) = 56 ∧ reg_get regs1 10 = AT_FDCWD ∧
      reg_get regs1 11 = psrc inp asp ∧ reg_get regs1 12 = Z_to_bv 64 0 ∧
      msteps target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs1 0x10011d8 (fmem inp asp arnd) trom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
      (Z_to_bv 64 16781712) (wmem inp asp arnd) trom)
    20 [false] [EVar 33, EVar 34] [(2, EVar 32), (1, ELit 0), (8, ELit 0)]
    [asp] [argcN inp, psrc inp asp] R HR Hms
  · cp_entry_sc
  · getr_resolve; rfl
  · getr_resolve; rfl
  · getr_resolve; rfl
  · refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · rw [init_mkst]
      exact Hms

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_lt3 (Hlt3 : inp.in_argv.length < 3) :
    to_wexit target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) [] (Z_to_bv 64 2) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  rw [init_mkst]
  norm_pc
  sym_block target_segs 20 [true] [] [(2, EVar 32), (1, ELit 0), (8, ELit 0)]
    [asp] [argcN inp] R HR
  · cp_entry_sc
  · getr_resolve; rfl
  · getr_resolve; rfl
  · getr_resolve; rfl
  · apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011b4 rfl)
    apply tw_exit_coden
    · t_out HR
    · t_out HR
    · decide +kernel

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem tgt_to_open2 (regs : bvmap 5 word) (fd : word)
    (H10 : reg_get regs 10 = fd) (Hlt : bv_unsigned fd < 2^31)
    (H15 : reg_get regs 15 = Z_to_bv 64 (bv_unsigned asp + 8))
    (H1 : reg_get regs 1 = (0x10011b0 : word)) :
    ∃ regs2, bv_unsigned (getr regs2 17) = 56 ∧ reg_get regs2 10 = AT_FDCWD ∧
      reg_get regs2 11 = pdst inp asp ∧ reg_get regs2 12 = Z_to_bv 64 577 ∧
      reg_get regs2 14 = fd ∧ reg_get regs2 1 = (0x10011b0 : word) ∧
      msteps target_segs (mkst regs 0x10011dc (fmem inp asp arnd) trom)
        { ms_regs := regs2, ms_fregs := bvmap_empty, ms_pc_val := 0x10011f8,
          ms_svc_pending := some (getr regs2 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
          ms_mem := fmem inp asp arnd, ms_rom := trom } := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781788) (fmem inp asp arnd) trom)
    8 [false] [EVar 34] [(10, EVar 32), (15, EVar 33)]
    [fd, Z_to_bv 64 (bv_unsigned asp + 8)] [pdst inp asp] R HR Hms
  · repeat' apply And.intro
    all_goals first
    | (rw [show Z_to_bv 64 (bv_unsigned asp + 24) = asp + nat_to_word (8 + 8 * 2) by
          rw [word_add_nat]; congr 1 <;> omega]
       exact ⟨word_le8 (pdst inp asp), read_pdst_f inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3,
         bytes_le_n_to_le_8 _⟩)
    | (apply c_lts_pos_0; omega)
    | omega
  · exact H10
  · exact H15
  · refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR
    · apply msteps_trans _ _ _ _ Hms
      sym_pc_lit
      exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011f8 rfl)
        (msteps.mst_refl _)

theorem tgt_open2_to_loop (regs : bvmap 5 word) (fd fd2 : word)
    (H10 : reg_get regs 10 = fd2) (Hlt2 : bv_unsigned fd2 < 2^31)
    (H14 : reg_get regs 14 = fd) (H1 : reg_get regs 1 = (0x10011b0 : word)) :
    ∃ regsH, reg_get regsH 1 = (0x10011b0 : word) ∧ reg_get regsH 13 = fd2 ∧
      reg_get regsH 14 = fd ∧ reg_get regsH 15 = tbuf ∧
      msteps target_segs (mkst regs 0x10011fc (fmem inp asp arnd) trom)
        (mkst regsH 0x100120c (fmem inp asp arnd) trom) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781820) (fmem inp asp arnd) trom)
    4 [false] [] [(10, EVar 32)] [fd2] [] R HR Hms
  · apply c_lts_pos_0; omega
  · exact H10
  · refine ⟨R, ?_, ?_, ?_, ?_, Hms⟩
    · t_out HR
    · t_out HR
    · t_out HR
    · t_out HR

theorem tgt_openat_enoent_empty (ms : machine_state) (model : Model) (x8 : word)
    (p : path) (U : word × Fs → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 56)
    (Hfl : modeled_open_flags (ms_gpr ms 2) = true) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = true) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout target_segs (advance_past_svc (apply_effect ms
      (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] [])))) model U) :
    to_fout target_segs ms model U := by
  have Hchk : ∀ eff, check_syscall (sys_input target_segs ms x8) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [] := by
    intro eff
    rw [check_syscall_56 target_segs ms x8 eff model Hno]
    simp only [check_openat, Hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      check_openat_body, in_mem_si, Hpath, Hpe]
    exact check_copyins_after_ret_only _ _ _ _ _
  have Hagree : lookups_agree_at (bv_unsigned (sys_input target_segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  refine tfo_sys_det target_segs ms model x8
    (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] [])) model U
    Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
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

theorem tgt_open_empty_rec (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (p : path) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (Hfl : modeled_open_flags (reg_get regs 12) = true) (H10 : reg_get regs 10 = AT_FDCWD)
    (Hpath : read_cstr (mrb target_segs mem) (reg_get regs 11) = CstrOk p)
    (Hpe : path_eqb p [] = true) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout target_segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
      mem (seg_rom target_segs)) model U) :
    to_fout target_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := seg_rom target_segs } model U := by
  let ms : machine_state :=
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom target_segs }
  apply tgt_openat_enoent_empty ms model (getr regs 17) p U rfl H17 Hfl H10 Hpath Hpe Hh Hlazy
  simpa only [ms, adv_eff_ret_copyins] using Hcont

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem target_absent (Hlen : (src inp).length ≤ 4095)
    (Hnone : fs_lookup inp.in_fs (src inp) = none) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (cp_outcomes inp.in_fs (src inp) (dst inp)) := by
  apply tfo_equiv (U := fun o => o = (Z_to_bv 64 3, inp.in_fs))
  · obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
      target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
    apply tfo_msteps _ _ _ _ _ Hms
    apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
    apply tfo_open_enoent_rec (p := src inp)
    · exact H17
    · exact H10
    · exact H12
    · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen
    · exact Hsrc_nodot
    · exact Hnone
    · rfl
    · rfl
    · apply tgt_open1_err_tail (e := ENOENT)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact H1
      · rfl
  · intro o
    simp only [cp_outcomes, Hnone]

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_empty (Hlen : (src inp).length ≤ 4095)
    (Hse : path_eqb (src inp) [] = true) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tgt_open_empty_rec (p := src inp)
  · exact H17
  · rw [H12]; decide +kernel
  · exact H10
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen
  · exact Hse
  · rfl
  · rfl
  · apply tgt_open1_err_tail (e := ENOENT)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_toolong (Hlen : 4096 ≤ (src inp).length) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_toolong_rec
  · exact H17
  · rw [H12]; decide +kernel
  · rw [H11]; exact target_cstr_src_toolong inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen
  · rfl
  · rfl
  · apply tgt_open1_err_tail (e := ENAMETOOLONG)
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem target_present_dst_toolong (d0 : List byte)
    (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : 4096 ≤ (dst inp).length) (Hsne : path_eqb (src inp) [] = false) (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_rec (p := src inp) (d := d0)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsrc_nodot
  · exact Hsome
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    apply tfo_open_toolong_rec
    · exact K17
    · rw [K12]; decide +kernel
    · rw [K11]; exact target_cstr_dst_toolong inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
    · rfl
    · rfl
    · apply tgt_open2_err_tail (e := ENAMETOOLONG)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
  · intro o
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem target_present_dst_empty (d0 : List byte)
    (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : (dst inp).length ≤ 4095) (Hsne : path_eqb (src inp) [] = false)
    (Hde : path_eqb (dst inp) [] = true) (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_rec (p := src inp) (d := d0)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsrc_nodot
  · exact Hsome
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    apply tgt_open_empty_rec (p := dst inp)
    · exact K17
    · rw [K12]; decide +kernel
    · exact K10
    · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
    · exact Hde
    · rfl
    · rfl
    · apply tgt_open2_err_tail (e := ENOENT)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
  · intro o
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot in
theorem target_present_dst_dot (d0 : List byte)
    (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : (dst inp).length ≤ 4095) (Hsne : path_eqb (src inp) [] = false)
    (Hde : path_eqb (dst inp) dot_path = true) (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  have Hdne : path_eqb (dst inp) [] = false := by
    rw [(path_eqb_eq _ _).mp Hde]; decide +kernel
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_rec (p := src inp) (d := d0)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsrc_nodot
  · exact Hsome
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    apply tfo_open_wr_dot_rec (p := dst inp)
    · exact K17
    · exact K10
    · rw [K12]; decide +kernel
    · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
    · exact Hdne
    · exact Hde
    · rfl
    · rfl
    · apply tgt_open2_err_tail (e := EISDIR)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
  · intro o
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot_dst_toolong (Hsdot : path_eqb (src inp) dot_path = true)
    (Hlen2 : 4096 ≤ (dst inp).length) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  have Hs : src inp = dot_path := (path_eqb_eq _ _).mp Hsdot
  have Hlen1 : (src inp).length ≤ 4095 := by rw [Hs]; decide +kernel
  have Hsne : path_eqb (src inp) [] = false := by rw [Hs]; decide +kernel
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_dot_rec (p := src inp)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsdot
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    apply tfo_open_toolong_rec
    · exact K17
    · rw [K12]; decide +kernel
    · rw [K11]; exact target_cstr_dst_toolong inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
    · rfl
    · rfl
    · apply tgt_open2_err_tail (e := ENAMETOOLONG)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
  · intro o
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot_dstempty
    (Hlen2 : (dst inp).length ≤ 4095) (Hsdot : path_eqb (src inp) dot_path = true)
    (Hde : path_eqb (dst inp) [] = true) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  have Hs : src inp = dot_path := (path_eqb_eq _ _).mp Hsdot
  have Hlen1 : (src inp).length ≤ 4095 := by rw [Hs]; decide +kernel
  have Hsne : path_eqb (src inp) [] = false := by rw [Hs]; decide +kernel
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_dot_rec (p := src inp)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsdot
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    apply tgt_open_empty_rec (p := dst inp)
    · exact K17
    · rw [K12]; decide +kernel
    · exact K10
    · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
    · exact Hde
    · rfl
    · rfl
    · apply tgt_open2_err_tail (e := ENOENT)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
  · intro o
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot_dstdot
    (Hlen2 : (dst inp).length ≤ 4095) (Hsdot : path_eqb (src inp) dot_path = true)
    (Hde : path_eqb (dst inp) dot_path = true) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  have Hs : src inp = dot_path := (path_eqb_eq _ _).mp Hsdot
  have Hlen1 : (src inp).length ≤ 4095 := by rw [Hs]; decide +kernel
  have Hsne : path_eqb (src inp) [] = false := by rw [Hs]; decide +kernel
  have Hdne : path_eqb (dst inp) [] = false := by
    rw [(path_eqb_eq _ _).mp Hde]; decide +kernel
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_dot_rec (p := src inp)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsdot
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    apply tfo_open_wr_dot_rec (p := dst inp)
    · exact K17
    · exact K10
    · rw [K12]; decide +kernel
    · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
    · exact Hdne
    · exact Hde
    · rfl
    · rfl
    · apply tgt_open2_err_tail (e := EISDIR)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
  · intro o
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨fd, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot in
theorem target_present (d0 : List byte)
    (Hlen1 : (src inp).length ≤ 4095) (Hlen2 : (dst inp).length ≤ 4095)
    (Hsne : path_eqb (src inp) [] = false) (Hdne : path_eqb (dst inp) [] = false)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0)
    (Hrep : ((cp_read_data inp.in_fs (src inp) (dst inp)).length : Int) < 2^64) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (cp_outcomes inp.in_fs (src inp) (dst inp)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_rec (p := src inp) (d := d0)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs) ∨
      (fs_under inp.in_fs (dst inp) = false ∧ o = (Z_to_bv 64 0, cp_final_fs inp.in_fs (src inp) (dst inp))))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsrc_nodot
  · exact Hsome
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    cases Hun : fs_under inp.in_fs (dst inp) with
    | true =>
      apply tfo_open_wr_isdir_rec (p := dst inp)
      · exact K17
      · exact K10
      · exact K12
      · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
      · exact Hdne
      · exact Hdst_nodot
      · exact Hun
      · rfl
      · rfl
      · apply tfo_equiv (U := fun o => o = (Z_to_bv 64 4, inp.in_fs))
        · apply tgt_open2_err_tail (e := EISDIR)
          · decide +kernel
          · decide +kernel
          · regupd_resolve; rfl
          · regupd_resolve; exact K1
          · rfl
        · intro o; simp only [Bool.true_eq_false, false_and, or_false]
    | false =>
      apply tfo_open_wr_rec (p := dst inp)
        (Te := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
        (Ts := fun _ o => o = (Z_to_bv 64 0, cp_final_fs inp.in_fs (src inp) (dst inp)))
      · exact K17
      · exact K10
      · exact K12
      · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
      · exact Hdne
      · exact Hdst_nodot
      · exact Hun
      · rfl
      · rfl
      · intro e HIn
        obtain ⟨He1, He2⟩ := openat_errno_range e HIn
        apply tgt_open2_err_tail (e := e)
        · exact He1
        · exact He2
        · regupd_resolve; rfl
        · regupd_resolve; exact K1
        · rfl
      · intro fd2 Hlk2 Hfd2
        have Hlt2 : bv_unsigned fd2 < 2^31 := by rw [Hfd2]; exact alloc_fd_lt_2_31 _
        have Hne : fd ≠ fd2 := by
          intro Heq
          rw [← Heq] at Hlk2
          change fd_lookup (fd_insert _ fd _) fd = none at Hlk2
          rw [fd_lookup_insert_eq] at Hlk2
          cases Hlk2
        obtain ⟨regsH, G1, G13, G14, G15, HmsH⟩ :=
          tgt_open2_to_loop inp asp arnd (regupd regs2 10 fd2) fd fd2
            (by regupd_resolve; rfl) Hlt2 (by regupd_resolve; exact K14) (by regupd_resolve; exact K1)
        apply tfo_msteps _ _ _ _ _ HmsH
        unfold cp_final_fs
        apply target_loop inp.in_fs (src inp) (dst inp) (cp_read_data inp.in_fs (src inp) (dst inp))
          fd fd2 (cp_read_data_lookup _ _ _ _ Hsome) Hne Hlt Hlt2 Hrep
          ((cp_read_data inp.in_fs (src inp) (dst inp)).length + 1) 0
          _ _ _ (by omega) (by omega) ⟨G1, G13, G14, G15⟩
        refine ⟨rfl, rfl, ?_, ?_, rfl⟩
        · model_simp
          rw [fd_lookup_insert_neq _ _ _ _ Hne, fd_lookup_insert_eq]
          rfl
        · exact fd_lookup_insert_eq _ _ _
      · intro o
        constructor
        · intro H
          rcases H with H | ⟨_, H⟩
          · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
          · have Hfd3 : fd = Z_to_bv 64 3 := Hfd
            refine Or.inr ⟨Z_to_bv 64 4, ?_, ?_, H⟩
            · rw [Hfd3]; rfl
            · rw [Hfd3]; rfl
        · intro H
          rcases H with ⟨e, _, H⟩ | ⟨w, _, _, H⟩
          · exact Or.inl H
          · exact Or.inr ⟨rfl, H⟩
  · intro o
    simp only [cp_outcomes, Hsome]
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨w, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot_normal (Hlen2 : (dst inp).length ≤ 4095)
    (Hsdot : path_eqb (src inp) dot_path = true) (Hdne : path_eqb (dst inp) [] = false)
    (Hddot : openat_plain_name (dst inp) = true) :
    to_fout target_segs (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs) ∨
        (fs_under inp.in_fs (dst inp) = false ∧ o = (Z_to_bv 64 5, fs_set inp.in_fs (dst inp) []))) := by
  have Hs : src inp = dot_path := (path_eqb_eq _ _).mp Hsdot
  have Hlen1 : (src inp).length ≤ 4095 := by rw [Hs]; decide +kernel
  have Hsne : path_eqb (src inp) [] = false := by rw [Hs]; decide +kernel
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps _ _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl)
  apply tfo_open_rd_dot_rec (p := src inp)
    (Te := fun _ o => o = (Z_to_bv 64 3, inp.in_fs))
    (Ts := fun _ o => o = (Z_to_bv 64 4, inp.in_fs) ∨
      (fs_under inp.in_fs (dst inp) = false ∧ o = (Z_to_bv 64 5, fs_set inp.in_fs (dst inp) [])))
  · exact H17
  · exact H10
  · exact H12
  · rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen1
  · exact Hsne
  · exact Hsdot
  · rfl
  · rfl
  · intro e HIn
    obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    apply tgt_open1_err_tail (e := e)
    · exact He1
    · exact He2
    · regupd_resolve; rfl
    · regupd_resolve; exact H1
    · rfl
  · intro fd Hlk Hfd
    have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    apply tfo_msteps _ _ _ _ _ Hms2
    cases Hun : fs_under inp.in_fs (dst inp) with
    | true =>
      apply tfo_open_wr_isdir_rec (p := dst inp)
      · exact K17
      · exact K10
      · exact K12
      · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
      · exact Hdne
      · exact Hddot
      · exact Hun
      · rfl
      · rfl
      · apply tfo_equiv (U := fun o => o = (Z_to_bv 64 4, inp.in_fs))
        · apply tgt_open2_err_tail (e := EISDIR)
          · decide +kernel
          · decide +kernel
          · regupd_resolve; rfl
          · regupd_resolve; exact K1
          · rfl
        · intro o; simp only [Bool.true_eq_false, false_and, or_false]
    | false =>
      apply tfo_open_wr_rec (p := dst inp)
        (Te := fun _ o => o = (Z_to_bv 64 4, inp.in_fs))
        (Ts := fun _ o => o = (Z_to_bv 64 5, fs_set inp.in_fs (dst inp) []))
      · exact K17
      · exact K10
      · exact K12
      · rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2
      · exact Hdne
      · exact Hddot
      · exact Hun
      · rfl
      · rfl
      · intro e HIn
        obtain ⟨He1, He2⟩ := openat_errno_range e HIn
        apply tgt_open2_err_tail (e := e)
        · exact He1
        · exact He2
        · regupd_resolve; rfl
        · regupd_resolve; exact K1
        · rfl
      · intro fd2 Hlk2 Hfd2
        have Hlt2 : bv_unsigned fd2 < 2^31 := by rw [Hfd2]; exact alloc_fd_lt_2_31 _
        have Hne : fd ≠ fd2 := by
          intro Heq
          rw [← Heq] at Hlk2
          change fd_lookup (fd_insert _ fd _) fd = none at Hlk2
          rw [fd_lookup_insert_eq] at Hlk2
          cases Hlk2
        obtain ⟨regsH, G1, G13, G14, G15, HmsH⟩ :=
          tgt_open2_to_loop inp asp arnd (regupd regs2 10 fd2) fd fd2
            (by regupd_resolve; rfl) Hlt2 (by regupd_resolve; exact K14) (by regupd_resolve; exact K1)
        apply tfo_msteps _ _ _ _ _ HmsH
        obtain ⟨regsR, R17, R10, R11, R12, R1, R13, R14, R15, HmsR⟩ :=
          tgt_head_to_read regsH (fmem inp asp arnd) fd fd2 G1 G13 G14 G15
        apply tfo_msteps _ _ _ _ _ HmsR
        apply tfo_read_dir_rec
        · exact R17
        · rw [R10]; model_simp
          rw [fd_lookup_insert_neq _ _ _ _ Hne, fd_lookup_insert_eq]
        · rw [R10]; exact fd32_lt31 fd Hlt
        · rw [R11, R12]; decide +kernel
        · rfl
        · rfl
        · apply tgt_read_err_tail (e := EISDIR)
          · decide +kernel
          · decide +kernel
          · regupd_resolve; rfl
          · regupd_resolve; exact R1
          · rfl
      · intro o
        constructor
        · intro H
          rcases H with H | ⟨_, H⟩
          · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
          · have Hfd3 : fd = Z_to_bv 64 3 := Hfd
            refine Or.inr ⟨Z_to_bv 64 4, ?_, ?_, H⟩
            · rw [Hfd3]; rfl
            · rw [Hfd3]; rfl
        · intro H
          rcases H with ⟨e, _, H⟩ | ⟨w, _, _, H⟩
          · exact Or.inl H
          · exact Or.inr ⟨rfl, H⟩
  · intro o
    constructor
    · intro H
      rcases H with H | H
      · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
      · exact Or.inr ⟨Z_to_bv 64 3, rfl, by rfl, H⟩
    · intro H
      rcases H with ⟨e, _, H⟩ | ⟨w, _, _, H⟩
      · exact Or.inl H
      · exact Or.inr H

def model0 : Model := init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp

def tX : word × Fs → Prop := fun o =>
  o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)

theorem huge_chunk (d0 : List byte) (Hbig : (2^64 : Int) ≤ (d0.length : Int)) (off : word) :
    1 ≤ ((file_read d0 off (Z_to_bv 64 1024)).length : Int) ∧
    ((file_read d0 off (Z_to_bv 64 1024)).length : Int) ≤ 1024 := by
  rw [length_file_read, wtn_1024]
  have Hr := u64_range off
  have Hoff : (word_to_nat off : Int) = bv_unsigned off := rfl
  omega

def tO1pins (regs : bvmap 5 word) : Prop :=
  bv_unsigned (getr regs 17) = 56 ∧ reg_get regs 10 = AT_FDCWD ∧
  reg_get regs 11 = psrc inp asp ∧ reg_get regs 12 = Z_to_bv 64 0 ∧
  reg_get regs 15 = Z_to_bv 64 (bv_unsigned asp + 8) ∧ reg_get regs 1 = (0x10011b0 : word)

def o1rec (regs : bvmap 5 word) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := 0x10011d8,
    ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem := fmem inp asp arnd, ms_rom := trom }

def model1 (fd : word) : Model :=
  with_fds (fd_insert (m_fds (model0 inp asp abrk amb)) fd (FdFile (src inp) (Z_to_bv 64 0)))
    (model0 inp asp abrk amb)

def tO2pins (regs : bvmap 5 word) (fd : word) : Prop :=
  bv_unsigned (getr regs 17) = 56 ∧ reg_get regs 10 = AT_FDCWD ∧
  reg_get regs 11 = pdst inp asp ∧ reg_get regs 12 = Z_to_bv 64 577 ∧
  reg_get regs 14 = fd ∧ reg_get regs 1 = (0x10011b0 : word)

def o2rec (regs : bvmap 5 word) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := 0x10011f8,
    ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem := fmem inp asp arnd, ms_rom := trom }

def tRpins (regs : bvmap 5 word) (fdin fdout : word) : Prop :=
  bv_unsigned (getr regs 17) = 63 ∧ reg_get regs 10 = fdin ∧ reg_get regs 11 = tbuf ∧
  reg_get regs 12 = Z_to_bv 64 1024 ∧ reg_get regs 1 = (0x10011b0 : word) ∧
  reg_get regs 13 = fdout ∧ reg_get regs 14 = fdin ∧ reg_get regs 15 = tbuf

def rdrec (regs : bvmap 5 word) (mem : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := 0x100121c,
    ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem := mem, ms_rom := trom }

def tHM (fdin fdout : word) (model : Model) : Prop :=
  m_halted model = none ∧ m_vm_lazy model = [] ∧ ∃ (off : word) (data : List byte),
    fd_lookup (m_fds model) fdin = some (FdFile (src inp) off) ∧
    fd_lookup (m_fds model) fdout = some (FdFileW (dst inp) off) ∧
    m_fs model = fs_set inp.in_fs (dst inp) data ∧ bv_unsigned off ≤ (data.length : Int)

def tAnchor (c : config) : Prop :=
  ∃ fdin fdout regs mem model, fdin ≠ fdout ∧ fd32 fdin = fdin ∧ fd32 fdout = fdout ∧
    tRpins regs fdin fdout ∧ tHM inp fdin fdout model ∧ c = mkCfg (rdrec regs mem) model

def tHI (c : config) : Prop :=
  (∃ ms regs1, tO1pins inp asp regs1 ∧ msteps target_segs ms (o1rec inp asp arnd regs1) ∧
    c = mkCfg ms (model0 inp asp abrk amb)) ∨
  (∃ ms regs2 fd, fd_lookup (m_fds (model0 inp asp abrk amb)) fd = none ∧
    bv_unsigned fd < 2^31 ∧ tO2pins inp asp regs2 fd ∧
    msteps target_segs ms (o2rec inp asp arnd regs2) ∧ c = mkCfg ms (model1 inp asp abrk amb fd)) ∨
  (∃ c'', dsil target_segs c c'' ∧ tAnchor inp c'')

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem tgt_huge_start :
    tHI inp asp arnd abrk amb
      (mkCfg (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) (model0 inp asp abrk amb)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  refine Or.inl ⟨_, regs1, ⟨H17, H10, H11, H12, H15, H1⟩, ?_, rfl⟩
  apply msteps_trans _ _ _ _ Hms
  exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl) (msteps.mst_refl _)

variable (d0 : List byte)
variable (Hplen1 : (src inp).length ≤ 4095) (Hplen2 : (dst inp).length ≤ 4095)
variable (Hsd : src inp ≠ dst inp) (Hsome0 : fs_lookup inp.in_fs (src inp) = some d0)
variable (Hbig : (2^64 : Int) ≤ (d0.length : Int))
variable (Hsne0 : path_eqb (src inp) [] = false) (Hdne0 : path_eqb (dst inp) [] = false)

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hplen1 Hsome0 Hsne0 in
theorem tgt_huge_open1_anchor (regs1 : bvmap 5 word) (evs : List event) (st : step_to)
    (Hpins : tO1pins inp asp regs1)
    (Hss : sstep target_segs (mkCfg (o1rec inp asp arnd regs1) (model0 inp asp abrk amb)) evs st) :
    fdiv_resp target_segs (tHI inp asp arnd abrk amb) (tX inp) evs st := by
  obtain ⟨H17, H10, H11, H12, H15, H1⟩ := Hpins
  obtain ⟨Hne, Herr, Hok, Hinv⟩ := open_rd_branches target_segs (o1rec inp asp arnd regs1)
    (getr regs1 17) (model0 inp asp abrk amb) (src inp) d0 H17 H10
    (by change read_cstr (mrb target_segs (fmem inp asp arnd)) (reg_get regs1 11) = _
        rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hplen1)
    Hsne0 (by change bv_unsigned (bv_and (reg_get regs1 12) _) = 0; rw [H12]; decide +kernel)
    Hsrc_nodot Hsome0
  have Hshape : ∀ eff m' evs',
      syscall_spec (sys_input target_segs (o1rec inp asp arnd regs1) (getr regs1 17))
        (model0 inp asp abrk amb) (Ok eff m' evs') →
      evs' = [] ∧ m_halted m' = none ∧ m_vm_lazy m' = [] := by
    intro eff m' evs' Hs
    obtain ⟨Hevs, H⟩ := Hinv eff m' evs' Hs
    rcases H with ⟨e, _, _, rfl⟩ | ⟨fd, _, _, _, rfl⟩ <;> exact ⟨Hevs, rfl, rfl⟩
  obtain ⟨eff, m2, Hspec, rfl, rfl⟩ := sstep_fsys_inv target_segs
    (o1rec inp asp arnd regs1) (model0 inp asp abrk amb) (getr regs1 17)
    evs st rfl rfl rfl Hne Hshape Hss
  refine ⟨rfl, _, rfl, ?_⟩
  obtain ⟨_, H⟩ := Hinv eff m2 [] Hspec
  rcases H with ⟨e, HIn, rfl, rfl⟩ | ⟨fd, Hlk, Hfd, rfl, rfl⟩
  · obtain ⟨He1, He2⟩ := openat_errno_range e HIn
    refine Or.inr ⟨rfl, rfl, (fun o => o = (Z_to_bv 64 3, inp.in_fs)), ?_, ?_⟩
    · dsimp only [config.cfg_ms, config.cfg_model, o1rec]
      rw [adv_eff_ret_copyins]
      apply tgt_open1_err_tail (e := e) (He1 := He1) (He2 := He2)
      · regupd_resolve; rfl
      · regupd_resolve; exact H1
      · rfl
    · intro o Ho; exact Or.inl Ho
  · have Hlt : bv_unsigned fd < 2^31 := by rw [Hfd]; exact alloc_fd_lt_2_31 _
    obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 (regupd regs1 10 fd) fd
        (by regupd_resolve; rfl) Hlt (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    refine Or.inl (Or.inr (Or.inl ⟨_, regs2, fd, Hlk, Hlt,
      ⟨K17, K10, K11, K12, K14, K1⟩, Hms2, ?_⟩))
    simp only [o1rec, adv_eff_ret_copyins]
    rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 Hdst_nodot Hplen2 Hdne0 in
theorem tgt_huge_open2_anchor (regs2 : bvmap 5 word) (fd : word)
    (evs : List event) (st : step_to)
    (Hlk : fd_lookup (m_fds (model0 inp asp abrk amb)) fd = none)
    (Hlt : bv_unsigned fd < 2^31) (Hpins : tO2pins inp asp regs2 fd)
    (Hss : sstep target_segs (mkCfg (o2rec inp asp arnd regs2) (model1 inp asp abrk amb fd)) evs st) :
    fdiv_resp target_segs (tHI inp asp arnd abrk amb) (tX inp) evs st := by
  obtain ⟨K17, K10, K11, K12, K14, K1⟩ := Hpins
  have Hpath : read_cstr (ms_read_byte (o2rec inp asp arnd regs2))
      (ms_gpr (o2rec inp asp arnd regs2) 1) = CstrOk (dst inp) := by
    change read_cstr (mrb target_segs (fmem inp asp arnd)) (reg_get regs2 11) = _
    rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hplen2
  have Hfl : bv_unsigned (bv_and (ms_gpr (o2rec inp asp arnd regs2) 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags := by
    change bv_unsigned (bv_and (reg_get regs2 12) _) = _
    rw [K12]; decide +kernel
  cases Hun : fs_under inp.in_fs (dst inp) with
  | true =>
    obtain ⟨Hok, Huniq, Hne⟩ := open_wr_isdir target_segs (o2rec inp asp arnd regs2)
      (getr regs2 17) (model1 inp asp abrk amb fd) (dst inp) K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
    have Hshape : ∀ eff m' evs',
        syscall_spec (sys_input target_segs (o2rec inp asp arnd regs2) (getr regs2 17))
          (model1 inp asp abrk amb fd) (Ok eff m' evs') →
        evs' = [] ∧ m_halted m' = none ∧ m_vm_lazy m' = [] := by
      intro eff m' evs' Hs
      obtain ⟨_, rfl, rfl⟩ := Huniq eff m' evs' Hs
      exact ⟨rfl, rfl, rfl⟩
    obtain ⟨eff, m2, Hspec, rfl, rfl⟩ := sstep_fsys_inv target_segs
      (o2rec inp asp arnd regs2) (model1 inp asp abrk amb fd) (getr regs2 17)
      evs st rfl rfl rfl Hne Hshape Hss
    obtain ⟨rfl, rfl, _⟩ := Huniq eff m2 [] Hspec
    refine ⟨rfl, _, rfl, Or.inr ⟨rfl, rfl, (fun o => o = (Z_to_bv 64 4, inp.in_fs)), ?_, ?_⟩⟩
    · dsimp only [config.cfg_ms, config.cfg_model, o2rec]
      rw [adv_eff_ret_copyins]
      apply tgt_open2_err_tail (e := EISDIR)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
    · intro o Ho; exact Or.inr Ho
  | false =>
    obtain ⟨Hne, Herr, Hok, Hinv⟩ := open_wr_branches target_segs (o2rec inp asp arnd regs2)
      (getr regs2 17) (model1 inp asp abrk amb fd) (dst inp) K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
    have Hshape : ∀ eff m' evs',
        syscall_spec (sys_input target_segs (o2rec inp asp arnd regs2) (getr regs2 17))
          (model1 inp asp abrk amb fd) (Ok eff m' evs') →
        evs' = [] ∧ m_halted m' = none ∧ m_vm_lazy m' = [] := by
      intro eff m' evs' Hs
      obtain ⟨Hevs, H⟩ := Hinv eff m' evs' Hs
      rcases H with ⟨e, _, _, rfl⟩ | ⟨fd2, _, _, _, rfl⟩ <;> exact ⟨Hevs, rfl, rfl⟩
    obtain ⟨eff, m2, Hspec, rfl, rfl⟩ := sstep_fsys_inv target_segs
      (o2rec inp asp arnd regs2) (model1 inp asp abrk amb fd) (getr regs2 17)
      evs st rfl rfl rfl Hne Hshape Hss
    refine ⟨rfl, _, rfl, ?_⟩
    obtain ⟨_, H⟩ := Hinv eff m2 [] Hspec
    rcases H with ⟨e, HIn, rfl, rfl⟩ | ⟨fd2, Hlk2, Hfd2, rfl, rfl⟩
    · obtain ⟨He1, He2⟩ := openat_errno_range e HIn
      refine Or.inr ⟨rfl, rfl, (fun o => o = (Z_to_bv 64 4, inp.in_fs)), ?_, ?_⟩
      · dsimp only [config.cfg_ms, config.cfg_model, o2rec]
        rw [adv_eff_ret_copyins]
        apply tgt_open2_err_tail (e := e)
        · exact He1
        · exact He2
        · regupd_resolve; rfl
        · regupd_resolve; exact K1
        · rfl
      · intro o Ho; exact Or.inr Ho
    · have Hlt2 : bv_unsigned fd2 < 2^31 := by rw [Hfd2]; exact alloc_fd_lt_2_31 _
      have Hnefd : fd ≠ fd2 := by
        intro Heq
        rw [← Heq] at Hlk2
        change fd_lookup (fd_insert _ fd _) fd = none at Hlk2
        rw [fd_lookup_insert_eq] at Hlk2
        cases Hlk2
      obtain ⟨regsH, G1, G13, G14, G15, HmsH⟩ :=
        tgt_open2_to_loop inp asp arnd (regupd regs2 10 fd2) fd fd2
          (by regupd_resolve; rfl) Hlt2 (by regupd_resolve; exact K14) (by regupd_resolve; exact K1)
      obtain ⟨regsR, R17, R10, R11, R12, R1, R13, R14, R15, HmsR⟩ :=
        tgt_head_to_read regsH (fmem inp asp arnd) fd fd2 G1 G13 G14 G15
      let model2 := with_fds
        (fd_insert (m_fds (model1 inp asp abrk amb fd)) fd2 (FdFileW (dst inp) (Z_to_bv 64 0)))
        (with_fs (fs_set (m_fs (model1 inp asp abrk amb fd)) (dst inp) []) (model1 inp asp abrk amb fd))
      refine Or.inl (Or.inr (Or.inr ⟨mkCfg (rdrec regsR (fmem inp asp arnd)) model2, ?_,
        fd, fd2, regsR, fmem inp asp arnd, model2,
        Hnefd, fd32_lt31 fd Hlt, fd32_lt31 fd2 Hlt2,
        ⟨R17, R10, R11, R12, R1, R13, R14, R15⟩, ?_, rfl⟩))
      · dsimp only [o2rec]
        rw [adv_eff_ret_copyins]
        apply dsil_msteps target_segs _ _ model2 _ (msteps_trans _ _ _ _ HmsH HmsR) rfl
        exact dsil.dsil_refl _
      · refine ⟨rfl, rfl, Z_to_bv 64 0, [], ?_, ?_, rfl, by decide +kernel⟩
        · change fd_lookup (fd_insert _ fd2 _) fd = _
          rw [fd_lookup_insert_neq _ _ _ _ Hnefd]
          exact fd_lookup_insert_eq _ _ _
        · exact fd_lookup_insert_eq _ _ _

include Hsd Hsome0 Hbig in
theorem tgt_huge_loop_anchor (c : config) (evs : List event) (st : step_to)
    (HA : tAnchor inp c) (Hss : sstep target_segs c evs st) :
    fdiv_resp target_segs (tHI inp asp arnd abrk amb) (tX inp) evs st := by
  obtain ⟨fdin, fdout, regs, mem, model, Hnefd, Hfin32, Hfout32, Hpins, HM, rfl⟩ := HA
  obtain ⟨R17, R10, R11, R12, R1, R13, R14, R15⟩ := Hpins
  obtain ⟨Hh, Hlazy, off, data, Hfin, Hfout, Hfsm, Hoff⟩ := HM
  let chunk := file_read d0 off (Z_to_bv 64 1024)
  obtain ⟨Hc1, Hc2⟩ := huge_chunk d0 Hbig off
  change 1 ≤ (chunk.length : Int) at Hc1
  change (chunk.length : Int) ≤ 1024 at Hc2
  have HuLen : bv_unsigned (len_word chunk) = (chunk.length : Int) := u_len_word _ (by omega)
  have Hg0 : ms_gpr (rdrec regs mem) 0 = fdin := R10
  have Hg1 : ms_gpr (rdrec regs mem) 1 = tbuf := R11
  have Hg2 : ms_gpr (rdrec regs mem) 2 = Z_to_bv 64 1024 := R12
  obtain ⟨w, Hw⟩ := wseg_ok_wdef target_segs tbuf (Z_to_bv 64 1024) (rdrec regs mem) target_buf_wseg
  obtain ⟨Hok, Huniq, Hne⟩ := read_file_uniq target_segs (rdrec regs mem) (getr regs 17)
    model (src inp) off d0 w R17 (by rw [Hg0]; exact Hfin) (by rw [Hg0]; exact Hfin32)
    (by rw [Hfsm, fs_lookup_set_neq _ _ _ _ Hsd]; exact Hsome0)
    (by rw [Hg1, Hg2]; exact Hw)
    (by rw [Hg2]; decide +kernel) (by rw [Hg2]; decide +kernel)
    (by rw [Hg1, Hg2]; apply access_okb_intro; rw [u_tbuf]; decide +kernel)
  try dsimp only at Hok Huniq
  rw [Hg0, Hg1, Hg2] at Hok Huniq
  have Hchunk_ne : chunk ≠ [] := by intro H; simp only [H, List.length_nil] at Hc1; omega
  change syscall_spec _ _ (Ok (mkEffect (len_word chunk) (delivered_writes tbuf chunk) []) _ []) at Hok
  change ∀ eff2 m2 evs2, syscall_spec _ _ (Ok eff2 m2 evs2) →
    eff2 = mkEffect (len_word chunk) (delivered_writes tbuf chunk) [] ∧
    m2 = with_fds (fd_insert (m_fds model) fdin (FdFile (src inp) (off + len_word chunk))) model ∧
    evs2 = [] at Huniq
  rw [delivered_writes_ne tbuf chunk Hchunk_ne] at Hok Huniq
  have Hshape : ∀ eff m' evs',
      syscall_spec (sys_input target_segs (rdrec regs mem) (getr regs 17)) model (Ok eff m' evs') →
      evs' = [] ∧ m_halted m' = none ∧ m_vm_lazy m' = [] := by
    intro eff m' evs' Hs
    obtain ⟨_, rfl, rfl⟩ := Huniq eff m' evs' Hs
    exact ⟨rfl, Hh, Hlazy⟩
  obtain ⟨eff, m2, Hspec, rfl, rfl⟩ := sstep_fsys_inv target_segs (rdrec regs mem) model
    (getr regs 17) evs st Hh Hlazy rfl Hne Hshape Hss
  obtain ⟨rfl, rfl, _⟩ := Huniq eff m2 [] Hspec
  refine ⟨rfl, _, rfl, Or.inl (Or.inr (Or.inr ?_))⟩
  let model' := with_fds (fd_insert (m_fds model) fdin (FdFile (src inp) (off + len_word chunk))) model
  obtain ⟨regsW, W17, W10, W11, W12, W1, W13, W14, W15, HmsW⟩ :=
    tgt_read_to_write (regupd regs 10 (len_word chunk)) (write_to_mem mem tbuf chunk)
      fdin fdout (len_word chunk) (by regupd_resolve; rfl) (by omega) (by omega)
      (by regupd_resolve; exact R1) (by regupd_resolve; exact R13)
      (by regupd_resolve; exact R14) (by regupd_resolve; exact R15)
  let wrec : machine_state :=
    { ms_regs := regsW, ms_fregs := bvmap_empty, ms_pc_val := 0x100123c,
      ms_svc_pending := some (getr regsW 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := write_to_mem mem tbuf chunk, ms_rom := trom }
  have HgW0 : ms_gpr wrec 0 = fdout := W10
  have HgW1 : ms_gpr wrec 1 = tbuf := W11
  have HgW2 : ms_gpr wrec 2 = len_word chunk := W12
  obtain ⟨HokW, HuniqW, HneW⟩ := write_file_uniq target_segs wrec (getr regsW 17)
    model' (dst inp) off data chunk W17
    (by rw [HgW0]; change fd_lookup (fd_insert _ fdin _) fdout = _
        rw [fd_lookup_insert_neq _ _ _ _ (Ne.symm Hnefd)]; exact Hfout)
    (by rw [HgW0]; exact Hfout32)
    (by rw [HgW1, HgW2, read_bytes_map_read_byte, ms_read_bytes_rdn target_segs wrec _ _ rfl]
        change rdn target_segs (write_to_mem mem tbuf chunk) tbuf (word_to_nat (len_word chunk)) = _
        rw [wtn_len_word chunk (by omega)]
        apply rdn_write_to_mem; rw [u_tbuf]; omega)
    (by rw [HgW2, HuLen]; unfold rw_bytes_max; omega)
    (by change fs_lookup (m_fs model) (dst inp) = _; rw [Hfsm]; exact fs_lookup_set_eq _ _ _)
    (by apply file_gap_in_range; unfold rw_bytes_max; omega)
    (by apply w_is0_pos; rw [HgW2, HuLen]; omega)
  try dsimp only at HokW HuniqW
  rw [HgW0, HgW2] at HokW HuniqW
  let model'' := with_fds (fd_insert (m_fds model') fdout (FdFileW (dst inp) (off + len_word chunk)))
    (with_fs (fs_set (m_fs model') (dst inp) (file_write data off chunk)) model')
  obtain ⟨regsH, G1, G13, G14, G15, HmsH⟩ :=
    tgt_write_to_head (regupd regsW 10 (len_word chunk)) (write_to_mem mem tbuf chunk)
      fdin fdout (len_word chunk) (by regupd_resolve; rfl) (by regupd_resolve; exact W12)
      (by omega) (by omega) (by regupd_resolve; exact W1) (by regupd_resolve; exact W13)
      (by regupd_resolve; exact W14) (by regupd_resolve; exact W15)
  obtain ⟨regsR2, Q17, Q10, Q11, Q12, Q1, Q13, Q14, Q15, HmsR2⟩ :=
    tgt_head_to_read regsH (write_to_mem mem tbuf chunk) fdin fdout G1 G13 G14 G15
  refine ⟨mkCfg (rdrec regsR2 (write_to_mem mem tbuf chunk)) model'', ?_,
    fdin, fdout, regsR2, write_to_mem mem tbuf chunk, model'', Hnefd, Hfin32, Hfout32,
    ⟨Q17, Q10, Q11, Q12, Q1, Q13, Q14, Q15⟩, ?_, rfl⟩
  · dsimp only [rdrec]
    rw [adv_apply_write]
    apply dsil_msteps target_segs _ _ model' _ HmsW Hlazy
    apply dsil.dsil_sys (ms := wrec) (model := model') (c'' := _) (x8 := getr regsW 17)
      (eff := with_copyins [(ms_gpr wrec 1, chunk.length)] (mkEffect (len_word chunk) [] []))
      (model' := model'') rfl Hh Hlazy HokW HuniqW HneW Hh Hlazy
    rw [adv_eff_ret_copyins]
    apply dsil_msteps target_segs _ _ model'' _ HmsH Hlazy
    apply dsil_msteps target_segs _ _ model'' _ HmsR2 Hlazy
    exact dsil.dsil_refl _
  · refine ⟨Hh, Hlazy, off + len_word chunk, file_write data off chunk, ?_, ?_, ?_, ?_⟩
    · change fd_lookup (fd_insert _ fdout _) fdin = _
      rw [fd_lookup_insert_neq _ _ _ _ Hnefd]
      exact fd_lookup_insert_eq _ _ _
    · exact fd_lookup_insert_eq _ _ _
    · change fs_set (m_fs model) (dst inp) (file_write data off chunk) = _
      rw [Hfsm]; exact fs_set_set _ _ _ _
    · exact file_write_off_bound data off chunk (by omega) Hoff

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsd Hsome0 Hbig Hsne0 Hdne0 in
theorem tgt_huge_ok : fdiv_ok target_segs (tHI inp asp arnd abrk amb) (tX inp) := by
  intro c Hc evs st Hss
  rcases Hc with ⟨ms, regs1, Hpins, Hm, rfl⟩ | ⟨ms, regs2, fd, Hlk, Hlt, Hpins, Hm, rfl⟩ |
    ⟨c'', Hd, HA⟩
  · rcases msteps_region_inv target_segs ms (o1rec inp asp arnd regs1) (model0 inp asp abrk amb)
      evs st Hm rfl Hss with rfl | ⟨Hevs, ms1, rfl, Hm1⟩
    · apply tgt_huge_open1_anchor (d0 := d0) <;> assumption
    · exact ⟨Hevs, _, rfl, Or.inl (Or.inl ⟨ms1, regs1, Hpins, Hm1, rfl⟩)⟩
  · rcases msteps_region_inv target_segs ms (o2rec inp asp arnd regs2) (model1 inp asp abrk amb fd)
      evs st Hm rfl Hss with rfl | ⟨Hevs, ms1, rfl, Hm1⟩
    · exact tgt_huge_open2_anchor (inp := inp) (Hva := Hva) (Hve := Hve)
        (asp := asp) (arnd := arnd) (Hsp_lo := Hsp_lo) (Hsp_hi := Hsp_hi)
        (abrk := abrk) (amb := amb) (Hge3 := Hge3) (Hdst_nodot := Hdst_nodot)
        (Hplen2 := Hplen2) (Hdne0 := Hdne0) regs2 fd evs st Hlk Hlt Hpins Hss
    · exact ⟨Hevs, _, rfl, Or.inl (Or.inr (Or.inl ⟨ms1, regs2, fd, Hlk, Hlt, Hpins, Hm1, rfl⟩))⟩
  · apply dsil_region_inv target_segs (tAnchor inp) (tHI inp asp arnd abrk amb) (tX inp)
      _ _ _ _ c c'' Hd HA evs st Hss
    · rintro c0 ⟨fdin, fdout, regs, mem, model, _, _, _, _, ⟨Hh, _, _⟩, rfl⟩
      exact Hh
    · rintro c0 ⟨fdin, fdout, regs, mem, model, _, _, _, _, ⟨_, Hlazy, _⟩, rfl⟩
      exact Hlazy
    · intro c0 HA0 evs0 st0 Hss0
      apply tgt_huge_loop_anchor (d0 := d0) <;> assumption
    · intro c0 c1 Hd0 HA0
      exact Or.inr (Or.inr ⟨c1, Hd0, HA0⟩)

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsome0 Hsne0 Hdne0 in
theorem tgt_huge_admits (o : word × Fs) (Ho : tX inp o) :
    ∃ c, star target_segs
      (init_config target_segs 0x1001190 target_phdrs asp abrk amb arnd target_alloc_limit inp)
      (fout_trace o) c := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  have Hstar1 : star target_segs
      (init_config target_segs 0x1001190 target_phdrs asp abrk amb arnd target_alloc_limit inp)
      [] (mkCfg (o1rec inp asp arnd regs1) (model0 inp asp abrk amb)) := by
    apply msteps_star_nil _ _ _ _ rfl rfl
    apply msteps_trans _ _ _ _ Hms
    exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d8 rfl) (msteps.mst_refl _)
  obtain ⟨Hne, Herr, Hok, Hinv⟩ := open_rd_branches target_segs (o1rec inp asp arnd regs1)
    (getr regs1 17) (model0 inp asp abrk amb) (src inp) d0 H17 H10
    (by change read_cstr (mrb target_segs (fmem inp asp arnd)) (reg_get regs1 11) = _
        rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hplen1)
    Hsne0 (by change bv_unsigned (bv_and (reg_get regs1 12) _) = 0; rw [H12]; decide +kernel)
    Hsrc_nodot Hsome0
  rcases Ho with rfl | rfl
  · have Hto : to_fout target_segs
        (advance_past_svc (apply_effect (o1rec inp asp arnd regs1)
          (with_copyins (open_copyins (o1rec inp asp arnd regs1)) (mkEffect (errno_ret ENOMEM) [] []))))
        (model0 inp asp abrk amb) (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
      rw [o1rec, adv_eff_ret_copyins]
      apply tgt_open1_err_tail (e := ENOMEM)
      · decide +kernel
      · decide +kernel
      · regupd_resolve; rfl
      · regupd_resolve; exact H1
      · rfl
    obtain ⟨c, Hstar3⟩ := to_fout_star_admits target_segs _ _ _ Hto rfl rfl
      (Z_to_bv 64 3, inp.in_fs) rfl
    refine ⟨c, ?_⟩
    exact star_trans target_segs _ [] _ _ _ Hstar1
      (star_trans target_segs _ [] _ _ _
        (star_syscall_nil target_segs _ _ _ _ _ rfl rfl (Herr ENOMEM ENOMEM_in_openat_errnos) rfl rfl)
        Hstar3)
  · obtain ⟨regs2, K17, K10, K11, K12, K14, K1, Hms2⟩ :=
      tgt_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
        (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        (by regupd_resolve; rfl) (by decide +kernel)
        (by regupd_resolve; exact H15) (by regupd_resolve; exact H1)
    have Hstar2 : star target_segs (mkCfg (o1rec inp asp arnd regs1) (model0 inp asp abrk amb))
        [] (mkCfg (o2rec inp asp arnd regs2) (model1 inp asp abrk amb (Z_to_bv 64 3))) := by
      apply star_trans target_segs _ [] _ [] _
        (star_syscall_nil target_segs _ _ _ _ _ rfl rfl (Hok (Z_to_bv 64 3) rfl rfl) rfl rfl)
      rw [o1rec, adv_eff_ret_copyins]
      exact msteps_star_nil _ _ _ _ rfl rfl Hms2
    have Hpath : read_cstr (ms_read_byte (o2rec inp asp arnd regs2))
        (ms_gpr (o2rec inp asp arnd regs2) 1) = CstrOk (dst inp) := by
      change read_cstr (mrb target_segs (fmem inp asp arnd)) (reg_get regs2 11) = _
      rw [K11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hplen2
    have Hfl : bv_unsigned (bv_and (ms_gpr (o2rec inp asp arnd regs2) 2)
        (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags := by
      change bv_unsigned (bv_and (reg_get regs2 12) _) = _
      rw [K12]; decide +kernel
    have Herr2 : ∃ e, 1 ≤ e ∧ e ≤ 4095 ∧
        syscall_spec (sys_input target_segs (o2rec inp asp arnd regs2) (getr regs2 17))
          (model1 inp asp abrk amb (Z_to_bv 64 3))
          (Ok (with_copyins (open_copyins (o2rec inp asp arnd regs2)) (mkEffect (errno_ret e) [] []))
            (model1 inp asp abrk amb (Z_to_bv 64 3)) []) := by
      cases Hun : fs_under inp.in_fs (dst inp) with
      | true =>
        obtain ⟨HokB, _, _⟩ := open_wr_isdir target_segs (o2rec inp asp arnd regs2) (getr regs2 17)
          (model1 inp asp abrk amb (Z_to_bv 64 3)) (dst inp) K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
        exact ⟨EISDIR, by decide +kernel, by decide +kernel, HokB⟩
      | false =>
        obtain ⟨_, HerrB, _, _⟩ := open_wr_branches target_segs (o2rec inp asp arnd regs2) (getr regs2 17)
          (model1 inp asp abrk amb (Z_to_bv 64 3)) (dst inp) K17 K10 Hpath Hdne0 Hfl Hdst_nodot Hun
        exact ⟨ENOMEM, by decide +kernel, by decide +kernel, HerrB ENOMEM ENOMEM_in_openat_errnos⟩
    obtain ⟨e, He1, He2, Hspec⟩ := Herr2
    have Hto : to_fout target_segs
        (advance_past_svc (apply_effect (o2rec inp asp arnd regs2)
          (with_copyins (open_copyins (o2rec inp asp arnd regs2)) (mkEffect (errno_ret e) [] []))))
        (model1 inp asp abrk amb (Z_to_bv 64 3)) (fun o => o = (Z_to_bv 64 4, inp.in_fs)) := by
      rw [o2rec, adv_eff_ret_copyins]
      apply tgt_open2_err_tail (e := e)
      · exact He1
      · exact He2
      · regupd_resolve; rfl
      · regupd_resolve; exact K1
      · rfl
    obtain ⟨c, Hstar4⟩ := to_fout_star_admits target_segs _ _ _ Hto rfl rfl
      (Z_to_bv 64 4, inp.in_fs) rfl
    refine ⟨c, ?_⟩
    exact star_trans target_segs _ [] _ _ _ Hstar1
      (star_trans target_segs _ [] _ _ _ Hstar2
        (star_trans target_segs _ [] _ _ _
          (star_syscall_nil target_segs _ _ _ _ _ rfl rfl Hspec rfl rfl) Hstar4))

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsd Hsome0 Hbig Hsne0 Hdne0 in
theorem target_huge_obs (tr : List event) :
    obs_trace target_segs
      (init_config target_segs 0x1001190 target_phdrs asp abrk amb arnd target_alloc_limit inp) tr ↔
    ∃ o, (o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) ∧
      is_prefix tr (fout_trace o) := by
  have Hok : fdiv_ok target_segs (tHI inp asp arnd abrk amb) (tX inp) := by
    apply tgt_huge_ok (d0 := d0) <;> assumption
  have Hstart := tgt_huge_start inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    rcases fdiv_star_only target_segs _ _ Hok _ _ _ Hstar Hstart with Hnil | ⟨o, Ho, Hp'⟩
    · subst tr'
      cases tr with
      | nil => exact ⟨(Z_to_bv 64 3, inp.in_fs), Or.inl rfl, is_prefix_nil _⟩
      | cons x tr => exact False.elim Hp
    · exact ⟨o, Ho, is_prefix_trans _ _ _ Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    have Hex : ∃ c, star target_segs
        (init_config target_segs 0x1001190 target_phdrs asp abrk amb arnd target_alloc_limit inp)
        (fout_trace o) c := by
      apply tgt_huge_admits (d0 := d0) <;> assumption
    obtain ⟨c, Hstar⟩ := Hex
    exact ⟨fout_trace o, c, Hstar, Hp⟩

include Hva Hve Hsp_lo Hsp_hi Hge3 Hsrc_nodot Hdst_nodot Hplen1 Hplen2 Hsd Hsome0 Hbig Hsne0 Hdne0 in
theorem target_huge_no_error :
    ¬ reaches_error target_segs
      (init_config target_segs 0x1001190 target_phdrs asp abrk amb arnd target_alloc_limit inp) := by
  apply fdiv_no_error target_segs (tHI inp asp arnd abrk amb) (tX inp)
  · apply tgt_huge_ok (d0 := d0) <;> assumption
  · apply tgt_huge_start <;> assumption

end TargetProof

end LinuxProcessSemantics.Examples.cp_ns.cp_ns_target
