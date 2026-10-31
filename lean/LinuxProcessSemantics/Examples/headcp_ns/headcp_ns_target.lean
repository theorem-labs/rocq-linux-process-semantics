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

/-! # headcp-ns: target binary

PROOF-SIDE FILE (not part of the trusted specification).
Twins `theories/Examples/headcp_ns/headcp_ns_target.v`.
Section parameters are explicit; shared facts are supplied by the common libraries.
-/

namespace LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_target

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
open LinuxProcessSemantics.Examples.headcp_ns.TargetMemImage

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

def trom : word → Option byte := seg_rom target_segs
def tbuf : word := 0x1002278

theorem u_tbuf : bv_unsigned tbuf = 0x1002278 := rfl

/-- The shared buffer fact covers a different address; use the range encoded
by this target binary, checked against its generated image. -/
private theorem headcp_buf_wseg :
    wseg_ok target_segs tbuf (word_to_nat (Z_to_bv 64 128)) = true := by
  apply wseg_ok_backed target_segs TargetMemImage_segment_002 _ _
    [TargetMemImage_seg_bytes_002_chars]
  · rfl
  · decide
  · exact congrArg (fun x => [x]) TargetMemImage_seg_bytes_002_chars_eq
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact TargetMemImage_seg_bytes_002_ascii
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact TargetMemImage_seg_bytes_002_hex
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    simp only [TargetMemImage_seg_bytes_002_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      TargetMemImage_seg_bytes_002_chars, List.length_replicate]
    decide
  · decide

theorem c_eq_bu_true (b : byte) (Hb : b = Z_to_bv 8 0) :
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = true := by
  subst b; rfl

theorem c_eq_bu_false (b : byte) (Hb : b ≠ Z_to_bv 8 0) :
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false := by
  apply c_eq_0_false
  rw [u_Z2bv _ (u8_range b).1 (by have H := u8_range b; omega)]
  intro H
  apply Hb
  apply bv_eq_of_unsigned
  exact H

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

def argcN : word := Common.ArgvEnv.argcN inp.in_argv

def wmem : word → Option byte :=
  wrap_mem target_phdrs asp inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd

include Hva in
theorem u_argcN : bv_unsigned (argcN inp) = (inp.in_argv.length : Int) :=
  Common.ArgvEnv.u_argcN inp.in_argv Hva

include Hva Hve Hsp_hi in
theorem target_bsb_nw :
    bv_unsigned asp + ((build_stack_bytes target_phdrs asp inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap arnd).length : Int) < 2 ^ 64 :=
  Common.ArgvEnv.bsb_nw target_phdrs asp inp.in_argv inp.in_envp inp.in_uid
    inp.in_hwcap arnd Hva Hve Hsp_hi

def fmem : word → Option byte :=
  wbytes (wbytes (wmem inp asp arnd)
    (Z_to_bv 64 (bv_unsigned asp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))

include Hsp_lo Hsp_hi in
theorem rdn_fmem_above (a : word) (n : Nat)
    (Ha : bv_unsigned asp ≤ bv_unsigned a) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs (fmem inp asp arnd) a n = rdn target_segs (wmem inp asp arnd) a n := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  unfold fmem
  rw [rdn_wbytes_disjoint, rdn_wbytes_disjoint]
  all_goals try rfl
  all_goals try rw [length_N_to_le_bytes]
  all_goals u_norm; omega

theorem rdn_wmem_stack (a : word) (n : Nat)
    (Ha : bv_unsigned asp ≤ bv_unsigned a) (Hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn target_segs (wmem inp asp arnd) a n =
      rdn target_segs (stack_to_mem asp (entry_stack_image target_phdrs asp
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd)) a n :=
  rdn_wrap_stack_above target_segs target_phdrs asp inp.in_argv inp.in_envp a n
    inp.in_uid inp.in_hwcap arnd Ha Hn

include Hva Hve Hsp_hi in
theorem read_argc_w :
    rdn target_segs (wmem inp asp arnd) asp 8 = some (word_le8 (argcN inp)) :=
  Common.ArgvEnv.read_argc_w target_segs target_phdrs asp inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap arnd Hva Hve Hsp_hi

def src : path := inp.in_argv.getD 1 []
def dst : path := inp.in_argv.getD 2 []
def psrc : word := cat_argv_ptr asp inp.in_argv inp.in_envp 1
def pdst : word := cat_argv_ptr asp inp.in_argv inp.in_envp 2


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

theorem tgt_openat_enoent_empty (ms : machine_state) (model : Model)
    (x8 : word) (p : path) (U : word × Fs → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 56)
    (Hfl : modeled_open_flags (ms_gpr ms 2) = true)
    (_Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = cstr_result.CstrOk p)
    (Hpe : path_eqb p [] = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
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
    rw [in_sysno_si, Hno]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_openat
  refine tfo_sys_det target_segs ms model x8 _ model U Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
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
    (Hfl : modeled_open_flags (reg_get regs 12) = true)
    (H10 : reg_get regs 10 = AT_FDCWD)
    (Hpath : read_cstr (mrb target_segs mem) (reg_get regs 11) = cstr_result.CstrOk p)
    (Hpe : path_eqb p [] = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout target_segs (mkst (regupd regs 10 (errno_ret ENOENT))
      (v_addi pc 4) mem (seg_rom target_segs)) model U) :
    to_fout target_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs } model U := by
  apply tgt_openat_enoent_empty
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none,
      ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs } model (getr regs 17) p U rfl H17 Hfl H10 Hpath Hpe Hh Hlazy
  simpa only [adv_eff_ret_copyins] using Hcont

theorem tgt_read_dir_eisdir (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (fdv : word) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 63) (H10 : reg_get regs 10 = fdv)
    (Hfd : fd_lookup (m_fds model) fdv = some FdDir) (Hfd32 : fd32 fdv = fdv)
    (Hdr : (!access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12))) = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout target_segs (mkst (regupd regs 10 (errno_ret EISDIR))
      (v_addi pc 4) mem (seg_rom target_segs)) model U) :
    to_fout target_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs } model U := by
  let ms : machine_state :=
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs }
  have Hchk : ∀ eff, check_syscall (sys_input target_segs ms (getr regs 17)) eff model =
      check_ret_only eff (errno_ret EISDIR) model [] := by
    intro eff
    rw [check_syscall_63 target_segs ms (getr regs 17) eff model H17]
    change check_read _ (fd32 (reg_get regs 10)) (reg_get regs 11) (reg_get regs 12) eff model = _
    simp only [check_read, H10, Hfd32, Hfd, Hdr, Bool.false_eq_true, ↓reduceIte]
  have Hagree : lookups_agree_at (bv_unsigned (sys_input target_segs ms (getr regs 17)).in_sysno) := by
    rw [in_sysno_si, H17]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_read
  refine tfo_sys_det target_segs ms model (getr regs 17) (mkEffect (errno_ret EISDIR) [] []) model U rfl ?_ ?_ ?_ Hh Hlazy ?_
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

theorem tgt_open_dot_wr_eisdir (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 577)
    (Hpath : read_cstr (mrb target_segs mem) (reg_get regs 11) = cstr_result.CstrOk dot_path)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout target_segs (mkst (regupd regs 10 (errno_ret EISDIR))
      (v_addi pc 4) mem (seg_rom target_segs)) model U) :
    to_fout target_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs } model U := by
  let ms : machine_state :=
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs }
  have Hd0 : ms_gpr ms 0 = AT_FDCWD := H10
  have Hp : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = cstr_result.CstrOk dot_path := Hpath
  have Hf : ms_gpr ms 2 = Z_to_bv 64 577 := H12
  have Hchk : ∀ eff, check_syscall (sys_input target_segs ms (getr regs 17)) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model [] := by
    intro eff
    rw [check_syscall_56 target_segs ms (getr regs 17) eff model H17]
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
  have Hagree : lookups_agree_at (bv_unsigned (sys_input target_segs ms (getr regs 17)).in_sysno) := by
    rw [in_sysno_si, H17]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_openat
  refine tfo_sys_det target_segs ms model (getr regs 17)
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

theorem tgt_open_dot_rd_rec (regs : bvmap 5 word) (pc : word) (mem : word → Option byte)
    (model : Model) (Te : Int → word × Fs → Prop) (Ts : word → word × Fs → Prop)
    (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 0)
    (Hpath : read_cstr (mrb target_segs mem) (reg_get regs 11) = cstr_result.CstrOk dot_path)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ openat_errnos →
      to_fout target_segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
        mem (seg_rom target_segs)) model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout target_segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom target_segs))
        (with_fds (fd_insert (m_fds model) fd FdDir) model) (Ts fd))
    (HU : ∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) :
    to_fout target_segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs } model U := by
  let ms : machine_state :=
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom target_segs }
  have Hd0 : ms_gpr ms 0 = AT_FDCWD := H10
  have Hp : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = cstr_result.CstrOk dot_path := Hpath
  have Hf : ms_gpr ms 2 = Z_to_bv 64 0 := H12
  apply tfo_open_core target_segs ms model
    (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)
    (getr regs 17) (open_copyins ms) Te Ts U rfl Hh Hlazy
  · intro eff
    rw [check_syscall_56 target_segs ms (getr regs 17) eff model H17]
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

section Ge3
variable (Hge3 : 3 ≤ inp.in_argv.length)

include Hva Hve Hsp_hi Hge3 in
theorem psrc_bounds :
    bv_unsigned asp ≤ bv_unsigned (psrc inp asp) ∧
      bv_unsigned (psrc inp asp) + ((src inp).length : Int) + 1 < 2 ^ 64 :=
  Common.ArgvEnv.argv_ptr_bounds_at asp inp.in_argv inp.in_envp Hva Hve Hsp_hi 1 (by omega)

include Hva Hve Hsp_hi Hge3 in
theorem pdst_bounds :
    bv_unsigned asp ≤ bv_unsigned (pdst inp asp) ∧
      bv_unsigned (pdst inp asp) + ((dst inp).length : Int) + 1 < 2 ^ 64 :=
  Common.ArgvEnv.argv_ptr_bounds_at asp inp.in_argv inp.in_envp Hva Hve Hsp_hi 2 (by omega)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_psrc_f :
    rdn target_segs (fmem inp asp arnd) (asp + nat_to_word (8 + 8 * 1)) 8 =
      some (word_le8 (psrc inp asp)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  rw [rdn_fmem_above inp asp arnd Hsp_lo Hsp_hi]
  · exact Common.ArgvEnv.read_argv_ptr_w target_segs target_phdrs asp
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd Hva Hve Hsp_lo Hsp_hi 1 (by omega)
  all_goals rw [word_add_nat]; u_norm; omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem read_pdst_f :
    rdn target_segs (fmem inp asp arnd) (asp + nat_to_word (8 + 8 * 2)) 8 =
      some (word_le8 (pdst inp asp)) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  rw [rdn_fmem_above inp asp arnd Hsp_lo Hsp_hi]
  · exact Common.ArgvEnv.read_argv_ptr_w target_segs target_phdrs asp
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap arnd Hva Hve Hsp_lo Hsp_hi 2 (by omega)
  all_goals rw [word_add_nat]; u_norm; omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_src (Hlen : (src inp).length ≤ 4095) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (psrc inp asp) = cstr_result.CstrOk (src inp) := by
  obtain ⟨Hplo, Hphi⟩ := psrc_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz inp.in_argv 1 Hva (by omega)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_cstr_k target_phdrs target_segs asp inp.in_argv inp.in_envp 1
        inp.in_uid inp.in_hwcap arnd (by omega) (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_dst (Hlen : (dst inp).length ≤ 4095) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (pdst inp asp) = cstr_result.CstrOk (dst inp) := by
  obtain ⟨Hplo, Hphi⟩ := pdst_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_of_rdn
  · exact Hlen
  · exact valid_argv_str_nz inp.in_argv 2 Hva (by omega)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_cstr_k target_phdrs target_segs asp inp.in_argv inp.in_envp 2
        inp.in_uid inp.in_hwcap arnd (by omega) (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_src_toolong (Hlen : 4096 ≤ (src inp).length) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (psrc inp asp) = cstr_result.CstrTooLong := by
  obtain ⟨Hplo, Hphi⟩ := psrc_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn target_segs _ _ ((src inp).take 4096)
  · rw [List.length_take, Nat.min_eq_left Hlen]
  · intro H
    exact valid_argv_str_nz inp.in_argv 1 Hva (by omega) (List.mem_of_mem_take H)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_prefix_k target_phdrs target_segs asp inp.in_argv inp.in_envp 1 4096
        inp.in_uid inp.in_hwcap arnd (by omega) Hlen (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_cstr_dst_toolong (Hlen : 4096 ≤ (dst inp).length) :
    read_cstr (mrb target_segs (fmem inp asp arnd)) (pdst inp asp) = cstr_result.CstrTooLong := by
  obtain ⟨Hplo, Hphi⟩ := pdst_bounds inp Hva Hve asp Hsp_hi Hge3
  apply read_cstr_toolong_of_rdn target_segs _ _ ((dst inp).take 4096)
  · rw [List.length_take, Nat.min_eq_left Hlen]
  · intro H
    exact valid_argv_str_nz inp.in_argv 2 Hva (by omega) (List.mem_of_mem_take H)
  · rw [rdn_fmem_above inp asp arnd Hsp_lo Hsp_hi, rdn_wmem_stack]
    · exact read_argv_prefix_k target_phdrs target_segs asp inp.in_argv inp.in_envp 2 4096
        inp.in_uid inp.in_hwcap arnd (by omega) Hlen (target_bsb_nw inp Hva Hve asp arnd Hsp_hi)
    all_goals omega

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_to_open1 :
    ∃ regs1, reg_get regs1 1 = (0x10011b0 : word) ∧
      reg_get regs1 15 = Z_to_bv 64 (bv_unsigned asp + 8) ∧
      bv_unsigned (getr regs1 17) = 56 ∧ reg_get regs1 10 = AT_FDCWD ∧
      reg_get regs1 11 = psrc inp asp ∧ reg_get regs1 12 = Z_to_bv 64 0 ∧
      msteps target_segs
        (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
          inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (mkst regs1 0x10011d8 (fmem inp asp arnd) trom) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  have Hu := u_argcN inp Hva
  have Hnat : (argcN inp).toNat = inp.in_argv.length := by
    unfold bv_unsigned at Hu
    omega
  have Hbr : (!bv_ltu (Z_to_bv 64 2) (argcN inp)) = false := by
    change (!decide (2 < (argcN inp).toNat)) = false
    rw [Hnat]
    simp only [show 2 < inp.in_argv.length by omega,
      decide_true, Bool.not_true]
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
      (Z_to_bv 64 16781712) (wmem inp asp arnd) trom)
    20 [false] [EVar 33, EVar 34] [(2, EVar 32)]
    [asp] [argcN inp, psrc inp asp] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | exact Hbr
    | (apply store_ok_wrap_window
       all_goals try rw [stack_max_size_val]
       all_goals u_norm; omega)
    | (refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
       change rdn target_segs (wmem inp asp arnd) (v_addi asp 0) 8 = _
       rw [v_addi_0]
       exact read_argc_w inp Hva Hve asp arnd Hsp_hi)
    | (refine ⟨word_le8 (psrc inp asp), ?_, bytes_le_n_to_le_8 _⟩
       have H := read_psrc_f inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
       rw [rdn_fmem_above inp asp arnd Hsp_lo Hsp_hi] at H
       · rw [word_add_nat] at H; exact H
       all_goals rw [word_add_nat]; u_norm; omega)
    | (change (!c_ltu (Z_to_bv 64 2) (argcN inp)) = false
       rw [c_ltu_ltb, Bool.not_eq_false, decide_eq_true_eq]
       u_norm; omega)
    | (u_norm; omega))
  all_goals try (solve | headcp_eq_goal; getr_resolve; regupd_resolve; rfl)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (rw [init_mkst]
       apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       unfold fmem
       sym_mem_norm
       getr_resolve
       exact msteps.mst_refl _)

theorem target_err_exit (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (code : word) (fsv : Fs)
    (H11 : reg_get regs 11 = code) (H1 : reg_get regs 1 = (0x10011b0 : word))
    (Hc : bv_unsigned code < 256) (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x1001270 mem trom) model
      (fun o => o = (code, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781936) mem trom)
    5 [] [] [(1, ELit 0x10011b0), (11, EVar 32)] [code] [] R HR Hms
  all_goals try (solve | headcp_pin H1 | headcp_pin H11)
  apply tfo_msteps target_segs _ _ _ _ Hms
  sym_pc_lit
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011b4 rfl
  apply tfo_exit_rec
  · headcp_out HR
  · headcp_out HR
  · exact Hc
  · exact Hfs

theorem tgt_exit3 (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (X : word) (fsv : Fs)
    (H1 : reg_get regs 1 = (0x10011b0 : word)) (H10 : reg_get regs 10 = X)
    (Hneg : c_lts X (Z_to_bv 64 0) = true) (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x10011dc mem trom) model
      (fun o => o = (Z_to_bv 64 3, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781788) mem trom)
    7 [true] [] [(1, ELit 0x10011b0), (10, EVar 32)] [X] [] R HR Hms
  all_goals try (solve | exact Hneg | headcp_pin H1 | headcp_pin H10)
  apply tfo_msteps target_segs _ _ _ _ Hms
  sym_pc_lit
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011b4 rfl
  apply tfo_exit_rec
  · headcp_out HR
  · headcp_out HR
  · decide
  · exact Hfs

theorem tgt_exit4 (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (X : word) (fsv : Fs)
    (H1 : reg_get regs 1 = (0x10011b0 : word)) (H10 : reg_get regs 10 = X)
    (Hneg : c_lts X (Z_to_bv 64 0) = true) (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x10011fc mem trom) model
      (fun o => o = (Z_to_bv 64 4, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781820) mem trom)
    7 [true] [] [(1, ELit 0x10011b0), (10, EVar 32)] [X] [] R HR Hms
  all_goals try (solve | exact Hneg | headcp_pin H1 | headcp_pin H10)
  apply tfo_msteps target_segs _ _ _ _ Hms
  sym_pc_lit
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011b4 rfl
  apply tfo_exit_rec
  · headcp_out HR
  · headcp_out HR
  · decide
  · exact Hfs

theorem tgt_exit5 (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (X : word) (fsv : Fs)
    (H1 : reg_get regs 1 = (0x10011b0 : word)) (H10 : reg_get regs 10 = X)
    (Hneg : c_lts X (Z_to_bv 64 0) = true) (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x100121c mem trom) model
      (fun o => o = (Z_to_bv 64 5, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781852) mem trom)
    7 [true] [] [(1, ELit 0x10011b0), (10, EVar 32)] [X] [] R HR Hms
  all_goals try (solve | exact Hneg | headcp_pin H1 | headcp_pin H10)
  apply tfo_msteps target_segs _ _ _ _ Hms
  sym_pc_lit
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011b4 rfl
  apply tfo_exit_rec
  · headcp_out HR
  · headcp_out HR
  · decide
  · exact Hfs

theorem tgt_exit0 (regs : bvmap 5 word) (mem : word → Option byte)
    (model : Model) (fsv : Fs) (H1 : reg_get regs 1 = (0x10011b0 : word))
    (Hfs : m_fs model = fsv) :
    to_fout target_segs (mkst regs 0x100124c mem trom) model
      (fun o => o = (Z_to_bv 64 0, fsv)) := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781900) mem trom)
    6 [] [] [(1, ELit 0x10011b0)] [] [] R HR Hms
  all_goals try (solve | headcp_pin H1)
  apply tfo_msteps target_segs _ _ _ _ Hms
  sym_pc_lit
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011b4 rfl
  apply tfo_exit_rec
  · headcp_out HR
  · headcp_out HR
  · decide
  · exact Hfs

theorem tgt_open2_to_read (regs : bvmap 5 word) (mem : word → Option byte)
    (fdin fdout : word)
    (H1 : reg_get regs 1 = (0x10011b0 : word))
    (H10 : reg_get regs 10 = fdout)
    (H14 : reg_get regs 14 = fdin)
    (Hbound : bv_unsigned fdout < 2 ^ 31)
    : ∃ R,
      bv_unsigned (getr R 17) = 63 ∧
      reg_get R 10 = fdin ∧
      reg_get R 11 = tbuf ∧
      reg_get R 12 = Z_to_bv 64 128 ∧
      reg_get R 1 = (0x10011b0 : word) ∧
      reg_get R 13 = fdout ∧
      reg_get R 14 = fdin ∧
      msteps target_segs (mkst regs 0x10011fc mem trom)
        { ms_regs := R, ms_fregs := bvmap_empty, ms_pc_val := 0x1001218,
          ms_svc_pending := some (getr R 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom } := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781820) mem trom)
    8 [false] [] [(10, EVar 32), (14, EVar 33)]
    [fdout, fdin] [] R HR Hms
  all_goals try (solve
    | (apply c_lts_pos_0; omega)
    | headcp_pin H10
    | headcp_pin H14
    )
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ TF_1001218 rfl
       exact msteps.mst_refl _)

theorem tgt_read_to_write (regs : bvmap 5 word) (mem : word → Option byte)
    (fdin fdout cnt : word)
    (H1 : reg_get regs 1 = (0x10011b0 : word))
    (H10 : reg_get regs 10 = cnt)
    (H11 : reg_get regs 11 = tbuf)
    (H13 : reg_get regs 13 = fdout)
    (H14 : reg_get regs 14 = fdin)
    (Hbound : bv_unsigned cnt ≤ 128)
    : ∃ R,
      bv_unsigned (getr R 17) = 64 ∧
      reg_get R 10 = fdout ∧
      reg_get R 11 = tbuf ∧
      reg_get R 12 = cnt ∧
      reg_get R 1 = (0x10011b0 : word) ∧
      reg_get R 13 = fdout ∧
      reg_get R 14 = fdin ∧
      msteps target_segs (mkst regs 0x100121c mem trom)
        { ms_regs := R, ms_fregs := bvmap_empty, ms_pc_val := 0x100122c,
          ms_svc_pending := some (getr R 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom } := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781852) mem trom)
    5 [false] [] [(10, EVar 32), (13, EVar 33)]
    [cnt, fdout] [] R HR Hms
  all_goals try (solve
    | (apply c_lts_pos_0; omega)
    | headcp_pin H10
    | headcp_pin H13
    )
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ TF_100122c rfl
       exact msteps.mst_refl _)

theorem tgt_write_to_close (regs : bvmap 5 word) (mem : word → Option byte)
    (fdin fdout cnt : word)
    (H1 : reg_get regs 1 = (0x10011b0 : word))
    (H10 : reg_get regs 10 = cnt)
    (H13 : reg_get regs 13 = fdout)
    (H14 : reg_get regs 14 = fdin)
    (Hbound : bv_unsigned cnt ≤ 128)
    : ∃ R,
      bv_unsigned (getr R 17) = 57 ∧
      reg_get R 10 = fdin ∧
      reg_get R 1 = (0x10011b0 : word) ∧
      reg_get R 13 = fdout ∧
      msteps target_segs (mkst regs 0x1001230 mem trom)
        { ms_regs := R, ms_fregs := bvmap_empty, ms_pc_val := 0x100123c,
          ms_svc_pending := some (getr R 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom } := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781872) mem trom)
    4 [false] [] [(10, EVar 32), (14, EVar 33)]
    [cnt, fdin] [] R HR Hms
  all_goals try (solve
    | (apply c_lts_pos_0; omega)
    | headcp_pin H10
    | headcp_pin H14
    )
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ TF_100123c rfl
       exact msteps.mst_refl _)

theorem tgt_close_to_close (regs : bvmap 5 word) (mem : word → Option byte)
    (fdout : word)
    (H1 : reg_get regs 1 = (0x10011b0 : word))
    (H13 : reg_get regs 13 = fdout)
    : ∃ R,
      bv_unsigned (getr R 17) = 57 ∧
      reg_get R 10 = fdout ∧
      reg_get R 1 = (0x10011b0 : word) ∧
      msteps target_segs (mkst regs 0x1001240 mem trom)
        { ms_regs := R, ms_fregs := bvmap_empty, ms_pc_val := 0x1001248,
          ms_svc_pending := some (getr R 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom } := by
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781888) mem trom)
    3 [] [] [(13, EVar 32)]
    [fdout] [] R HR Hms
  all_goals try (solve
    | headcp_pin H13
    )
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ TF_1001248 rfl
       exact msteps.mst_refl _)

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem tgt_open1_to_open2 (regs : bvmap 5 word) (fd : word)
    (H1 : reg_get regs 1 = (0x10011b0 : word)) (H10 : reg_get regs 10 = fd)
    (H15 : reg_get regs 15 = Z_to_bv 64 (bv_unsigned asp + 8))
    (Hlt : bv_unsigned fd < 2 ^ 31) :
    ∃ R, bv_unsigned (getr R 17) = 56 ∧ reg_get R 10 = AT_FDCWD ∧
      reg_get R 11 = pdst inp asp ∧ reg_get R 12 = Z_to_bv 64 577 ∧
      reg_get R 1 = (0x10011b0 : word) ∧ reg_get R 14 = fd ∧
      msteps target_segs (mkst regs 0x10011dc (fmem inp asp arnd) trom)
        { ms_regs := R, ms_fregs := bvmap_empty, ms_pc_val := 0x10011f8,
          ms_svc_pending := some (getr R 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := fmem inp asp arnd, ms_rom := trom } := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 16781788) (fmem inp asp arnd) trom)
    8 [false] [EVar 34] [(10, EVar 32), (15, EVar 33)]
    [fd, Z_to_bv 64 (bv_unsigned asp + 8)] [pdst inp asp] R HR Hms
  all_goals repeat' apply And.intro
  all_goals try (solve
    | (refine ⟨word_le8 (pdst inp asp), ?_, bytes_le_n_to_le_8 _⟩
       have H := read_pdst_f inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
       rw [word_add_nat] at H
       exact H)
    | (u_norm; omega)
    | (apply c_lts_pos_0; omega)
    | headcp_pin H10
    | headcp_pin H15)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | headcp_out HR
    | (apply msteps_trans _ _ _ _ Hms
       sym_pc_lit
       apply msteps.mst_step _ _ _ rfl
       · exact step_ecall _ _ _ _ _ _ TF_10011f8 rfl
       exact msteps.mst_refl _)

private def headcp_pending (regs : bvmap 5 word) (pc : word) (mem : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
    ms_svc_pending := some (getr regs 17), ms_resv := none,
    ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := trom }

include Hva Hve Hsp_lo Hsp_hi Hge3 in
private theorem headcp_first_file (d0 : List byte) (U : word × Fs → Prop)
    (Hsrc_nodot : openat_plain_name (src inp) = true)
    (Hlen : (src inp).length ≤ 4095) (Hsne : path_eqb (src inp) [] = false)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0)
    (Hcont : ∀ regs2, bv_unsigned (getr regs2 17) = 56 → reg_get regs2 10 = AT_FDCWD →
      reg_get regs2 11 = pdst inp asp → reg_get regs2 12 = Z_to_bv 64 577 →
      reg_get regs2 1 = (0x10011b0 : word) → reg_get regs2 14 = Z_to_bv 64 3 →
      to_fout target_segs (headcp_pending regs2 0x10011f8 (fmem inp asp arnd))
        (with_fds (fd_insert (m_fds (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
          (Z_to_bv 64 3) (FdFile (src inp) (Z_to_bv 64 0)))
          (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)) U) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ U o) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps target_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011d8 rfl
  apply tfo_open_rd_rec target_segs _ _ _
    (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) (src inp) d0
    (fun _ o => o = (Z_to_bv 64 3, inp.in_fs)) (fun _ => U) _ H17 H10 H12
    (by rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen)
    Hsne Hsrc_nodot Hsome rfl rfl
  · intro e He
    obtain ⟨He1, He2⟩ := openat_errno_range e He
    apply tgt_exit3
    · regupd_resolve; exact H1
    · regupd_resolve; rfl
    · exact c_lts_errno e He1 He2
    · rfl
  · intro fd Hlk Hfd
    have Hfd3 : fd = Z_to_bv 64 3 := Hfd
    subst fd
    obtain ⟨regs2, G17, G10, G11, G12, G1, G14, Hms2⟩ :=
      tgt_open1_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
        (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        (by regupd_resolve; exact H1) (by regupd_resolve; rfl)
        (by regupd_resolve; exact H15) (by decide)
    exact tfo_msteps target_segs _ _ _ _ Hms2 (Hcont regs2 G17 G10 G11 G12 G1 G14)
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
    (Hcont : ∀ regs2, bv_unsigned (getr regs2 17) = 56 → reg_get regs2 10 = AT_FDCWD →
      reg_get regs2 11 = pdst inp asp → reg_get regs2 12 = Z_to_bv 64 577 →
      reg_get regs2 1 = (0x10011b0 : word) → reg_get regs2 14 = Z_to_bv 64 3 →
      to_fout target_segs (headcp_pending regs2 0x10011f8 (fmem inp asp arnd))
        (with_fds (fd_insert (m_fds (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
          (Z_to_bv 64 3) FdDir)
          (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)) U) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ U o) := by
  have Hsd := (path_eqb_eq _ _).mp Hsdot
  have Hlen : (src inp).length ≤ 4095 := by rw [Hsd]; decide
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps target_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011d8 rfl
  apply tgt_open_dot_rd_rec _ _ _ _
    (fun _ o => o = (Z_to_bv 64 3, inp.in_fs)) (fun _ => U) _ H17 H10 H12
    (by rw [H11, ← Hsd]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen)
    rfl rfl
  · intro e He
    obtain ⟨He1, He2⟩ := openat_errno_range e He
    apply tgt_exit3
    · regupd_resolve; exact H1
    · regupd_resolve; rfl
    · exact c_lts_errno e He1 He2
    · rfl
  · intro fd Hlk Hfd
    have Hfd3 : fd = Z_to_bv 64 3 := Hfd
    subst fd
    obtain ⟨regs2, G17, G10, G11, G12, G1, G14, Hms2⟩ :=
      tgt_open1_to_open2 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
        (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        (by regupd_resolve; exact H1) (by regupd_resolve; rfl)
        (by regupd_resolve; exact H15) (by decide)
    exact tfo_msteps target_segs _ _ _ _ Hms2 (Hcont regs2 G17 G10 G11 G12 G1 G14)
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
    (G1 : reg_get regs2 1 = (0x10011b0 : word))
    (G14 : reg_get regs2 14 = Z_to_bv 64 3)
    (G17 : bv_unsigned (getr regs2 17) = 56) (G10 : reg_get regs2 10 = AT_FDCWD)
    (G11 : reg_get regs2 11 = pdst inp asp) (G12 : reg_get regs2 12 = Z_to_bv 64 577)
    (Hcont : ∀ regs3, bv_unsigned (getr regs3 17) = 63 →
      reg_get regs3 10 = Z_to_bv 64 3 → reg_get regs3 11 = tbuf →
      reg_get regs3 12 = Z_to_bv 64 128 → reg_get regs3 1 = (0x10011b0 : word) →
      reg_get regs3 13 = Z_to_bv 64 4 → reg_get regs3 14 = Z_to_bv 64 3 →
      to_fout target_segs (headcp_pending regs3 0x1001218 (fmem inp asp arnd))
        (with_fds (fd_insert (fd_insert (m_fds (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
          (Z_to_bv 64 3) entry) (Z_to_bv 64 4) (FdFileW (dst inp) (Z_to_bv 64 0)))
          (with_fs (fs_set inp.in_fs (dst inp) [])
            (with_fds (fd_insert (m_fds (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
              (Z_to_bv 64 3) entry)
              (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)))) U) :
    to_fout target_segs (headcp_pending regs2 0x10011f8 (fmem inp asp arnd))
      (with_fds (fd_insert (m_fds (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
        (Z_to_bv 64 3) entry)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
      (fun o => o = (Z_to_bv 64 4, inp.in_fs) ∨ (fs_under inp.in_fs (dst inp) = false ∧ U o)) := by
  cases Hun : fs_under inp.in_fs (dst inp) with
  | true =>
    apply tfo_open_wr_isdir_rec target_segs _ _ _ (with_fds (fd_insert (m_fds (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
        (Z_to_bv 64 3) entry)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)) (dst inp) _ G17 G10 G12
      (by rw [G11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen)
      Hdne Hdst_nodot Hun rfl rfl
    apply tfo_equiv target_segs _ _ (fun o => o = (Z_to_bv 64 4, inp.in_fs))
    · apply tgt_exit4
      · regupd_resolve; exact G1
      · regupd_resolve; rfl
      · exact c_lts_errno EISDIR (by decide) (by decide)
      · rfl
    · intro o; simp only [Bool.true_eq_false, false_and, or_false]
  | false =>
    apply tfo_open_wr_rec target_segs _ _ _ (with_fds (fd_insert (m_fds (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
        (Z_to_bv 64 3) entry)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)) (dst inp)
      (fun _ o => o = (Z_to_bv 64 4, inp.in_fs)) (fun _ => U) _ G17 G10 G12
      (by rw [G11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen)
      Hdne Hdst_nodot Hun rfl rfl
    · intro e He
      obtain ⟨He1, He2⟩ := openat_errno_range e He
      apply tgt_exit4
      · regupd_resolve; exact G1
      · regupd_resolve; rfl
      · exact c_lts_errno e He1 He2
      · rfl
    · intro fd2 Hlk Hfd
      have Hfd4 : fd2 = Z_to_bv 64 4 := Hfd
      subst fd2
      obtain ⟨regs3, K17, K10, K11, K12, K1, K13, K14, Hms3⟩ :=
        tgt_open2_to_read (regupd regs2 10 (Z_to_bv 64 4)) (fmem inp asp arnd)
          (Z_to_bv 64 3) (Z_to_bv 64 4)
          (by regupd_resolve; exact G1) (by regupd_resolve; rfl)
          (by regupd_resolve; exact G14) (by decide)
      exact tfo_msteps target_segs _ _ _ _ Hms3 (Hcont regs3 K17 K10 K11 K12 K1 K13 K14)
    · intro o
      constructor
      · rintro (H | ⟨_, H⟩)
        · exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, H⟩
        · exact Or.inr ⟨Z_to_bv 64 4, rfl, rfl, H⟩
      · rintro (⟨e, _, H⟩ | ⟨fd, _, _, H⟩)
        · exact Or.inl H
        · exact Or.inr ⟨rfl, H⟩

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_absent (Hsrc_nodot : openat_plain_name (src inp) = true)
    (Hlen : (src inp).length ≤ 4095) (Hnone : fs_lookup inp.in_fs (src inp) = none) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (hc_outcomes inp.in_fs (src inp) (dst inp)) := by
  apply tfo_equiv target_segs _ _ (fun o => o = (Z_to_bv 64 3, inp.in_fs))
  · obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
      target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
    apply tfo_msteps target_segs _ _ _ _ Hms
    apply to_fout.tfo_step _ _ _ _ rfl
    · exact step_ecall _ _ _ _ _ _ TF_10011d8 rfl
    apply tfo_open_enoent_rec target_segs _ _ _
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) (src inp) _ H17 H10 H12
      (by rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen)
      Hsrc_nodot Hnone rfl rfl
    apply tgt_exit3
    · regupd_resolve; exact H1
    · regupd_resolve; rfl
    · exact c_lts_errno ENOENT (by decide) (by decide)
    · rfl
  · intro o; simp only [hc_outcomes, Hnone]

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_empty (Hlen : (src inp).length ≤ 4095) (Hse : path_eqb (src inp) [] = true) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps target_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011d8 rfl
  apply tgt_open_empty_rec _ _ _ _ (src inp) _ H17 (by rw [H12]; decide) H10
    (by rw [H11]; exact target_cstr_src inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen) Hse rfl rfl
  apply tgt_exit3
  · regupd_resolve; exact H1
  · regupd_resolve; rfl
  · exact c_lts_errno ENOENT (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_present_dst_empty (Hsrc_nodot : openat_plain_name (src inp) = true)
    (d0 : List byte) (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : (dst inp).length ≤ 4095)
    (Hsne : path_eqb (src inp) [] = false) (Hde : path_eqb (dst inp) [] = true)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_file inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
  intro regs2 G17 G10 G11 G12 G1 G14
  apply tgt_open_empty_rec _ _ _ _ (dst inp) _ G17 (by rw [G12]; decide) G10
    (by rw [G11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2) Hde rfl rfl
  apply tgt_exit4
  · regupd_resolve; exact G1
  · regupd_resolve; rfl
  · exact c_lts_errno ENOENT (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_dst_dot (Hsrc_nodot : openat_plain_name (src inp) = true)
    (d0 : List byte) (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : (dst inp).length ≤ 4095)
    (Hsne : path_eqb (src inp) [] = false) (Hddot : path_eqb (dst inp) dot_path = true)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_file inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
  intro regs2 G17 G10 G11 G12 G1 G14
  apply tgt_open_dot_wr_eisdir _ _ _ _ _ G17 G10 G12
    (by rw [G11, ← (path_eqb_eq _ _).mp Hddot]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply tgt_exit4
  · regupd_resolve; exact G1
  · regupd_resolve; rfl
  · exact c_lts_errno EISDIR (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_toolong (Hlen : 4096 ≤ (src inp).length) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs)) := by
  obtain ⟨regs1, H1, H15, H17, H10, H11, H12, Hms⟩ :=
    target_to_open1 inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3
  apply tfo_msteps target_segs _ _ _ _ Hms
  apply to_fout.tfo_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011d8 rfl
  apply tfo_open_toolong_rec target_segs _ _ _ _ _ H17 (by rw [H12]; decide)
    (by rw [H11]; exact target_cstr_src_toolong inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen) rfl rfl
  apply tgt_exit3
  · regupd_resolve; exact H1
  · regupd_resolve; rfl
  · exact c_lts_errno ENAMETOOLONG (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_present_dst_toolong (Hsrc_nodot : openat_plain_name (src inp) = true)
    (d0 : List byte) (Hlen1 : (src inp).length ≤ 4095)
    (Hlen2 : 4096 ≤ (dst inp).length)
    (Hsne : path_eqb (src inp) [] = false)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_file inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
  intro regs2 G17 G10 G11 G12 G1 G14
  apply tfo_open_toolong_rec target_segs _ _ _ _ _ G17 (by rw [G12]; decide)
    (by rw [G11]; exact target_cstr_dst_toolong inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply tgt_exit4
  · regupd_resolve; exact G1
  · regupd_resolve; rfl
  · exact c_lts_errno ENAMETOOLONG (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot_dstempty
    (Hlen2 : (dst inp).length ≤ 4095) (Hsdot : path_eqb (src inp) dot_path = true) (Hde : path_eqb (dst inp) [] = true) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_dir inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 _ Hsdot
  intro regs2 G17 G10 G11 G12 G1 G14
  apply tgt_open_empty_rec _ _ _ _ (dst inp) _ G17 (by rw [G12]; decide) G10
    (by rw [G11]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2) Hde rfl rfl
  apply tgt_exit4
  · regupd_resolve; exact G1
  · regupd_resolve; rfl
  · exact c_lts_errno ENOENT (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot_dstdot
    (Hlen2 : (dst inp).length ≤ 4095) (Hsdot : path_eqb (src inp) dot_path = true) (Hddot : path_eqb (dst inp) dot_path = true) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_dir inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 _ Hsdot
  intro regs2 G17 G10 G11 G12 G1 G14
  apply tgt_open_dot_wr_eisdir _ _ _ _ _ G17 G10 G12
    (by rw [G11, ← (path_eqb_eq _ _).mp Hddot]; exact target_cstr_dst inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply tgt_exit4
  · regupd_resolve; exact G1
  · regupd_resolve; rfl
  · exact c_lts_errno EISDIR (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot_dst_toolong
    (Hlen2 : 4096 ≤ (dst inp).length) (Hsdot : path_eqb (src inp) dot_path = true) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs)) := by
  apply headcp_first_dir inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 _ Hsdot
  intro regs2 G17 G10 G11 G12 G1 G14
  apply tfo_open_toolong_rec target_segs _ _ _ _ _ G17 (by rw [G12]; decide)
    (by rw [G11]; exact target_cstr_dst_toolong inp Hva Hve asp arnd Hsp_lo Hsp_hi Hge3 Hlen2) rfl rfl
  apply tgt_exit4
  · regupd_resolve; exact G1
  · regupd_resolve; rfl
  · exact c_lts_errno ENAMETOOLONG (by decide) (by decide)
  · rfl

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_present (Hsrc_nodot : openat_plain_name (src inp) = true)
    (Hdst_nodot : openat_plain_name (dst inp) = true) (d0 : List byte)
    (Hlen1 : (src inp).length ≤ 4095) (Hlen2 : (dst inp).length ≤ 4095)
    (Hsne : path_eqb (src inp) [] = false) (Hdne : path_eqb (dst inp) [] = false)
    (Hsome : fs_lookup inp.in_fs (src inp) = some d0) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (hc_outcomes inp.in_fs (src inp) (dst inp)) := by
  let chunk := file_read (hc_data inp.in_fs (src inp) (dst inp)) (Z_to_bv 64 0) (Z_to_bv 64 128)
  let Nc := len_word chunk
  have Hclen : chunk.length ≤ 128 := hc_chunk_le _
  have HNc : bv_unsigned Nc = (chunk.length : Int) := u_len_word chunk (by omega)
  let mr := write_to_mem (fmem inp asp arnd) tbuf chunk
  apply tfo_equiv target_segs _ _
    (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs) ∨
      (fs_under inp.in_fs (dst inp) = false ∧ o = (Z_to_bv 64 0, hc_final_fs inp.in_fs (src inp) (dst inp))))
  · apply headcp_first_file inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 d0 _ Hsrc_nodot Hlen1 Hsne Hsome
    intro regs2 G17 G10 G11 G12 G1 G14
    apply headcp_second_file inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3
      (FdFile (src inp) (Z_to_bv 64 0)) regs2
      (fun o => o = (Z_to_bv 64 0, hc_final_fs inp.in_fs (src inp) (dst inp)))
      Hlen2 Hdne Hdst_nodot G1 G14 G17 G10 G11 G12
    intro regs3 K17 K10 K11 K12 K1 K13 K14
    refine tfo_read_rec target_segs regs3 0x1001218 (fmem inp asp arnd) trom _
      (Z_to_bv 64 3) (src inp) (Z_to_bv 64 0) (hc_data inp.in_fs (src inp) (dst inp))
      tbuf (Z_to_bv 64 128) _ K17 K10 K11 K12 ?_ rfl ?_ headcp_buf_wseg
      (by decide) (by decide) (by decide) rfl rfl ?_
    · rfl
    · exact hc_data_lookup inp.in_fs (src inp) (dst inp) d0 Hsome
    obtain ⟨regs4, L17, L10, L11, L12, L1, L13, L14, Hms4⟩ :=
      tgt_read_to_write (regupd regs3 10 Nc) mr (Z_to_bv 64 3) (Z_to_bv 64 4) Nc
        (by regupd_resolve; exact K1) (by regupd_resolve; rfl)
        (by regupd_resolve; exact K11) (by regupd_resolve; exact K13)
        (by regupd_resolve; exact K14) (by rw [HNc]; omega)
    apply tfo_msteps target_segs _ _ _ _ Hms4
    refine tfo_write_rec target_segs regs4 0x100122c mr _ (Z_to_bv 64 4)
      (dst inp) (Z_to_bv 64 0) [] chunk tbuf Nc _ L17 L10 L11 L12
      ?_ rfl ?_ ?_ ?_ ?_ ?_ rfl rfl ?_
    · rfl
    · have Hnat : word_to_nat Nc = chunk.length := by
        unfold word_to_nat; unfold bv_unsigned at HNc; omega
      rw [Hnat]
      apply rdn_write_to_mem; rw [u_tbuf]; omega
    · rw [HNc]; unfold rw_bytes_max; omega
    · exact fs_lookup_set_eq _ _ _
    · apply file_gap_in_range; decide
    · left
      apply access_okb_intro
      rw [u_tbuf, HNc]
      unfold TASK_SIZE
      omega
    obtain ⟨regs5, M17, M10, M1, M13, Hms5⟩ :=
      tgt_write_to_close (regupd regs4 10 Nc) mr (Z_to_bv 64 3) (Z_to_bv 64 4) Nc
        (by regupd_resolve; exact L1) (by regupd_resolve; rfl)
        (by regupd_resolve; exact L13) (by regupd_resolve; exact L14)
        (by rw [HNc]; omega)
    apply tfo_msteps target_segs _ _ _ _ Hms5
    refine tfo_close_rec target_segs _ _ _ _ _ (Z_to_bv 64 3)
      (FdFile (src inp) (Z_to_bv 64 0 + Nc)) _ M17 M10 ?_ rfl rfl rfl ?_
    · rfl
    obtain ⟨regs6, N17, N10, N1, Hms6⟩ :=
      tgt_close_to_close (regupd regs5 10 (Z_to_bv 64 0)) mr (Z_to_bv 64 4)
        (by regupd_resolve; exact M1) (by regupd_resolve; exact M13)
    apply tfo_msteps target_segs _ _ _ _ Hms6
    refine tfo_close_rec target_segs _ _ _ _ _ (Z_to_bv 64 4)
      (FdFileW (dst inp) (Z_to_bv 64 0 + Nc)) _ N17 N10 ?_ rfl rfl rfl ?_
    · rfl
    apply tgt_exit0
    · regupd_resolve; exact N1
    · exact hc_final_collapse inp.in_fs (src inp) (dst inp)
  · intro o; simp only [hc_outcomes, Hsome]

include Hva Hve Hsp_lo Hsp_hi Hge3 in
theorem target_src_dot (Hlen2 : (dst inp).length ≤ 4095) (Hsdot : path_eqb (src inp) dot_path = true)
    (Hdne : path_eqb (dst inp) [] = false) (Hddot : openat_plain_name (dst inp) = true) :
    to_fout target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      (fun o => o = (Z_to_bv 64 3, inp.in_fs) ∨ o = (Z_to_bv 64 4, inp.in_fs) ∨
        (fs_under inp.in_fs (dst inp) = false ∧ o = (Z_to_bv 64 5, fs_set inp.in_fs (dst inp) []))) := by
  apply headcp_first_dir inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 _ Hsdot
  intro regs2 G17 G10 G11 G12 G1 G14
  apply headcp_second_file inp Hva Hve asp arnd Hsp_lo Hsp_hi abrk amb Hge3 FdDir regs2
    (fun o => o = (Z_to_bv 64 5, fs_set inp.in_fs (dst inp) [])) Hlen2 Hdne Hddot
    G1 G14 G17 G10 G11 G12
  intro regs3 K17 K10 K11 K12 K1 K13 K14
  refine tgt_read_dir_eisdir regs3 0x1001218 (fmem inp asp arnd) _ (Z_to_bv 64 3) _
    K17 K10 ?_ rfl ?_ rfl rfl ?_
  · rfl
  · rw [K11, K12]; decide
  apply tgt_exit5
  · regupd_resolve; exact K1
  · regupd_resolve; rfl
  · exact c_lts_errno EISDIR (by decide) (by decide)
  · rfl

end Ge3

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_lt3 (Hlt3 : inp.in_argv.length < 3) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      [] (Z_to_bv 64 2) := by
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have HargcLe := valid_argv_len inp.in_argv Hva
  have Hu := u_argcN inp Hva
  have Hnat : (argcN inp).toNat = inp.in_argv.length := by
    unfold bv_unsigned at Hu
    omega
  have Hbr : (!bv_ltu (Z_to_bv 64 2) (argcN inp)) = true := by
    change (!decide (2 < (argcN inp).toNat)) = true
    rw [Hnat]
    simp only [show ¬ 2 < inp.in_argv.length by omega,
      decide_false, Bool.not_false]
  rw [init_mkst]
  sym_block target_segs 20 [true] [EVar 33] [(2, EVar 32)]
    [asp] [argcN inp] R HR
  all_goals repeat' apply And.intro
  all_goals try (solve
    | exact Hbr
    | (apply store_ok_wrap_window
       all_goals try rw [stack_max_size_val]
       all_goals u_norm; omega)
    | (refine ⟨word_le8 (argcN inp), ?_, bytes_le_n_to_le_8 _⟩
       change rdn target_segs (wmem inp asp arnd) (v_addi asp 0) 8 = _
       rw [v_addi_0]
       exact read_argc_w inp Hva Hve asp arnd Hsp_hi)
    | (change (!c_ltu (Z_to_bv 64 2) (argcN inp)) = true
       rw [c_ltu_ltb, Bool.not_eq_true, decide_eq_false_iff_not]
       u_norm; omega)
    | (u_norm; omega))
  all_goals try (solve | headcp_eq_goal; getr_resolve; regupd_resolve; rfl)
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011b4 rfl
  apply tw_exit_coden
  · headcp_out HR
  · headcp_out HR
  · decide

end TargetProof
end LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_target
