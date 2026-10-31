import LinuxProcessSemantics.Common.FileSim.Base
import LinuxProcessSemantics.Common.FileSim.Decode
import LinuxProcessSemantics.Common.FileSim.Algebra

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Ports the open nodes at Rocq lines 1389–1590 and 2085–2336.
The flag-mask spelling follows `Decode.lean`; `segs` is explicit first.
-/

namespace LinuxProcessSemantics.Common.FileSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.State.FdEntry
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.Common.PropExec

theorem tfo_open_core (segs : List Segment) (ms : machine_state) (model : Model)
    (mk : word → Model) (x8 : word) (reads : List (word × Nat))
    (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop)
    (U : (word × Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      check_open_result_copyins reads eff model mk)
    (Hmk : ∀ fd, m_halted (mk fd) = none ∧ m_vm_lazy (mk fd) = [])
    (Herr : ∀ e, e ∈ openat_errnos →
      to_fout segs (advance_past_svc (apply_effect ms
        (with_copyins reads (mkEffect (errno_ret e) [] [])))) model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout segs (advance_past_svc (apply_effect ms
        (with_copyins reads (mkEffect fd [] [])))) (mk fd) (Ts fd))
    (HU : ∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) :
    to_fout segs ms model U := by
  have Hmem : check_syscall (sys_input segs ms x8)
      (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])) model = CheckOk model [] := by
    rw [Hchk, check_open_result_copyins_ok_iff]
    exact Or.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, rfl, rfl, rfl⟩
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    cases Hfind : lookup_ca checked_table (bv_unsigned (sys_input segs ms x8).in_sysno) with
    | none => rw [check_syscall_of_none _ _ _ Hfind] at Hmem; cases Hmem
    | some c => exact lookups_agree_at_of_found _ c Hfind
  have Hspec : ∀ eff m evs, syscall_spec (sys_input segs ms x8) model (Ok eff m evs) ↔
      ((∃ e, e ∈ openat_errnos ∧ eff = with_copyins reads (mkEffect (errno_ret e) [] []) ∧
          m = model ∧ evs = []) ∨
       (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧
          eff = with_copyins reads (mkEffect fd [] []) ∧ m = mk fd ∧ evs = [])) := by
    intro eff m evs
    rw [← check_syscall_ok_iff _ _ _ _ _ Hagree, Hchk, check_open_result_copyins_ok_iff]
  refine to_fout.tfo_sys ms model x8
    (fun eff _ => if addr_is_error_b eff.eff_ret then
      Te (two_pow_64 - bv_unsigned eff.eff_ret) else Ts eff.eff_ret) U Hsvc ?_ ?_ ?_ ?_ ?_
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_open_result_copyins_never_unmodeled _ _ _ _ H
  · exact ⟨_, model, [], check_syscall_sound_ok _ _ _ _ _ Hmem⟩
  · intro eff m evs Hs
    rcases (Hspec eff m evs).mp Hs with
      ⟨e, _, rfl, rfl, rfl⟩ | ⟨fd, _, _, rfl, rfl, rfl⟩
    · exact ⟨rfl, Hh, Hlazy⟩
    · exact ⟨rfl, Hmk fd⟩
  · intro eff m evs Hs
    rcases (Hspec eff m evs).mp Hs with
      ⟨e, HIn, rfl, rfl, _⟩ | ⟨fd, Hlk, Heq, rfl, rfl, _⟩
    · obtain ⟨H1, H2⟩ := openat_errno_range e HIn
      simpa only [with_copyins, mkEffect, errno_ret_error_b e H1 H2,
        ↓reduceIte, errno_ret_recover e H1 H2] using Herr e HIn
    · have Hne : addr_is_error_b fd = false := by rw [Heq]; exact alloc_fd_not_error_b _
      simpa only [with_copyins, mkEffect, Hne, Bool.false_eq_true, ↓reduceIte] using Hok fd Hlk Heq
  · intro o
    rw [HU]
    constructor
    · rintro (⟨e, HIn, Ht⟩ | ⟨fd, Hlk, Heq, Ht⟩)
      · refine ⟨_, model, [], (Hspec _ _ _).mpr (Or.inl ⟨e, HIn, rfl, rfl, rfl⟩), ?_⟩
        obtain ⟨H1, H2⟩ := openat_errno_range e HIn
        simpa only [with_copyins, mkEffect, errno_ret_error_b e H1 H2,
          ↓reduceIte, errno_ret_recover e H1 H2] using Ht
      · refine ⟨_, mk fd, [], (Hspec _ _ _).mpr (Or.inr ⟨fd, Hlk, Heq, rfl, rfl, rfl⟩), ?_⟩
        have Hne : addr_is_error_b fd = false := by rw [Heq]; exact alloc_fd_not_error_b _
        simpa only [with_copyins, mkEffect, Hne, Bool.false_eq_true, ↓reduceIte] using Ht
    · rintro ⟨eff, m, evs, Hs, Ht⟩
      rcases (Hspec eff m evs).mp Hs with
        ⟨e, HIn, rfl, rfl, _⟩ | ⟨fd, Hlk, Heq, rfl, rfl, _⟩
      · obtain ⟨H1, H2⟩ := openat_errno_range e HIn
        refine Or.inl ⟨e, HIn, ?_⟩
        simpa only [with_copyins, mkEffect, errno_ret_error_b e H1 H2,
          ↓reduceIte, errno_ret_recover e H1 H2] using Ht
      · have Hne : addr_is_error_b fd = false := by rw [Heq]; exact alloc_fd_not_error_b _
        refine Or.inr ⟨fd, Hlk, Heq, ?_⟩
        simpa only [with_copyins, mkEffect, Hne, Bool.false_eq_true, ↓reduceIte] using Ht

theorem open_ok_fd (segs : List Segment) (ms : machine_state) (model : Model)
    (mk : word → Model) (x8 : word) (reads : List (word × Nat)) (fd : word)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      check_open_result_copyins reads eff model mk)
    (Hlk : fd_lookup (m_fds model) fd = none) (Heq : fd = alloc_fd (m_fds model)) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (with_copyins reads (mkEffect fd [] [])) (mk fd) []) := by
  apply check_syscall_sound_ok
  rw [Hchk, check_open_result_copyins_ok_iff]
  exact Or.inr ⟨fd, Hlk, Heq, rfl, rfl, rfl⟩

theorem tfo_openat_toolong (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (U : (word × Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 56)
    (Hfl : modeled_open_flags (ms_gpr ms 2) = true)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
      (with_copyins (open_copyins ms) (mkEffect (errno_ret ENAMETOOLONG) [] [])))) model U) :
    to_fout segs ms model U := by
  have Hchk := openat_toolong_check segs ms x8 model Hno Hfl Hpath
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_openat
  refine tfo_sys_det segs ms model x8 _ model U Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
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

theorem tfo_openat_enoent (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : path) (U : (word × Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 56)
    (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = 0)
    (Hdot : openat_plain_name p = true) (Hfs : fs_lookup (m_fs model) p = none)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
      (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] [])))) model U) :
    to_fout segs ms model U := by
  have Hunw := openat_plain_name_noslash p Hdot
  have Hdir := openat_plain_name_nodirref p Hdot
  have Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [] := by
    intro eff
    rw [check_syscall_56 segs ms x8 eff model Hno]
    simp only [check_openat, modeled_open_flags_rd _ Hfl, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, check_openat_body, in_mem_si, Hpath]
    cases Hpe : path_eqb p [] with
    | true =>
      simp only [↓reduceIte]
      exact check_copyins_after_ret_only _ _ _ _ _
    | false =>
      have Hfd : bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true := by decide
      simp only [Bool.false_eq_true, ↓reduceIte, Hdirfd, Hfd, Bool.not_true,
        check_openat_resolved, Hunw, Hfl, beq_self_eq_true, check_openat_read, Hdir, Hfs]
      exact check_copyins_after_ret_only _ _ _ _ _
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_openat
  refine tfo_sys_det segs ms model x8 _ model U Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
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

theorem tfo_open_enoent_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model) (p : path)
    (U : (word × Fs) → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 0)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p)
    (Hdot : openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = none)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs)) model U) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
      model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  refine tfo_openat_enoent segs ms model (getr regs 17) p U rfl H17 H10 Hpath
    ?_ Hdot Hfs Hh Hlazy ?_
  · change bv_unsigned (bv_and (reg_get regs 12) (bv_not (Z_to_bv 64 open_ignored_flags))) = 0
    rw [H12]
    decide
  · simpa only [ms, adv_eff_ret_copyins] using Hcont

theorem tfo_open_rd_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model) (p : path) (d : List byte)
    (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop)
    (U : (word × Fs) → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 0)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = some d)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ openat_errnos →
      to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs))
        model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
        (with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model) (Ts fd))
    (HU : ∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
      model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  refine tfo_open_core segs ms model (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)
    (getr regs 17) (open_copyins ms) Te Ts U rfl Hh Hlazy ?_ ?_ ?_ ?_ HU
  · intro eff
    apply openat_rd_check segs ms (getr regs 17) model p d H17 H10 Hpath Hpe
      ?_ Hdot Hfs eff
    change bv_unsigned (bv_and (reg_get regs 12) (bv_not (Z_to_bv 64 open_ignored_flags))) = 0
    rw [H12]
    decide
  · intro fd
    exact ⟨Hh, Hlazy⟩
  · intro e HIn
    simpa only [ms, adv_eff_ret_copyins] using Herr e HIn
  · intro fd Hlk Heq
    simpa only [ms, adv_eff_ret_copyins] using Hok fd Hlk Heq

theorem tfo_open_wr_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model) (p : path)
    (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop)
    (U : (word × Fs) → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 577)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : openat_plain_name p = true)
    (Hun : fs_under (m_fs model) p = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ openat_errnos →
      to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs))
        model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
        (with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
        (with_fs (fs_set (m_fs model) p []) model)) (Ts fd))
    (HU : ∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
      model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  refine tfo_open_core segs ms model (fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
        (with_fs (fs_set (m_fs model) p []) model))
    (getr regs 17) (open_copyins ms) Te Ts U rfl Hh Hlazy ?_ ?_ ?_ ?_ HU
  · intro eff
    apply openat_wr_check segs ms (getr regs 17) model p H17 H10 Hpath Hpe
      ?_ Hdot Hun eff
    change bv_unsigned (bv_and (reg_get regs 12) (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags
    rw [H12]
    decide
  · intro fd
    exact ⟨Hh, Hlazy⟩
  · intro e HIn
    simpa only [ms, adv_eff_ret_copyins] using Herr e HIn
  · intro fd Hlk Heq
    simpa only [ms, adv_eff_ret_copyins] using Hok fd Hlk Heq

theorem tfo_open_wr_isdir_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model) (p : path)
    (U : (word × Fs) → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 577)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : openat_plain_name p = true)
    (Hun : fs_under (m_fs model) p = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model U) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
      model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  have Hchk : ∀ eff, check_syscall (sys_input segs ms (getr regs 17)) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model [] := by
    intro eff
    apply openat_wr_isdir_check segs ms (getr regs 17) model p H17 H10 Hpath Hpe
      ?_ Hdot Hun eff
    change bv_unsigned (bv_and (reg_get regs 12) (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags
    rw [H12]
    decide
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms (getr regs 17)).in_sysno) := by
    rw [in_sysno_si, H17]
    exact lookups_agree_at_of_found _ _ lookup_ca_checked_table_openat
  refine tfo_sys_det segs ms model (getr regs 17)
    (with_copyins (open_copyins ms) (mkEffect (errno_ret EISDIR) [] [])) model U
    rfl ?_ ?_ ?_ Hh Hlazy ?_
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

theorem tfo_open_toolong_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model)
    (U : (word × Fs) → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (Hfl : modeled_open_flags (reg_get regs 12) = true)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = CstrTooLong)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem (seg_rom segs)) model U) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
      model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  refine tfo_openat_toolong segs ms model (getr regs 17) U rfl H17 ?_ ?_ Hh Hlazy ?_
  · exact Hfl
  · exact Hpath
  · simpa only [ms, adv_eff_ret_copyins] using Hcont

end LinuxProcessSemantics.Common.FileSim
