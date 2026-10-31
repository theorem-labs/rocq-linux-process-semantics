import LinuxProcessSemantics.Common.FileSim.Base
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # Common.FileSim — syscall decoding through the verified checker

TRUST BOUNDARY: shared proof library, not the trusted specification.
Image-INDEPENDENT.

This part ports Rocq lines 1028–1383. It needs no lemmas from FileSim's
Algebra or Tree ranges. Syscall-input lemmas take `segs` explicitly first.
As in `Sys.Fs.Open`, Rocq's `Z.ldiff` flag residue is spelled
`bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))`.
-/

namespace LinuxProcessSemantics.Common.FileSim

open LinuxProcessSemantics.Riscv.Prelude
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
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.Common.PropExec

/-! ## Dispatch -/

theorem check_syscall_56 (segs : List Segment) (ms : machine_state)
    (x8 : word) (eff : SyscallEffect) (m : Model) (Hno : bv_unsigned x8 = 56) :
    check_syscall (sys_input segs ms x8) eff m =
      check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m := by
  unfold check_syscall check_syscall_in
  rw [in_sysno_si, Hno]
  rfl

theorem check_syscall_57 (segs : List Segment) (ms : machine_state)
    (x8 : word) (eff : SyscallEffect) (m : Model) (Hno : bv_unsigned x8 = 57) :
    check_syscall (sys_input segs ms x8) eff m =
      check_close (fd32 (ms_gpr ms 0)) eff m := by
  unfold check_syscall check_syscall_in
  rw [in_sysno_si, Hno]
  rfl

theorem check_syscall_63 (segs : List Segment) (ms : machine_state)
    (x8 : word) (eff : SyscallEffect) (m : Model) (Hno : bv_unsigned x8 = 63) :
    check_syscall (sys_input segs ms x8) eff m =
      check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m := by
  unfold check_syscall check_syscall_in
  rw [in_sysno_si, Hno]
  rfl

theorem check_syscall_64 (segs : List Segment) (ms : machine_state)
    (x8 : word) (eff : SyscallEffect) (m : Model) (Hno : bv_unsigned x8 = 64) :
    check_syscall (sys_input segs ms x8) eff m =
      check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m := by
  unfold check_syscall check_syscall_in
  rw [in_sysno_si, Hno]
  rfl

/-! ## Open-result algebra -/

theorem fd_not_error (fd : word) (H : bv_unsigned fd < 2 ^ 31) :
    addr_is_error_b fd = false := by
  unfold addr_is_error_b two_pow_64
  exact decide_eq_false (by omega)

theorem errno_ret_recover (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    two_pow_64 - bv_unsigned (errno_ret e) = e := by
  rw [errno_ret_unsigned e H1 H2]
  omega

theorem ENOMEM_in_openat_errnos : ENOMEM ∈ openat_errnos := by decide

theorem openat_errno_range (e : Int) (HIn : e ∈ openat_errnos) :
    1 ≤ e ∧ e ≤ 4095 :=
  errnos_ok_range openat_errnos e openat_errnos_ok HIn

theorem check_open_result_never_unmodeled (eff : SyscallEffect) (m : Model)
    (mk : word → Model) : check_open_result eff m mk ≠ CheckUnmodeled :=
  check_new_fd_result_no_unmodeled openat_errnos eff m mk

theorem check_open_result_ok_iff (eff : SyscallEffect) (m : Model)
    (mk : word → Model) (m' : Model) (evs : List event) :
    check_open_result eff m mk = CheckOk m' evs ↔
      ((∃ e, e ∈ openat_errnos ∧ eff = mkEffect (errno_ret e) [] [] ∧
          m' = m ∧ evs = []) ∨
       (∃ fd, fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m) ∧
          eff = mkEffect fd [] [] ∧ m' = mk fd ∧ evs = [])) := by
  constructor
  · intro H
    obtain ⟨rfl, ret, rfl, Hret⟩ := check_new_fd_result_ok_inv openat_errnos eff m mk m' evs H
    rcases Hret with ⟨Herr, rfl⟩ | ⟨Hlk, Heq, rfl⟩
    · obtain ⟨e, HIn, rfl⟩ := (errno_ret_in_true openat_errnos ret).mp Herr
      exact Or.inl ⟨e, HIn, rfl, rfl, rfl⟩
    · exact Or.inr ⟨ret, Hlk, Heq, rfl, rfl, rfl⟩
  · rintro (⟨e, HIn, rfl, rfl, rfl⟩ | ⟨fd, Hlk, Heq, rfl, rfl, rfl⟩)
    · simp only [check_open_result, check_new_fd_result,
        errno_ret_in_intro _ e HIn, ↓reduceIte]
    · subst fd
      simp only [check_open_result, check_new_fd_result,
        errno_ret_in_alloc_fd _ _ openat_errnos_ok, Bool.false_eq_true,
        ↓reduceIte, Hlk, bv_eqb_refl]

def open_copyins (ms : machine_state) : List (word × Nat) :=
  [(ms_gpr ms 1, cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]

def check_open_result_copyins (reads : List (word × Nat)) (eff : SyscallEffect)
    (m : Model) (mk : word → Model) : check_result :=
  check_copyins reads eff (check_open_result (clear_copyins eff) m mk)

theorem effect_from_copyins_and_clear (eff : SyscallEffect) (reads : List (word × Nat))
    (core : SyscallEffect) (Hreads : eff.eff_copyins = reads)
    (Hcore : clear_copyins eff = core) : eff = with_copyins reads core := by
  subst core
  cases eff
  cases Hreads
  rfl

theorem check_open_result_copyins_never_unmodeled (reads : List (word × Nat))
    (eff : SyscallEffect) (m : Model) (mk : word → Model) :
    check_open_result_copyins reads eff m mk ≠ CheckUnmodeled := by
  unfold check_open_result_copyins check_copyins
  split
  · exact check_open_result_never_unmodeled _ _ _
  · exact check_result.noConfusion

theorem check_open_result_copyins_ok_iff (reads : List (word × Nat))
    (eff : SyscallEffect) (m : Model) (mk : word → Model) (m' : Model) (evs : List event) :
    check_open_result_copyins reads eff m mk = CheckOk m' evs ↔
      ((∃ e, e ∈ openat_errnos ∧
          eff = with_copyins reads (mkEffect (errno_ret e) [] []) ∧ m' = m ∧ evs = []) ∨
       (∃ fd, fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m) ∧
          eff = with_copyins reads (mkEffect fd [] []) ∧ m' = mk fd ∧ evs = [])) := by
  unfold check_open_result_copyins check_copyins
  split
  next Hreads =>
    have Hr := (access_ranges_eqb_eq _ _).mp Hreads
    rw [check_open_result_ok_iff]
    constructor
    · rintro (⟨e, HIn, Hcore, Hm, Hevs⟩ | ⟨fd, Hlk, Heq, Hcore, Hm, Hevs⟩)
      · exact Or.inl ⟨e, HIn, effect_from_copyins_and_clear _ _ _ Hr Hcore, Hm, Hevs⟩
      · exact Or.inr ⟨fd, Hlk, Heq, effect_from_copyins_and_clear _ _ _ Hr Hcore, Hm, Hevs⟩
    · rintro (⟨e, HIn, rfl, Hm, Hevs⟩ | ⟨fd, Hlk, Heq, rfl, Hm, Hevs⟩)
      · exact Or.inl ⟨e, HIn, rfl, Hm, Hevs⟩
      · exact Or.inr ⟨fd, Hlk, Heq, rfl, Hm, Hevs⟩
  next Hreads =>
    constructor
    · intro H; cases H
    · rintro (⟨_, _, rfl, _, _⟩ | ⟨_, _, _, rfl, _, _⟩) <;>
        exact False.elim (Hreads (access_ranges_eqb_refl reads))

theorem check_copyins_after_ret_only (reads : List (word × Nat))
    (eff : SyscallEffect) (r : word) (m : Model) (evs : List event) :
    check_copyins_after reads eff (check_ret_only (clear_copyins eff) r m evs) =
      check_ret_only_copyins reads eff r m evs := by
  unfold check_ret_only_copyins
  cases Hresult : check_ret_only (clear_copyins eff) r m evs with
  | CheckReject => simp [check_copyins_after, check_copyins]
  | CheckOk m' evs' => rfl
  | CheckUnmodeled => exact False.elim (check_ret_only_no_unmodeled _ _ _ _ Hresult)

/-! ## Openat reductions -/

theorem openat_rd_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path) (d : List byte)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = 0)
    (Hdot : openat_plain_name p = true) (Hfs : fs_lookup (m_fs model) p = some d)
    (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model =
      check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model) := by
  have Hunw := openat_plain_name_noslash p Hdot
  have Hdir := openat_plain_name_nodirref p Hdot
  rw [check_syscall_56 segs ms x8 eff model Hno]
  simp only [check_openat, modeled_open_flags_rd _ Hfl, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, check_openat_body, in_mem_si, Hpath, Hpe, Hdirfd]
  have Hfd : bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true := by decide
  simp only [Hfd, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    check_openat_resolved, Hunw, Hfl, beq_self_eq_true, check_openat_read, Hdir, Hfs]
  unfold check_open_result_copyins open_copyins
  cases Hresult : check_open_result (clear_copyins eff) model
    (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model) with
  | CheckReject => rfl
  | CheckOk m evs => rfl
  | CheckUnmodeled => exact False.elim (check_open_result_never_unmodeled _ _ _ Hresult)

theorem openat_wr_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags)
    (Hdot : openat_plain_name p = true) (Hun : fs_under (m_fs model) p = false)
    (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model =
      check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
          (with_fs (fs_set (m_fs model) p []) model)) := by
  have Hunw := openat_plain_name_noslash p Hdot
  have Hdir := openat_plain_name_nodirref p Hdot
  rw [check_syscall_56 segs ms x8 eff model Hno]
  simp only [check_openat, modeled_open_flags_wr _ Hfl, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, check_openat_body, in_mem_si, Hpath, Hpe, Hdirfd]
  have Hfd : bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true := by decide
  have Hwr : (wr_create_flags == (0 : Int)) = false := by decide
  simp only [Hfd, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    check_openat_resolved, Hunw, Hfl, Hwr, beq_self_eq_true,
    check_openat_create, Hdir, Hun, Bool.false_or, check_create_wronly]
  unfold check_open_result_copyins open_copyins
  cases Hresult : check_open_result (clear_copyins eff) model
    (fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
      (with_fs (fs_set (m_fs model) p []) model)) with
  | CheckReject => rfl
  | CheckOk m evs => rfl
  | CheckUnmodeled => exact False.elim (check_open_result_never_unmodeled _ _ _ Hresult)

theorem openat_wr_isdir_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags)
    (Hdot : openat_plain_name p = true) (Hun : fs_under (m_fs model) p = true)
    (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model [] := by
  have Hunw := openat_plain_name_noslash p Hdot
  have Hdir := openat_plain_name_nodirref p Hdot
  rw [check_syscall_56 segs ms x8 eff model Hno]
  simp only [check_openat, modeled_open_flags_wr _ Hfl, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, check_openat_body, in_mem_si, Hpath, Hpe, Hdirfd]
  have Hfd : bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true := by decide
  have Hwr : (wr_create_flags == (0 : Int)) = false := by decide
  simp only [Hfd, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    check_openat_resolved, Hunw, Hfl, Hwr, beq_self_eq_true,
    check_openat_create, Hdir, Hun, Bool.false_or]
  exact check_copyins_after_ret_only (open_copyins ms) eff (errno_ret EISDIR) model []

theorem openat_toolong_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (Hno : bv_unsigned x8 = 56)
    (Hfl : modeled_open_flags (ms_gpr ms 2) = true)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong)
    (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret ENAMETOOLONG) model [] := by
  rw [check_syscall_56 segs ms x8 eff model Hno]
  simp only [check_openat, Hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    check_openat_body, in_mem_si, Hpath]
  exact check_copyins_after_ret_only (open_copyins ms) eff (errno_ret ENAMETOOLONG) model []

end LinuxProcessSemantics.Common.FileSim
