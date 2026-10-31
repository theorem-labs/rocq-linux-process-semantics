import LinuxProcessSemantics.Common.FileSim.Decode
import LinuxProcessSemantics.Common.FileSim.Algebra
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StreamExec

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # Common.FileSim — file read, write, close, and raw-ecall wrappers

TRUST BOUNDARY: shared proof library, not the trusted specification.
Image-INDEPENDENT.

Ports Rocq lines 1591–1878 and 1890–2084, reusing `Base.record_gpr`.
The Section variable `segs` is an explicit leading argument.
The read wrapper uses `StreamExec.adv_apply_write` for a nonempty delivery
and `Base.adv_eff_ret` for EOF instead of copying `adv_apply_delivered`.
No lemma from the Open part is needed. The newer checker's
`unreadable_source_past_eof` guard is false under the original full-buffer
readability premises; no extra hypothesis is required.
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
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.StreamExec

variable (segs : List Segment)

theorem tfo_read_file (ms : machine_state) (model : Model) (x8 : word)
    (p : path) (off : word) (data w : List byte) (U : word × Fs → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdFile p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = some w)
    (Hcnt : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max)
    (_Hpos : 0 < bv_unsigned (ms_gpr ms 2))
    (Haok : access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (advance_past_svc (apply_effect ms
        (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
          (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) [])))
      (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
        (FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) model) U) :
    to_fout segs ms model U := by
  let bs := file_read data off (ms_gpr ms 2)
  have Hlen : (bs.length : Int) ≤ bv_unsigned (ms_gpr ms 2) := by
    dsimp only [bs]
    rw [length_file_read]
    have Hmin := Nat.min_le_left (word_to_nat (ms_gpr ms 2))
      (data.length - word_to_nat off)
    change ((min _ _ : Nat) : Int) ≤ ((word_to_nat (ms_gpr ms 2) : Nat) : Int)
    omega
  have HL : bv_unsigned (len_word bs) ≤ bv_unsigned (ms_gpr ms 2) := by
    have Hr := word_unsigned_range (ms_gpr ms 2)
    rw [len_word_unsigned bs (by omega)]
    exact Hlen
  have Hword : Z_to_bv 64 (bv_unsigned (ms_gpr ms 2)) = ms_gpr ms 2 := by
    simp only [Z_to_bv, bv_unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have Hreduce : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      match (generalizing := false) bs with
      | [] => check_ret_only eff (Z_to_bv 64 0)
          (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
            (FdFile p (off + len_word bs))) model) []
      | _ :: _ => match eff with
        | .mkEffectU ret [(a, bs')] [] [] [] [] =>
          if bv_eqb a (ms_gpr ms 1) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
          then CheckOk (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
            (FdFile p (off + len_word bs))) model) [] else CheckReject
        | _ => CheckReject := by
    intro eff
    rw [check_syscall_63 segs ms x8 eff model Hno]
    simp only [check_read, Hfd32, Hfd, Haok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Hfs, rw_count_clamp_of_rw _ Hcnt, Hword, in_wmem_si]
    rw [read_bytes_map_prefix _ _ _ _ _ HL Hw]
    rfl
  have Hchk : ∀ eff m' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ↔
      eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [] ∧
      m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
        (FdFile p (off + len_word bs))) model ∧ evs = [] := by
    intro eff m' evs
    rw [Hreduce]
    cases Hbs : bs with
    | nil => exact check_ret_only_ok_iff _ _ _ _ _ _
    | cons b rest =>
      cases eff with
      | mkEffectU ret ws zs us cs copyins =>
        cases ws with
        | nil => simp only [mkEffect, delivered_writes, SyscallEffect.mkEffectU.injEq,
            reduceCtorEq, and_false, false_and]
        | cons aw ws =>
          rcases aw with ⟨a, bytes⟩
          cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
            simp only [mkEffect, delivered_writes, reduceCtorEq, SyscallEffect.mkEffectU.injEq,
              List.cons.injEq, Prod.mk.injEq, and_true, and_false, false_and]
          split
          next H =>
            simp only [Bool.and_eq_true] at H
            obtain ⟨⟨Ha, Hb⟩, Hr⟩ := H
            have Ha' := (bv_eqb_eq _ _).mp Ha
            have Hb' := (listN_eqb_eq _ _).mp Hb
            have Hr' := (bv_eqb_eq _ _).mp Hr
            subst a bytes ret
            simp only [check_result.CheckOk.injEq, true_and, eq_comm]
          next H =>
            simp only [reduceCtorEq, false_iff]
            rintro ⟨⟨rfl, rfl, rfl⟩, _, _⟩
            exact H (by simp only [PropExec.bv_eqb_refl, listN_eqb_refl, Bool.and_self])
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]
    rfl
  apply tfo_sys_det segs ms model x8
    (mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [])
    (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
      (FdFile p (off + len_word bs))) model) U Hsvc
  · exact (check_syscall_ok_iff _ _ _ _ _ Hagree).mp ((Hchk _ _ _).mpr ⟨rfl, rfl, rfl⟩)
  · intro eff m' evs Hs
    exact (Hchk _ _ _).mp ((check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs)
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hreduce] at H
    cases Hbs : bs with
    | nil =>
      rw [Hbs] at H
      exact check_ret_only_no_unmodeled _ _ _ _ H
    | cons b rest =>
      rw [Hbs] at H
      cases H
  · exact Hh
  · exact Hlazy
  · exact Hcont

theorem tfo_write_file (ms : machine_state) (model : Model) (x8 : word)
    (p : path) (off : word) (data bs : List byte) (U : word × Fs → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdFileW p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (Hcnt : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : (!modeled_file_gap data off bs) = false)
    (Hnz : w_is0 (ms_gpr ms 2) = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
      (with_copyins [(ms_gpr ms 1, bs.length)] (mkEffect (ms_gpr ms 2) [] []))))
      (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
        (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U) :
    to_fout segs ms model U := by
  have Hrb : read_bytes_map (sys_input segs ms x8).in_mem
      (ms_gpr ms 1) (ms_gpr ms 2) = some bs := Hrd
  have Hlen := read_bytes_map_length _ _ _ _ Hrb
  have Hret : len_word bs = ms_gpr ms 2 := by
    rw [len_word, Hlen]
    simp only [Z_to_bv, bv_unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have Hne : bs.length ≠ 0 := by
    intro Hz
    have Hzero : ms_gpr ms 2 = Z_to_bv 64 0 := by
      rw [← Hret, len_word, Hz]
      rfl
    have Htrue : w_is0 (ms_gpr ms 2) = true := by
      rw [Hzero]; exact PropExec.bv_eqb_refl _
    rw [Hnz] at Htrue
    cases Htrue
  have Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      check_ret_only_copyins [(ms_gpr ms 1, bs.length)] eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
          (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) [] := by
    intro eff
    rw [check_syscall_64 segs ms x8 eff model Hno]
    have Hbeq : (bs.length == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact Hne
    simp only [check_write, Hfd32, Hfd, rw_range_in_range _ _ Hcnt,
      Bool.false_eq_true, ↓reduceIte,
      write_source_of_rw _ _ _ Hcnt, readable_bytes_full _ _ _ _ Hrb,
      Hfs, unreadable_source_past_eof, Hnz, Hbeq,
      Bool.not_false, Bool.true_and, Bool.false_and, Hgap, Hret]
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  apply tfo_sys_det segs ms model x8
    (with_copyins [(ms_gpr ms 1, bs.length)] (mkEffect (ms_gpr ms 2) [] []))
    (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
      (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U Hsvc
  · apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m' evs Hs
    have H := (check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs
    rw [Hchk, check_ret_only_copyins_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ H
  · exact Hh
  · exact Hlazy
  · exact Hcont

/-- The zero-count write carries an empty copy-in ledger. -/
theorem tfo_write_file_zero (ms : machine_state) (model : Model) (x8 : word)
    (p : path) (off : word) (data bs : List byte) (U : word × Fs → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdFileW p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (Hcnt : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : (!modeled_file_gap data off bs) = false)
    (Hz : w_is0 (ms_gpr ms 2) = true)
    (Hok : access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms (mkEffect (ms_gpr ms 2) [] [])))
      (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
        (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U) :
    to_fout segs ms model U := by
  have Hrb : read_bytes_map (sys_input segs ms x8).in_mem
      (ms_gpr ms 1) (ms_gpr ms 2) = some bs := Hrd
  have Hlen := read_bytes_map_length _ _ _ _ Hrb
  have Hret : len_word bs = ms_gpr ms 2 := by
    rw [len_word, Hlen]
    simp only [Z_to_bv, bv_unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      check_ret_only eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
          (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) [] := by
    intro eff
    rw [check_syscall_64 segs ms x8 eff model Hno]
    simp only [check_write, Hfd32, Hfd, rw_range_in_range _ _ Hcnt,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      write_source_of_rw _ _ _ Hcnt, readable_bytes_full _ _ _ _ Hrb,
      Hfs, unreadable_source_past_eof, Hz, Bool.false_and, Hgap, Hret,
      check_access_ok_zero, Hok]
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  apply tfo_sys_det segs ms model x8 (mkEffect (ms_gpr ms 2) [] [])
    (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
      (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U Hsvc
  · apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m' evs Hs
    have H := (check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs
    rw [Hchk, check_ret_only_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_no_unmodeled _ _ _ _ H
  · exact Hh
  · exact Hlazy
  · exact Hcont

theorem tfo_close (ms : machine_state) (model : Model) (x8 : word)
    (e : FdEntry) (U : word × Fs → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 57)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some e)
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [])))
      (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) U) :
    to_fout segs ms model U := by
  have Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      check_ret_only eff (Z_to_bv 64 0)
        (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) [] := by
    intro eff
    rw [check_syscall_57 segs ms x8 eff model Hno]
    simp only [check_close, Hfd32, Hfd]
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  apply tfo_sys_det segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
    (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) U Hsvc
  · apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m' evs Hs
    have H := (check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs
    rw [Hchk, check_ret_only_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_no_unmodeled _ _ _ _ H
  · exact Hh
  · exact Hlazy
  · exact Hcont

/-! ## Raw-ecall record wrappers -/

theorem tfo_exit_rec (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (code : word) (fsv : Fs)
    (H17 : bv_unsigned (getr regs 17) = 93)
    (H10 : reg_get regs 10 = code) (Hc : bv_unsigned code < 256)
    (Hfs : m_fs model = fsv) :
    to_fout segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      model (fun o => o = (code, fsv)) := by
  rw [← Hfs]
  apply tfo_exit_code segs _ model (getr regs 17) code rfl (Or.inl H17)
  · rw [record_gpr, arg_reg_0]
    exact H10
  · exact land_255_small code Hc

theorem tfo_read_rec (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (fdv : word) (p : path)
    (off : word) (data : List byte) (buf cnt : word) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 63)
    (H10 : reg_get regs 10 = fdv) (H11 : reg_get regs 11 = buf)
    (H12 : reg_get regs 12 = cnt)
    (Hfd : fd_lookup (m_fds model) fdv = some (FdFile p off))
    (Hfd32 : fd32 fdv = fdv) (Hfs : fs_lookup (m_fs model) p = some data)
    (Hwseg : wseg_ok segs buf (word_to_nat cnt) = true)
    (Hcnt : bv_unsigned cnt ≤ rw_bytes_max) (Hpos : 0 < bv_unsigned cnt)
    (Haok : access_okb buf (bv_unsigned cnt) = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
        (write_to_mem mem buf (file_read data off cnt)) rom)
      (with_fds (fd_insert (m_fds model) fdv
        (FdFile p (off + len_word (file_read data off cnt)))) model) U) :
    to_fout segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } model U := by
  let ms : machine_state :=
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none,
      ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
  have Hg0 : ms_gpr ms 0 = fdv := by
    rw [record_gpr, arg_reg_0]; exact H10
  have Hg1 : ms_gpr ms 1 = buf := by
    rw [record_gpr, arg_reg_1]; exact H11
  have Hg2 : ms_gpr ms 2 = cnt := by
    rw [record_gpr, arg_reg_2]; exact H12
  obtain ⟨w, Hw⟩ := wseg_ok_wdef segs buf cnt ms Hwseg
  apply tfo_read_file segs ms model (getr regs 17) p off data w U rfl H17
  · rw [Hg0]; exact Hfd
  · rw [Hg0]; exact Hfd32
  · exact Hfs
  · rw [Hg1, Hg2]; exact Hw
  · rw [Hg2]; exact Hcnt
  · rw [Hg2]; exact Hpos
  · rw [Hg1, Hg2]; exact Haok
  · exact Hh
  · exact Hlazy
  · rw [Hg0, Hg1, Hg2]
    dsimp only [ms]
    cases Hbs : file_read data off cnt with
    | nil =>
      simp only [Hbs, write_to_mem] at Hcont
      simp only [delivered_writes, adv_eff_ret]
      exact Hcont
    | cons b rest =>
      simp only [Hbs] at Hcont
      rw [delivered_writes, adv_apply_write]
      exact Hcont

theorem tfo_write_rec (regs : bvmap 5 word) (pc : word)
    (mem : word → Option byte) (model : Model) (fdv : word) (p : path)
    (off : word) (data bs : List byte) (buf cnt : word) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 64)
    (H10 : reg_get regs 10 = fdv) (H11 : reg_get regs 11 = buf)
    (H12 : reg_get regs 12 = cnt)
    (Hfd : fd_lookup (m_fds model) fdv = some (FdFileW p off))
    (Hfd32 : fd32 fdv = fdv)
    (Hrd : rdn segs mem buf (word_to_nat cnt) = some bs)
    (Hcnt : bv_unsigned cnt ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : (!modeled_file_gap data off bs) = false)
    (Hok : access_okb buf (bv_unsigned cnt) = true ∨ 0 < bv_unsigned cnt)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs))
      (with_fds (fd_insert (m_fds model) fdv (FdFileW p (off + cnt)))
        (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U) :
    to_fout segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom segs } model U := by
  let ms : machine_state :=
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none,
      ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := seg_rom segs }
  have Hg0 : ms_gpr ms 0 = fdv := by
    rw [record_gpr, arg_reg_0]; exact H10
  have Hg1 : ms_gpr ms 1 = buf := by
    rw [record_gpr, arg_reg_1]; exact H11
  have Hg2 : ms_gpr ms 2 = cnt := by
    rw [record_gpr, arg_reg_2]; exact H12
  have Hread : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs := by
    rw [Hg1, Hg2, read_bytes_map_read_byte, ms_read_bytes_rdn segs ms _ _ rfl]
    exact Hrd
  cases Hz : w_is0 cnt with
  | true =>
    apply tfo_write_file_zero segs ms model (getr regs 17) p off data bs U rfl H17
    · rw [Hg0]; exact Hfd
    · rw [Hg0]; exact Hfd32
    · exact Hread
    · rw [Hg2]; exact Hcnt
    · exact Hfs
    · exact Hgap
    · rw [Hg2]; exact Hz
    · rw [Hg1, Hg2]
      rcases Hok with Hfl | Hp
      · exact Hfl
      · rw [w_is0_pos cnt Hp] at Hz
        cases Hz
    · exact Hh
    · exact Hlazy
    · rw [Hg0, Hg2]
      dsimp only [ms]
      rw [adv_eff_ret]
      exact Hcont
  | false =>
    apply tfo_write_file segs ms model (getr regs 17) p off data bs U rfl H17
    · rw [Hg0]; exact Hfd
    · rw [Hg0]; exact Hfd32
    · exact Hread
    · rw [Hg2]; exact Hcnt
    · exact Hfs
    · exact Hgap
    · rw [Hg2]; exact Hz
    · exact Hh
    · exact Hlazy
    · rw [Hg0, Hg2]
      dsimp only [ms]
      rw [adv_eff_ret_copyins]
      exact Hcont

theorem tfo_close_rec (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (fdv : word)
    (e : FdEntry) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 57) (H10 : reg_get regs 10 = fdv)
    (Hfd : fd_lookup (m_fds model) fdv = some e) (Hfd32 : fd32 fdv = fdv)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
      (with_fds (fd_remove (m_fds model) fdv) model) U) :
    to_fout segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } model U := by
  let ms : machine_state :=
    { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none,
      ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
  have Hg0 : ms_gpr ms 0 = fdv := by
    rw [record_gpr, arg_reg_0]; exact H10
  apply tfo_close segs ms model (getr regs 17) e U rfl H17
  · rw [Hg0]; exact Hfd
  · rw [Hg0]; exact Hfd32
  · exact Hh
  · exact Hlazy
  · rw [Hg0]
    dsimp only [ms]
    rw [adv_eff_ret]
    exact Hcont

end LinuxProcessSemantics.Common.FileSim
