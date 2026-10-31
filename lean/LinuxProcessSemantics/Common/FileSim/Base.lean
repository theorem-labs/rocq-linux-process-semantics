import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.CatExec

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # Common.FileSim — union-of-resolutions glue for file-copying binaries

TRUST BOUNDARY: shared proof library, not the trusted specification.
Image-INDEPENDENT.

Conventions:

- Outcomes are `(word × Fs.Fs)` pairs (exit code is a `word`); the
  masked exit code is `bv_and (ms_gpr ms 0) (Z_to_bv 64 255)`.
- Syscall numbers are Z-characterized: the pending number `x8` is
  quantified with `bv_unsigned x8 = 56/57/63/64` (mirroring
  CatSim's `tw_write` / StreamSim's `read0_*`).
- Errnos are `Int` (`Te : Int → _`); fds are `word`s bounded by
  `bv_unsigned fd < 2^31`; open-flag arithmetic is Rocq's `Z.ldiff`
  over `bv_unsigned`.
- The raw-ecall records carry the `ms_resv := none` field and a
  `bvmap 5 word` register file (`reg_get regs 10/11/12` are
  a0/a1/a2, `getr regs 17` is a7); post-syscall states collapse to
  `mkst ... (v_addi pc 4) ...`.
- File offsets/counts are `word`s bridged with `word_to_nat`; the
  read-effect return value is `len_word bs` and offsets advance by
  `bv` addition (`off + len_word bs`, the Specs.v spelling).

A binary whose only observables are its exit code and the FINAL FILE
SYSTEM (no channel I/O at all: openat/close and file read/write emit
no trace events) has as behavior a UNION over syscall resolutions of
(exit code, final fs) outcomes. The Rocq file provides, across the Lean parts:

- `to_fout segs ms model U`: from machine state `ms` and model
  `model`, the reachable set of (code, fs) outcomes is EXACTLY `U`.
  Leaves are exit ecalls; interior nodes are event-free,
  never-halting, never-erroring syscalls branching over every
  admissible resolution (`tfo_sys`).
- The trace characterization (`fout_obs_iff`): `obs_trace` is
  exactly the prefixes of `[ExitEv code fs]` for the outcomes in
  `U`; plus no-error (`fout_no_error_run`) and the
  `Equivalence.equiv`-level glue (`fout_strong_equiv`).
- Per-syscall decoding through the verified checker for the
  file-system surface: openat (O_RDONLY hit/miss and
  O_WRONLY|O_CREAT|O_TRUNC), file read, file write, close — as
  ergonomic `to_fout` nodes.
- `read_cstr` bridges (path strings out of argv stack memory),
  fs/fd-table algebra, and `file_read`/`file_write` arithmetic for
  the copy-loop bookkeeping.
- May-error reachability helpers (`msteps_spec_err_error`,
  `reaches_error_star`) plus the stronger universal-error helper
  `msteps_spec_err_all_traces_error` for deterministic Unmodeled paths.

This part ports Rocq lines 59–128, 507–540, 987–1026, and 1890–1894.

Representation spellings:
- Rocq `fst`/`snd` are `.1`/`.2`, `Z` is `Int`, and `Z.of_nat k`
  is `(k : Int)`. Record projections use Lean's dot notation.
- Rocq's Section `WithSegs` variable becomes the explicit leading
  argument `segs` of `to_fout`, `tfo_exit_code`, and `tfo_sys_det`.
- Inductive constructors are under `to_fout`; their Rocq names are unchanged.
- `arg_reg_0/1/2` remain in `Common.PropExec`. The return-effect collapse
  reuses `Common.CatExec.adv_set`, and the first argument projection reuses
  `Common.ExitSim.in_arg0_sys_input`.
- The two ergonomic nodes need only the constructors in this part, not
  the later Rocq `to_fout_*` lemmas.
-/

namespace LinuxProcessSemantics.Common.FileSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.ExitSim

/-! ## Model plumbing -/

theorem with_fds_fs (f : List (word × FdEntry)) (m : Model) :
    m_fs (with_fds f m) = m_fs m := rfl

theorem with_fds_halted (f : List (word × FdEntry)) (m : Model) :
    m_halted (with_fds f m) = m_halted m := rfl

theorem with_fds_fds (f : List (word × FdEntry)) (m : Model) :
    m_fds (with_fds f m) = f := rfl

theorem with_fs_fs (f : Fs.Fs) (m : Model) : m_fs (with_fs f m) = f := rfl

theorem with_fs_halted (f : Fs.Fs) (m : Model) :
    m_halted (with_fs f m) = m_halted m := rfl

theorem with_fs_fds (f : Fs.Fs) (m : Model) :
    m_fds (with_fs f m) = m_fds m := rfl

/-- Advance past the svc after applying a return-only effect at the raw ecall record. -/
theorem adv_eff_ret (regs : bvmap 5 word) (pc x8 : word)
    (mem rom : word → Option byte) (r : word) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some x8, ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rom } (mkEffect r [] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom :=
  CatExec.adv_set regs pc (some x8) mem rom r

/-- Copy-in provenance does not change the machine-state transition. -/
theorem adv_eff_ret_copyins (regs : bvmap 5 word) (pc x8 : word)
    (mem rom : word → Option byte) (r : word) (copyins : List (word × Nat)) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some x8, ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rom } (with_copyins copyins (mkEffect r [] [])))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom :=
  adv_eff_ret regs pc x8 mem rom r

/-! ## Syscall input projections -/

theorem in_sysno_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 := rfl

theorem in_arg0_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 :=
  in_arg0_sys_input segs ms x8

theorem in_arg1_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 := rfl

theorem in_arg2_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 := rfl

theorem in_mem_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_mem = ms_read_byte ms := rfl

theorem in_wmem_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_wmem = ms_writable_byte segs ms := rfl

/-! ## The exact (exit code, final fs) outcome set -/

def fout_trace (o : word × Fs.Fs) : List event := [ExitEv o.1 o.2]

inductive to_fout (segs : List Segment) :
    machine_state → Model → ((word × Fs.Fs) → Prop) → Prop
  | tfo_exit : ∀ ms model x8 (U : (word × Fs.Fs) → Prop),
      ms.ms_svc_pending = some x8 →
      is_exit_no x8 →
      (∀ o, U o ↔ o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) →
      to_fout segs ms model U
  | tfo_step : ∀ ms ms' model U,
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = MachineOk ms' →
      to_fout segs ms' model U →
      to_fout segs ms model U
  | tfo_sys : ∀ ms model x8
      (T : SyscallEffect → Model → (word × Fs.Fs) → Prop)
      (U : (word × Fs.Fs) → Prop),
      ms.ms_svc_pending = some x8 →
      ¬ syscall_spec (sys_input segs ms x8) model Unmodeled →
      (∃ eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) →
      (∀ eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        evs = [] ∧ m_halted model' = none ∧ m_vm_lazy model' = []) →
      (∀ eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        to_fout segs (advance_past_svc (apply_effect ms eff)) model' (T eff model')) →
      (∀ o, U o ↔ ∃ eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ∧ T eff model' o) →
      to_fout segs ms model U

/-- Exit leaf with a small literal code. -/
theorem tfo_exit_code (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 code : word) (Hsvc : ms.ms_svc_pending = some x8) (Hx8 : is_exit_no x8)
    (Hg : ms_gpr ms 0 = code) (Hland : bv_and code (Z_to_bv 64 255) = code) :
    to_fout segs ms model (fun o => o = (code, m_fs model)) := by
  apply to_fout.tfo_exit ms model x8 _ Hsvc Hx8
  intro o
  rw [Hg, Hland]

/-- Sequential composition for a syscall with a unique admissible outcome. -/
theorem tfo_sys_det (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (model' : Model) (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hok : syscall_spec (sys_input segs ms x8) model (Ok eff model' []))
    (Huniq : ∀ eff2 m2 evs2,
      syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) →
      eff2 = eff ∧ m2 = model' ∧ evs2 = [])
    (Hne : ¬ syscall_spec (sys_input segs ms x8) model Unmodeled)
    (Hh' : m_halted model' = none) (Hlazy' : m_vm_lazy model' = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms eff)) model' U) :
    to_fout segs ms model U := by
  refine to_fout.tfo_sys ms model x8 (fun _ _ => U) U Hsvc Hne
    ⟨eff, model', [], Hok⟩ ?_ ?_ ?_
  · intro eff2 m2 evs2 Hs
    obtain ⟨_, rfl, rfl⟩ := Huniq eff2 m2 evs2 Hs
    exact ⟨rfl, Hh', Hlazy'⟩
  · intro eff2 m2 evs2 Hs
    obtain ⟨rfl, rfl, _⟩ := Huniq eff2 m2 evs2 Hs
    exact Hcont
  · intro o
    constructor
    · intro Ho
      exact ⟨eff, model', [], Hok, Ho⟩
    · rintro ⟨_, _, _, _, Ht⟩
      exact Ht

/-- Unpack the argument-register projection at a raw machine-state record. -/
theorem record_gpr (regs fr : bvmap 5 word) (pc : word) (sv rv : Option word)
    (fc : BitVec 32) (mem rom : word → Option byte) (k : Nat) :
    ms_gpr
      { ms_regs := regs, ms_fregs := fr, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := rv, ms_fcsr := fc, ms_mem := mem, ms_rom := rom } k
      = reg_get regs (Z_to_bv 5 (10 + (k : Int))) := rfl

end LinuxProcessSemantics.Common.FileSim
