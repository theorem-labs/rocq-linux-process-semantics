import LinuxProcessSemantics.Common.AllocSim
import LinuxProcessSemantics.Common.SeqExec

/-! rocq-baseline: 7ba58b45f168d97ca1a555a98fa3b36f29eb5b81 -/

/-! # Common.MmapSim — one anonymous mmap with a failure tail and a success tail

Ported from `theories/Common/MmapSim.v`, with the Rocq statements
(ticket E-proof-library-2a).  The file was read at the commit named
above (`nightly/09-28-2026`).

What a `tmw` derivation pins (the one mmap register shape
`mmap_args_ok` names, the same failure tail for every errno in
`mmap_errnos`, the same success tail for every admissible grant address)
and why the munmap shape `munmap_args_ok` names has one outcome are argued
in the Rocq file's header.  The `CatSim`,
`SeqExec` and `PropExec` names this file reaches that no earlier port
of those files declares are appended to them, in their sections headed
"Additions for E-proof-library-2a (MmapSim)".

Representation spellings:
- Rocq `Z` is `Int`, and Rocq's `2 ^ sh` at a `Z` exponent is
  `PropExec.Z_pow 2 sh`.  Rocq `Z.div` and `mod` are `/` and `%`, which
  agree with them at the positive divisors used here (`Z_pow 2 sh` and
  `page_size`).  Rocq's `=?`, `<?` and `<=?` on `Z` inside a boolean are
  the decided `=`, `<` and `≤`.
- Rocq `firstn`/`skipn` are `List.take`/`List.drop`, and `(_ <= _)%nat`
  is `Nat`'s `≤`.  Rocq `Forall_cons_iff` on `bufs_modeled` is
  `List.mem_cons_self` and `List.mem_cons_of_mem` here.
- Rocq's `Section WithSegs` variable `segs` is an explicit leading
  argument of `twm`, `twm_pend`, `twm_tail` and `tmw`, and of the
  section's lemmas that use it.
- Rocq's `Scheme … Minimality` declarations `twm_min`, `twm_pend_min`
  and `twm_tail_min`, and its `Combined Scheme` `twm_mutind`, are
  theorems proved from `twm.rec`.  Rocq's generated `twm_ind`,
  `twm_pend_ind`, `twm_tail_ind` and `tmw_ind` are stated as theorems, as
  `ExitSim.to_exit_ind` is; the SProp eliminators `twm_sind`,
  `twm_pend_sind`, `twm_tail_sind` and `tmw_sind` are not ported (Lean
  has no SProp).
- Rocq's `State.alloc_top_bounds` tactic, which `grant_not_errno`'s proof
  calls, poses `alloc_top_room` and `stack_max_size_val`; the Lean `State`
  has the first and no twin of the second, so that proof decides
  `stack_max_size`'s value in place. -/

namespace LinuxProcessSemantics.Common.MmapSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem hiding exec
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.ExitSim

/-! ## Extra per-instruction step lemmas -/

/-- Unsigned shift right is division, at the `bv_unsigned` level.  Rocq's
`Z.div` is `/` here: they differ only at a negative divisor, and
`Z_pow 2 sh` is positive under the hypothesis. -/
theorem v_srli_div (x : word) (sh : Int) (Hsh : 0 ≤ sh ∧ sh < 64) :
    bv_unsigned (v_srli x sh) = bv_unsigned x / Z_pow 2 sh := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, sh = (k : Int) := ⟨sh.toNat, by omega⟩
  have hx := u64_range x
  have hsh : Z_shiftl (bv_unsigned x) (-(k : Int)) = bv_unsigned x / 2 ^ k := by
    cases k with
    | zero => simp only [Int.natCast_zero, Int.neg_zero, Z_shiftl, Int.shiftLeft_zero, Int.pow_zero, Int.ediv_one]
    | succ j =>
      show Z_shiftl (bv_unsigned x) (Int.negSucc j) = _
      simp only [Z_shiftl, Int.shiftRight_eq_div_pow]
      rw [Int.natCast_pow]
      rfl
  have hp : Z_pow 2 (k : Int) = 2 ^ k := rfl
  unfold v_srli
  rw [Z_to_bv_unsigned, bv_wrap64_mod, hsh, hp]
  have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have h0 : 0 ≤ bv_unsigned x / 2 ^ k := Int.ediv_nonneg hx.1 (Int.le_of_lt hpos)
  have hle : bv_unsigned x / 2 ^ k ≤ bv_unsigned x := Int.ediv_le_self _ hx.1
  exact Int.emod_eq_of_lt h0 (by omega)

/-- Byte store of an ARBITRARY register value: `SeqExec.step_sb` with the
stored byte spelled as the low byte `Z_to_bv 8 (bv_unsigned v)`. -/
theorem step_sb_any (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (.Store .SZ1 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
          [Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom) := by
  rw [← N_to_le_bytes_1_small]
  exact step_sb segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok

/-- `step_sb_any` with address, value and stored byte pre-normalized. -/
theorem step_sb_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word) (b : byte)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decode_any w = some (.Store .SZ1 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) (bv_signed imm) = a)
    (Hv : getr regs rs2 = v)
    (Hb : Z_to_bv 8 (bv_unsigned v) = b)
    (Hok : store_ok segs mem a 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom) := by
  rw [step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd (by rw [Ha]; exact Hok),
    Ha, Hv, Hb]

/-! ## `wbytes`: append a byte at the end of an accumulated store run -/

theorem wbytes_snoc (bs : List byte) (m : word → Option byte) (a : word) (b : byte) :
    wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word bs.length) [b] :=
  wbytes_app m a

/-! ## The zero-filled grant overlay -/

/-- `AllocSim.zmem` with the argument order an mmap-side proof reads
(`zfill addr len mem`). -/
def zfill (a n : word) (m : word → Option byte) : word → Option byte :=
  zmem m a n

theorem zfill_out (a n : word) (m : word → Option byte) (x : word)
    (Hx : bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) :
    zfill a n m x = m x :=
  zmem_out m a n x Hx

/-- The no-overflow hypothesis is inherited from `rdn_ext`. -/
theorem rdn_zfill_out (segs : List Segment) (a n : word) (m : word → Option byte) (x : word)
    (k : Nat) (Hnw : bv_unsigned x + (k : Int) ≤ 2 ^ 64)
    (Hd : bv_unsigned x + (k : Int) ≤ bv_unsigned a
      ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) :
    rdn segs (zfill a n m) x k = rdn segs m x k :=
  rdn_zmem_out segs m a n x k Hnw Hd

/-! ## Model transformers for mmap and munmap -/

def munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
      (map_remove (m_vmmaps m).vm_maps addr)
      (maps_subtract (m_vmmaps m).vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
      (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
      (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m

def mmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved ((a, n) :: (m_vmmaps m).vm_maps)
      (m_vmmaps m).vm_noaccess (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
      (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m

/-- The rounded grant length as a `word`: what lands in the effect's zero
list and in the model's `vm_maps` entry. -/
def page_round_up (len : word) : word :=
  Z_to_bv 64 (page_round_up_Z (bv_unsigned len))

set_option linter.unusedVariables false in
/-- May the kernel grant `[a, a+n)`?  `n` is the ROUNDED length and `hint`
the caller's addr argument, which Rocq's comment calls dead (issue #506). -/
def grant_ok (hint : word) (m : Model) (a : word) (n : Int) : Bool :=
  decide (bv_unsigned a % page_size = 0) && decide (0 < bv_unsigned a)
  && decide (bv_unsigned a + n ≤ alloc_top (m_vmmaps m))
  && region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a (Z_to_bv 64 n)
  && decide (vm_backing_used m + n ≤ (m_vmmaps m).vm_limit)

theorem munmap_model_halted (addr n : word) (m : Model) :
    m_halted (munmap_model addr n m) = m_halted m := rfl
theorem munmap_model_fs (addr n : word) (m : Model) :
    m_fs (munmap_model addr n m) = m_fs m := rfl
theorem munmap_model_fd1chan (addr n : word) (m : Model) (H : fd1chan m) :
    fd1chan (munmap_model addr n m) := H
theorem munmap_model_no_lazy (addr n : word) (m : Model) (Hlazy : m_vm_lazy m = []) :
    m_vm_lazy (munmap_model addr n m) = [] := by
  show maps_subtract (m_vm_lazy m) _ _ = []
  rw [Hlazy]
  rfl
theorem mmap_model_halted (a n : word) (m : Model) :
    m_halted (mmap_model a n m) = m_halted m := rfl
theorem mmap_model_fs (a n : word) (m : Model) : m_fs (mmap_model a n m) = m_fs m := rfl
theorem mmap_model_fd1chan (a n : word) (m : Model) (H : fd1chan m) :
    fd1chan (mmap_model a n m) := H
theorem mmap_model_lazy (a n : word) (m : Model) :
    m_vm_lazy (mmap_model a n m) = m_vm_lazy m := rfl

/-- Unpack `grant_ok` into its `Int`-level facts. -/
theorem grant_ok_unpack (hint : word) (m : Model) (a : word) (n : Int)
    (H : grant_ok hint m a n = true) :
    bv_unsigned a % page_size = 0 ∧ 0 < bv_unsigned a ∧
    bv_unsigned a + n ≤ alloc_top (m_vmmaps m) ∧
    region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a (Z_to_bv 64 n) = true ∧
    vm_backing_used m + n ≤ (m_vmmaps m).vm_limit := by
  simp only [grant_ok, Bool.and_eq_true, decide_eq_true_eq] at H
  obtain ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩ := H
  exact ⟨H1, H2, H3, H4, H5⟩

theorem region_free_cons (b s : word) (r : List (word × word)) (lo n : word)
    (H : region_free ((b, s) :: r) lo n = true) :
    (bv_unsigned lo + bv_unsigned n ≤ bv_unsigned b
      ∨ bv_unsigned b + bv_unsigned s ≤ bv_unsigned lo)
    ∧ region_free r lo n = true := by
  simp only [region_free, iv_overlap, Bool.and_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at H
  obtain ⟨H1, H2⟩ := H
  refine ⟨?_, H2⟩
  omega

/-- Numeric restatements of the per-role allocation budgets
(`State.source_alloc_limit` / `State.target_alloc_limit`). -/
theorem source_alloc_limit_val : source_alloc_limit = 0x400000000 := rfl
theorem target_alloc_limit_val : target_alloc_limit = 0x8000000000 := rfl

/-! ## Syscall-input decode facts -/

theorem in_arg3_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3 := rfl
theorem in_arg4_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4 := rfl
theorem in_arg5_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5 := rfl

/-- The one mmap register shape this library covers, which
`Mmap.mmap_modeled_b` accepts.  Why a0 is unconstrained, and why a4 is
pinned to -1 although the modeled shape does not read it, is argued on the
Rocq definition. -/
def mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 ≠ Z_to_bv 64 0 ∧ ms_gpr ms 2 = Z_to_bv 64 3
  ∧ ms_gpr ms 3 = Z_to_bv 64 34 ∧ ms_gpr ms 4 = Z_to_bv 64 (-1)
  ∧ ms_gpr ms 5 = Z_to_bv 64 0

/-- What `mmap_args_ok` gives `check_mmap`'s tests: a page-aligned offset,
anonymous flags, a nonzero length and the `mmap_modeled_b` shape, which
together select the arm `mmap_fail_ok` and `mmap_succ_ok` unfold to. -/
theorem mmap_args_ok_gates (ms : machine_state) (H : mmap_args_ok ms) :
    mmap_off_aligned_b (ms_gpr ms 5) = true ∧ mmap_anon_b (ms_gpr ms 3) = true ∧
    w_is0 (ms_gpr ms 1) = false ∧
    mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true := by
  obtain ⟨H1, H2, H3, _, H5⟩ := H
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [H5]; decide
  · rw [H3]; decide
  · exact bv_eqb_neq _ _ H1
  · rw [H2, H3, H5]; decide

/-! ## munmap: the unique admissible outcome for the modeled shape -/

/-- The munmap register and ledger shape whose outcome is unique; why the
range conjunct bounds the SUM by `State.TASK_SIZE` is argued on the Rocq
definition. -/
def munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  bv_unsigned (ms_gpr ms 0) % page_size = 0 ∧
  ms_gpr ms 1 ≠ Z_to_bv 64 0 ∧
  bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) ≤ TASK_SIZE ∧
  map_has (m_vmmaps model).vm_maps (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) = true

/-- The unique admissible munmap effect: return 0 and unmap the range. -/
def munmap_eff (ms : machine_state) : SyscallEffect :=
  SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] []

/-- Which arm answers this number, on the spec side.  `syscall_spec` is
`dispatch spec_table`, so fixing the number settles the table lookup by
conversion.  See #580. -/
theorem syscall_spec_munmap (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome SyscallEffect)
    (Hno : bv_unsigned x8 = 215) :
    syscall_spec (sys_input segs ms x8) model o ↔
      munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o := by
  unfold syscall_spec dispatch
  rw [ExitSim.in_sysno_sys_input, Hno]
  exact Iff.rfl

/-- Under `munmap_args_ok` the checker collapses to the single accepted
effect. -/
theorem munmap_check_modeled (ms : machine_state) (model : Model) (eff : SyscallEffect)
    (H : munmap_args_ok ms model) :
    check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model =
      match eff with
      | SyscallEffect.mkEffectU r [] [] us [] [] =>
          if w_is0 r && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
          then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
          else CheckReject
      | _ => CheckReject := by
  obtain ⟨Hal, Hlen, Hnw, Hhas⟩ := H
  have h1 : (!(bv_unsigned (ms_gpr ms 0) % page_size == 0) || w_is0 (ms_gpr ms 1)) = false := by
    simp only [Hal, beq_self_eq_true, Bool.not_true, Bool.false_or]
    exact bv_eqb_neq _ _ Hlen
  have h2 : ¬ (TASK_SIZE < bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1))) := by
    omega
  unfold page_round_up at Hhas
  simp only [check_munmap, h1, Bool.false_eq_true, ↓reduceIte, h2, Hhas]
  rfl

theorem munmap_ok (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : bv_unsigned x8 = 215) (Ha : munmap_args_ok ms model) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (munmap_eff ms) (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []) := by
  apply (syscall_spec_munmap segs ms x8 model _ Hno).2
  apply check_munmap_sound_ok
  rw [munmap_check_modeled ms model _ Ha]
  simp only [munmap_eff, w_is0, bv_eqb_refl, (listNN_eqb_eq _ _).2 rfl, Bool.and_self, ↓reduceIte]

theorem munmap_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hno : bv_unsigned x8 = 215) (Ha : munmap_args_ok ms model)
    (Hspec : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) :
    eff = munmap_eff ms ∧
      model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model ∧ evs = [] := by
  have h := check_munmap_complete_ok _ _ _ _ _ _ _ ((syscall_spec_munmap segs ms x8 model _ Hno).1 Hspec)
  rw [munmap_check_modeled ms model eff Ha] at h
  split at h
  · rename_i r us
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, w_is0, bv_eqb_eq, listNN_eqb_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨rfl, rfl, rfl⟩
    · cases h
  · cases h

theorem munmap_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : bv_unsigned x8 = 215) (Ha : munmap_args_ok ms model) :
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro Hspec
  have h := check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])
    ((syscall_spec_munmap segs ms x8 model _ Hno).1 Hspec)
  rw [munmap_check_modeled ms model _ Ha] at h
  dsimp only [mkEffect] at h
  split at h <;> cases h

/-! ## mmap: the two families of admissible outcomes -/

/-- The mmap half of `syscall_spec_munmap`, by the same argument. -/
theorem syscall_spec_mmap (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome SyscallEffect)
    (Hno : bv_unsigned x8 = 222) :
    syscall_spec (sys_input segs ms x8) model o ↔
      mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4)
        (ms_gpr ms 5) (sys_input segs ms x8) model o := by
  unfold syscall_spec dispatch
  rw [ExitSim.in_sysno_sys_input, Hno]
  exact Iff.rfl

theorem ENOMEM_in_mmap_errnos : ENOMEM ∈ mmap_errnos := List.mem_cons_self

theorem mmap_errno_range (e : Int) (HIn : e ∈ mmap_errnos) : 1 ≤ e ∧ e ≤ 4095 :=
  errnos_ok_range mmap_errnos e rfl HIn

theorem mmap_fail_ok (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (e : Int) (Hno : bv_unsigned x8 = 222) (Ha : mmap_args_ok ms) (HIn : e ∈ mmap_errnos) :
    syscall_spec (sys_input segs ms x8) model (Ok (mkEffect (errno_ret e) [] []) model []) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  apply (syscall_spec_mmap segs ms x8 model _ Hno).2
  apply check_mmap_sound_ok
  unfold check_mmap
  rw [Hoff, Hanon, Hl, Hmb, Bool.not_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, ite_eq_left rfl]
  dsimp only [mkEffect]
  rw [ite_eq_left (errno_ret_in_intro _ _ HIn)]

/-- Rocq's `0 <= n` hypothesis is kept: `mmap_succ_ok`, its one caller in
this file, discharges it with `page_round_up_Z_nonneg`. -/
theorem grant_not_errno (hint : word) (model : Model) (a : word) (n : Int) (Hn : 0 ≤ n)
    (Hg : grant_ok hint model a n = true) : errno_ret_in mmap_errnos a = false := by
  obtain ⟨_, _, Hce, _⟩ := grant_ok_unpack _ _ _ _ Hg
  apply errno_ret_in_below mmap_errnos a rfl
  have := alloc_top_room (m_vmmaps model)
  have Hs : stack_max_size = 8388608 := by decide
  omega

theorem mmap_succ_ok (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (a : word) (Hno : bv_unsigned x8 = 222) (Ha : mmap_args_ok ms)
    (Hg : grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  obtain ⟨_, _, Hflags, _, _⟩ := Ha
  have Hne := grant_not_errno (ms_gpr ms 0) model a
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))
    (page_round_up_Z_nonneg _ (u64_range (ms_gpr ms 1)).1) Hg
  apply (syscall_spec_mmap segs ms x8 model _ Hno).2
  apply check_mmap_sound_ok
  unfold check_mmap
  rw [Hoff, Hanon, Hl, Hmb, Bool.not_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, ite_eq_left rfl]
  dsimp only [mkEffect]
  rw [Hne, ite_eq_right Bool.false_ne_true, Hflags]
  have Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false := by decide
  simp only [grant_ok, Bool.and_eq_true] at Hg
  obtain ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩ := Hg
  simp only [mmap_noreserve_backed_ok, with_mmap_backing, Hnr, Bool.false_eq_true, ↓reduceIte,
    H1, H2, H3, H4, H5, page_round_up, (listNN_eqb_eq _ _).2 rfl, Bool.and_self, mmap_model]

theorem mmap_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hno : bv_unsigned x8 = 222) (Ha : mmap_args_ok ms)
    (Hspec : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) :
    evs = [] ∧
      ((∃ e, e ∈ mmap_errnos ∧ eff = mkEffect (errno_ret e) [] [] ∧ model' = model) ∨
       (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
          ∧ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
          ∧ model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  obtain ⟨_, _, Hflags, _, _⟩ := Ha
  have h := check_mmap_complete_ok _ _ _ _ _ _ _ _ _ _ _
    ((syscall_spec_mmap segs ms x8 model _ Hno).1 Hspec)
  unfold check_mmap at h
  rw [Hoff, Hanon, Hl, Hmb, Bool.not_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, ite_eq_left rfl,
    Hflags] at h
  have Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false := by decide
  simp only [mmap_noreserve_backed_ok, with_mmap_backing, Hnr, Bool.false_eq_true,
    ↓reduceIte] at h
  split at h
  · rename_i r zs
    split at h
    · rename_i Herr
      split at h
      · cases h
        obtain ⟨e, HIn, rfl⟩ := (errno_ret_in_true _ _).1 Herr
        exact ⟨rfl, Or.inl ⟨e, HIn, rfl, rfl⟩⟩
      · cases h
    · split at h
      · rename_i Hcond
        cases h
        simp only [Bool.and_eq_true] at Hcond
        obtain ⟨⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩, Hzs⟩ := Hcond
        obtain rfl := (listNN_eqb_eq _ _).1 Hzs
        refine ⟨rfl, Or.inr ⟨r, ?_, rfl, rfl⟩⟩
        simp only [grant_ok, H1, H2, H3, H4, H5, Bool.and_self]
      · cases h
  · cases h

theorem mmap_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : bv_unsigned x8 = 222) (Ha : mmap_args_ok ms) :
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro Hspec
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  have h := check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])
    ((syscall_spec_mmap segs ms x8 model _ Hno).1 Hspec)
  unfold check_mmap at h
  rw [Hoff, Hanon, Hl, Hmb, Bool.not_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, ite_eq_left rfl] at h
  dsimp only [mkEffect] at h
  have E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false := by decide
  rw [E, ite_eq_right Bool.false_ne_true] at h
  split at h <;> cases h

/-! ## Post-syscall state collapses -/

/-- A successful grant's post-state: a0 := a, the granted page range reads
as zeros, the PC advances past the ecall. -/
theorem adv_mmap_grant (regs : bvmap 5 word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (a n : word) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (mkEffect a [] [(a, n)]))
    = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom := by
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  have hf : Z_to_bv 32 0 = (0 : BitVec 32) := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte,
    apply_writes, apply_copies, apply_unmaps, apply_zeros_one, zfill, ms_pc, mkst, regupd, hf,
    b_npc4]

/-! ## The unmapped-range overlay (munmap) -/

/-- After `munmap(a, n)` the covered range is unmapped: an address in
`[a, a+n)` reads `none` (a later access faults), and the others are
untouched.  Coverage is checked in `Int` over unsigned values, as `zfill`
checks it. -/
def unfill (a n : word) (m : word → Option byte) : word → Option byte :=
  fun x => if bv_unsigned a ≤ bv_unsigned x && bv_unsigned x < bv_unsigned a + bv_unsigned n
           then none else m x

theorem unfill_out (a n : word) (m : word → Option byte) (x : word)
    (Hx : bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) :
    unfill a n m x = m x := by
  unfold unfill
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · rfl

/-- The no-overflow hypothesis is inherited from `rdn_ext`. -/
theorem rdn_unfill_out (segs : List Segment) (a n : word) (m : word → Option byte) (x : word)
    (k : Nat) (Hnw : bv_unsigned x + (k : Int) ≤ 2 ^ 64)
    (Hd : bv_unsigned x + (k : Int) ≤ bv_unsigned a
      ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) :
    rdn segs (unfill a n m) x k = rdn segs m x k := by
  apply rdn_ext segs k _ _ x Hnw
  intro y Hy
  apply unfill_out
  omega

/-- A munmap effect's post-state: a0 := 0, the unmapped range reads as
unmapped, the PC advances past the ecall. -/
theorem adv_munmap (regs : bvmap 5 word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (a n : word) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
    = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom := by
  have Hm : apply_unmaps mem [(a, n)] = unfill a n mem := by
    funext x
    simp only [apply_unmaps, zeros_cover, unfill, List.any_cons, List.any_nil, Bool.or_false]
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  have hf : Z_to_bv 32 0 = (0 : BitVec 32) := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte,
    apply_writes, apply_copies, apply_zeros, Hm, ms_pc, mkst, regupd, hf, b_npc4]

/-! ## twm: writes/munmap/exit straight line, model threaded -/

mutual
/-- `twm ms model bufs code`: from `ms`, the machine writes each buffer of
`bufs` to fd 1 in full, may `munmap` a mapped range between them, and
exits with `code`.  The model is threaded: a munmap moves to the
unmapped model. -/
inductive twm (segs : List Segment) : machine_state → Model → List (List byte) → word → Prop
  | twm_exit : ∀ ms model x8,
      ms.ms_svc_pending = some x8 →
      is_exit_no x8 →
      twm segs ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
  | twm_write : ∀ ms model buf bufs code,
      1 ≤ buf.length →
      twm_pend segs ms model buf bufs code →
      twm segs ms model (buf :: bufs) code
  | twm_munmap : ∀ ms model x8 bufs code,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 215 →
      munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      twm segs ms model bufs code
  | twm_step : ∀ ms ms' model bufs code,
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      twm segs ms' model bufs code →
      twm segs ms model bufs code

/-- The put-style retry loop realizing one buffer: a write-pending state
offering the remainder `rest`; the environment delivers a nonempty prefix,
and the loop reissues on the rest.  The trace contribution of the node is
the full buffer (WallSim's `to_wall` shape, inlined here because the
continuation is the mutual `twm`). -/
inductive twm_pend (segs : List Segment) :
    machine_state → Model → List byte → List (List byte) → word → Prop
  | twmp_write : ∀ ms model x8 rest bufs code,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      twm_pend segs ms model rest bufs code

/-- The between-syscalls form of `twm_pend`: instruction steps, then
another write-pending state if `rest` is nonempty, or a `twm` state if it
is empty. -/
inductive twm_tail (segs : List Segment) :
    machine_state → Model → List byte → List (List byte) → word → Prop
  | twmt_done : ∀ ms model bufs code,
      twm segs ms model bufs code →
      twm_tail segs ms model [] bufs code
  | twmt_more : ∀ ms model rest bufs code,
      1 ≤ rest.length →
      twm_pend segs ms model rest bufs code →
      twm_tail segs ms model rest bufs code
  | twmt_step : ∀ ms ms' model rest bufs code,
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      twm_tail segs ms' model rest bufs code →
      twm_tail segs ms model rest bufs code
end

/-- Rocq `Scheme twm_min := Minimality for twm Sort Prop`. -/
theorem twm_min (segs : List Segment)
    (P : machine_state → Model → List (List byte) → word → Prop)
    (P0 P1 : machine_state → Model → List byte → List (List byte) → word → Prop)
    (f : ∀ ms model x8, ms.ms_svc_pending = some x8 → is_exit_no x8 →
      P ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)))
    (f0 : ∀ ms model buf bufs code, 1 ≤ buf.length → twm_pend segs ms model buf bufs code →
      P0 ms model buf bufs code → P ms model (buf :: bufs) code)
    (f1 : ∀ ms model x8 bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 →
      munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P ms model bufs code)
    (f2 : ∀ ms ms' model bufs code, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      twm segs ms' model bufs code → P ms' model bufs code → P ms model bufs code)
    (f3 : ∀ ms model x8 rest bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P1 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      P0 ms model rest bufs code)
    (f4 : ∀ ms model bufs code, twm segs ms model bufs code → P ms model bufs code →
      P1 ms model [] bufs code)
    (f5 : ∀ ms model rest bufs code, 1 ≤ rest.length → twm_pend segs ms model rest bufs code →
      P0 ms model rest bufs code → P1 ms model rest bufs code)
    (f6 : ∀ ms ms' model rest bufs code, ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' → twm_tail segs ms' model rest bufs code →
      P1 ms' model rest bufs code → P1 ms model rest bufs code) :
    ∀ m m0 l b, twm segs m m0 l b → P m m0 l b := by
  intro m m0 l b h
  exact twm.rec (motive_1 := fun ms model bufs code _ => P ms model bufs code)
    (motive_2 := fun ms model rest bufs code _ => P0 ms model rest bufs code)
    (motive_3 := fun ms model rest bufs code _ => P1 ms model rest bufs code)
    f f0 f1 f2 f3 f4 f5 f6 h

/-- Rocq `with twm_pend_min := Minimality for twm_pend Sort Prop`. -/
theorem twm_pend_min (segs : List Segment)
    (P : machine_state → Model → List (List byte) → word → Prop)
    (P0 P1 : machine_state → Model → List byte → List (List byte) → word → Prop)
    (f : ∀ ms model x8, ms.ms_svc_pending = some x8 → is_exit_no x8 →
      P ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)))
    (f0 : ∀ ms model buf bufs code, 1 ≤ buf.length → twm_pend segs ms model buf bufs code →
      P0 ms model buf bufs code → P ms model (buf :: bufs) code)
    (f1 : ∀ ms model x8 bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 →
      munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P ms model bufs code)
    (f2 : ∀ ms ms' model bufs code, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      twm segs ms' model bufs code → P ms' model bufs code → P ms model bufs code)
    (f3 : ∀ ms model x8 rest bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P1 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      P0 ms model rest bufs code)
    (f4 : ∀ ms model bufs code, twm segs ms model bufs code → P ms model bufs code →
      P1 ms model [] bufs code)
    (f5 : ∀ ms model rest bufs code, 1 ≤ rest.length → twm_pend segs ms model rest bufs code →
      P0 ms model rest bufs code → P1 ms model rest bufs code)
    (f6 : ∀ ms ms' model rest bufs code, ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' → twm_tail segs ms' model rest bufs code →
      P1 ms' model rest bufs code → P1 ms model rest bufs code) :
    ∀ m m0 l l0 b, twm_pend segs m m0 l l0 b → P0 m m0 l l0 b := by
  intro m m0 l l0 b h
  exact twm_pend.rec (motive_1 := fun ms model bufs code _ => P ms model bufs code)
    (motive_2 := fun ms model rest bufs code _ => P0 ms model rest bufs code)
    (motive_3 := fun ms model rest bufs code _ => P1 ms model rest bufs code)
    f f0 f1 f2 f3 f4 f5 f6 h

/-- Rocq `with twm_tail_min := Minimality for twm_tail Sort Prop`. -/
theorem twm_tail_min (segs : List Segment)
    (P : machine_state → Model → List (List byte) → word → Prop)
    (P0 P1 : machine_state → Model → List byte → List (List byte) → word → Prop)
    (f : ∀ ms model x8, ms.ms_svc_pending = some x8 → is_exit_no x8 →
      P ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)))
    (f0 : ∀ ms model buf bufs code, 1 ≤ buf.length → twm_pend segs ms model buf bufs code →
      P0 ms model buf bufs code → P ms model (buf :: bufs) code)
    (f1 : ∀ ms model x8 bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 →
      munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P ms model bufs code)
    (f2 : ∀ ms ms' model bufs code, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      twm segs ms' model bufs code → P ms' model bufs code → P ms model bufs code)
    (f3 : ∀ ms model x8 rest bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P1 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      P0 ms model rest bufs code)
    (f4 : ∀ ms model bufs code, twm segs ms model bufs code → P ms model bufs code →
      P1 ms model [] bufs code)
    (f5 : ∀ ms model rest bufs code, 1 ≤ rest.length → twm_pend segs ms model rest bufs code →
      P0 ms model rest bufs code → P1 ms model rest bufs code)
    (f6 : ∀ ms ms' model rest bufs code, ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' → twm_tail segs ms' model rest bufs code →
      P1 ms' model rest bufs code → P1 ms model rest bufs code) :
    ∀ m m0 l l0 b, twm_tail segs m m0 l l0 b → P1 m m0 l l0 b := by
  intro m m0 l l0 b h
  exact twm_tail.rec (motive_1 := fun ms model bufs code _ => P ms model bufs code)
    (motive_2 := fun ms model rest bufs code _ => P0 ms model rest bufs code)
    (motive_3 := fun ms model rest bufs code _ => P1 ms model rest bufs code)
    f f0 f1 f2 f3 f4 f5 f6 h

/-- Rocq `Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min`. -/
theorem twm_mutind (segs : List Segment)
    (P : machine_state → Model → List (List byte) → word → Prop)
    (P0 P1 : machine_state → Model → List byte → List (List byte) → word → Prop)
    (f : ∀ ms model x8, ms.ms_svc_pending = some x8 → is_exit_no x8 →
      P ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)))
    (f0 : ∀ ms model buf bufs code, 1 ≤ buf.length → twm_pend segs ms model buf bufs code →
      P0 ms model buf bufs code → P ms model (buf :: bufs) code)
    (f1 : ∀ ms model x8 bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 →
      munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P ms model bufs code)
    (f2 : ∀ ms ms' model bufs code, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      twm segs ms' model bufs code → P ms' model bufs code → P ms model bufs code)
    (f3 : ∀ ms model x8 rest bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P1 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      P0 ms model rest bufs code)
    (f4 : ∀ ms model bufs code, twm segs ms model bufs code → P ms model bufs code →
      P1 ms model [] bufs code)
    (f5 : ∀ ms model rest bufs code, 1 ≤ rest.length → twm_pend segs ms model rest bufs code →
      P0 ms model rest bufs code → P1 ms model rest bufs code)
    (f6 : ∀ ms ms' model rest bufs code, ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' → twm_tail segs ms' model rest bufs code →
      P1 ms' model rest bufs code → P1 ms model rest bufs code) :
    (∀ m m0 l b, twm segs m m0 l b → P m m0 l b) ∧
      (∀ m m0 l l0 b, twm_pend segs m m0 l l0 b → P0 m m0 l l0 b) ∧
      (∀ m m0 l l0 b, twm_tail segs m m0 l l0 b → P1 m m0 l l0 b) :=
  ⟨twm_min segs P P0 P1 f f0 f1 f2 f3 f4 f5 f6,
    twm_pend_min segs P P0 P1 f f0 f1 f2 f3 f4 f5 f6,
    twm_tail_min segs P P0 P1 f f0 f1 f2 f3 f4 f5 f6⟩

/-- Rocq's generated non-mutual induction principle for `twm` (no
induction hypothesis through `twm_write`'s `twm_pend` premise). -/
theorem twm_ind (segs : List Segment)
    (P : machine_state → Model → List (List byte) → word → Prop)
    (f : ∀ ms model x8, ms.ms_svc_pending = some x8 → is_exit_no x8 →
      P ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)))
    (f0 : ∀ ms model buf bufs code, 1 ≤ buf.length → twm_pend segs ms model buf bufs code →
      P ms model (buf :: bufs) code)
    (f1 : ∀ ms model x8 bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 →
      munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P ms model bufs code)
    (f2 : ∀ ms ms' model bufs code, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      twm segs ms' model bufs code → P ms' model bufs code → P ms model bufs code) :
    ∀ m m0 l b, twm segs m m0 l b → P m m0 l b :=
  twm_min segs P (fun _ _ _ _ _ => True) (fun _ _ _ _ _ => True)
    f
    (fun ms model buf bufs code h1 h2 _ => f0 ms model buf bufs code h1 h2)
    f1 f2
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)

/-- Rocq's generated non-mutual induction principle for `twm_pend`. -/
theorem twm_pend_ind (segs : List Segment)
    (P : machine_state → Model → List byte → List (List byte) → word → Prop)
    (f : ∀ ms model x8 rest bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) →
      P ms model rest bufs code) :
    ∀ m m0 l l0 b, twm_pend segs m m0 l l0 b → P m m0 l l0 b :=
  twm_pend_min segs (fun _ _ _ _ => True) P (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun ms model x8 rest bufs code h1 h2 h3 h4 h5 h6 _ =>
      f ms model x8 rest bufs code h1 h2 h3 h4 h5 h6)
    (fun _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)

/-- Rocq's generated non-mutual induction principle for `twm_tail` (no
induction hypothesis through the `twm` and `twm_pend` premises). -/
theorem twm_tail_ind (segs : List Segment)
    (P : machine_state → Model → List byte → List (List byte) → word → Prop)
    (f : ∀ ms model bufs code, twm segs ms model bufs code → P ms model [] bufs code)
    (f0 : ∀ ms model rest bufs code, 1 ≤ rest.length → twm_pend segs ms model rest bufs code →
      P ms model rest bufs code)
    (f1 : ∀ ms ms' model rest bufs code, ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' → twm_tail segs ms' model rest bufs code →
      P ms' model rest bufs code → P ms model rest bufs code) :
    ∀ m m0 l l0 b, twm_tail segs m m0 l l0 b → P m m0 l l0 b :=
  twm_tail_min segs (fun _ _ _ _ => True) (fun _ _ _ _ _ => True) P
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun ms model bufs code h _ => f ms model bufs code h)
    (fun ms model rest bufs code h1 h2 _ => f0 ms model rest bufs code h1 h2)
    f1

theorem msteps_twm (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word)
    (H : msteps segs ms ms') (Hw : twm segs ms' model bufs code) : twm segs ms model bufs code := by
  induction H with
  | mst_refl _ => exact Hw
  | mst_step ms1 ms2 _ Hsvc Hstep _ ih =>
    exact twm.twm_step ms1 ms2 model bufs code Hsvc Hstep (ih Hw)

theorem msteps_twm_tail (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (rest : List byte) (bufs : List (List byte)) (code : word)
    (H : msteps segs ms ms') (Hw : twm_tail segs ms' model rest bufs code) :
    twm_tail segs ms model rest bufs code := by
  induction H with
  | mst_refl _ => exact Hw
  | mst_step ms1 ms2 _ Hsvc Hstep _ ih =>
    exact twm_tail.twmt_step ms1 ms2 model rest bufs code Hsvc Hstep (ih Hw)

/-- A write at the raw ecall post-state.  The environment may deliver any
nonempty prefix, so the continuation is the caller's put-loop obligation:
per delivered length `n`, a `twm_tail` of the remainder `buf.drop n`. -/
theorem twm_write_ret (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (buf : List byte)
    (bufs : List (List byte)) (code : word)
    (H17 : bv_unsigned (getr regs 17) = 64)
    (H10 : reg_get regs 10 = Z_to_bv 64 1)
    (Hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
      twm_tail segs (mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom)
        model (buf.drop n) bufs code) :
    twm segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      model (buf :: bufs) code := by
  have E10 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 := by decide
  have E11 : (Z_to_bv 5 (10 + ((1 : Nat) : Int)) : reg) = 11 := by decide
  have E12 : (Z_to_bv 5 (10 + ((2 : Nat) : Int)) : reg) = 12 := by decide
  refine twm.twm_write _ model buf bufs code Hnb ?_
  refine twm_pend.twmp_write _ model (getr regs 17) buf bufs code rfl H17 ?_ ?_ Hnb ?_
  · unfold ms_gpr
    rw [E10]
    exact H10
  · unfold ms_gpr
    rw [E11, E12]
    exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

/-- The reissued write at the raw ecall post-state, inside a retry loop:
the `twm_tail` counterpart of `twm_write_ret`. -/
theorem twm_tail_write_rec (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (rest : List byte)
    (bufs : List (List byte)) (code : word)
    (H17 : bv_unsigned (getr regs 17) = 64)
    (H10 : reg_get regs 10 = Z_to_bv 64 1)
    (Hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some rest)
    (Hnb : 1 ≤ rest.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ rest.length →
      twm_tail segs (mkst (regupd regs 10 (len_word (rest.take n))) (v_addi pc 4) mem rom)
        model (rest.drop n) bufs code) :
    twm_tail segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      model rest bufs code := by
  have E10 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 := by decide
  have E11 : (Z_to_bv 5 (10 + ((1 : Nat) : Int)) : reg) = 11 := by decide
  have E12 : (Z_to_bv 5 (10 + ((2 : Nat) : Int)) : reg) = 12 := by decide
  refine twm_tail.twmt_more _ model rest bufs code Hnb ?_
  refine twm_pend.twmp_write _ model (getr regs 17) rest bufs code rfl H17 ?_ ?_ Hnb ?_
  · unfold ms_gpr
    rw [E10]
    exact H10
  · unfold ms_gpr
    rw [E11, E12]
    exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

/-- A munmap at the raw ecall post-state: a0 := 0, the mapping dropped,
and the unmapped range reads as unmapped.  `a` and `nlen` name the addr
and len register values so call sites can pre-normalize them. -/
theorem twm_munmap_rec (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (bufs : List (List byte)) (code : word)
    (a nlen : word)
    (H17 : bv_unsigned (getr regs 17) = 215)
    (Ha : reg_get regs 10 = a)
    (Hn : reg_get regs 11 = nlen)
    (Hal : bv_unsigned a % page_size = 0)
    (Hlen : nlen ≠ Z_to_bv 64 0)
    (Hnw : bv_unsigned a + page_round_up_Z (bv_unsigned nlen) ≤ TASK_SIZE)
    (Hhas : map_has (m_vmmaps model).vm_maps a (page_round_up nlen) = true)
    (Hcont : twm segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
        (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code) :
    twm segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      model bufs code := by
  have E10 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 := by decide
  have E11 : (Z_to_bv 5 (10 + ((1 : Nat) : Int)) : reg) = 11 := by decide
  subst Ha Hn
  refine twm.twm_munmap _ model (getr regs 17) bufs code rfl H17 ?_ ?_
  · unfold munmap_args_ok ms_gpr
    rw [E10, E11]
    exact ⟨Hal, Hlen, Hnw, Hhas⟩
  · unfold munmap_eff ms_gpr
    rw [E10, E11, adv_munmap]
    exact Hcont

/-- Exit with an arbitrary small code at the raw ecall post-state. -/
theorem twm_exit_coden (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (c : word)
    (H17 : bv_unsigned (getr regs 17) = 93)
    (H10 : reg_get regs 10 = c) (Hc : bv_unsigned c < 256) :
    twm segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      model [] c := by
  have E10 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 := by decide
  have Hg : bv_and (ms_gpr
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } 0) (Z_to_bv 64 255) = c := by
    unfold ms_gpr
    rw [E10]
    show bv_and (reg_get regs 10) (Z_to_bv 64 255) = c
    rw [H10]
    exact land_255_small c Hc
  rw [← Hg]
  exact twm.twm_exit _ model (getr regs 17) rfl (Or.inl H17)

/-! ## One-step inversion for a munmap config -/

theorem sstep_munmap_inv (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 215)
    (Hargs : munmap_args_ok ms model)
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    evs = [] ∧
      st = SNext (config.mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) := by
  cases Hss with
  | sstep_instr _ _ _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_syscall _ _ x8' eff m' m'' evs' _ hv hspec _ hmat =>
    rw [Hsvc] at hv
    cases hv
    obtain ⟨heff, hm, hevs⟩ := munmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    subst heff hm hevs
    rw [materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy)] at hmat
    cases hmat
    exact ⟨rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ x8' eff m' evs' _ hv hspec _ hmat =>
    -- no lazy range can fault
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, hm, _⟩ := munmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    subst hm
    rw [materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy)] at hmat
    cases hmat
  | sstep_exit _ _ x8' eff m' evs' code _ hv hspec hh' _ =>
    -- munmap leaves haltedness unchanged
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, hm, _⟩ := munmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    subst hm
    rw [munmap_model_halted, Hh] at hh'
    cases hh'
  | sstep_killed _ _ x8' eff m' evs' sig _ hv hspec hk =>
    -- and unkilled, through `State.m_killed_of_m_halted_none`
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, hm, _⟩ := munmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    subst hm
    have Hhn : m_halted (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
        = none := by
      rw [munmap_model_halted]
      exact Hh
    rw [m_killed_of_m_halted_none _ Hhn] at hk
    cases hk
  | sstep_syscall_unmodeled _ _ x8' _ hv hspec =>
    rw [Hsvc] at hv
    cases hv
    exact absurd hspec (munmap_no_unmodeled segs ms x8 model Hno Hargs)

/-! ## Trace characterization of `twm`

The omni reading of `twm`: one mutual induction gives the exact trace,
termination and error-freedom for every chunking of every write node. -/

def twm_post (bufs : List (List byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o => tr = wevents bufs ++ [ExitEv code fs] ∧ exits_with code tr o

def twm_rest_post (rest : List byte) (bufs : List (List byte)) (code : word)
    (fs : Fs.Fs) : post :=
  fun tr o => tr = List.map (WriteEv (Z_to_bv 64 1)) rest ++ (wevents bufs ++ [ExitEv code fs])
    ∧ exits_with code tr o

theorem twm_exec_mut (segs : List Segment) :
    (∀ ms model bufs code, twm segs ms model bufs code →
      bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      exec segs (config.mkCfg ms model) (twm_post bufs code (m_fs model))) ∧
    (∀ ms model rest bufs code, twm_pend segs ms model rest bufs code →
      buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      exec segs (config.mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))) ∧
    (∀ ms model rest bufs code, twm_tail segs ms model rest bufs code →
      buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      exec segs (config.mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))) := by
  refine twm_mutind segs
    (fun ms model bufs code =>
      bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      exec segs (config.mkCfg ms model) (twm_post bufs code (m_fs model)))
    (fun ms model rest bufs code =>
      buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      exec segs (config.mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
    (fun ms model rest bufs code =>
      buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      exec segs (config.mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- twm_exit
    intro ms model x8 Hsvc Hx8 _ Hh _ _
    apply exec_step_only segs _ _
      [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (config.mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))
    · exact sstep.sstep_exit ms model x8 _ _ [] _ Hh Hsvc
        (exit_dispatch_ok _ model Hx8) rfl rfl
    · intro evs st Hss
      exact sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss
    · apply exec.exec_halt
      · simp only [m_halted_with_halted, ne_eq, reduceCtorEq, not_false_eq_true]
      · exact And.intro rfl (And.intro (m_halted_with_halted _ _) (m_killed_with_halted _ _))
  · -- twm_write: the write node contributes the full buffer
    intro ms model buf bufs code _ _ IH Hbm Hh Hlazy Hfd
    have Hb : buf_modeled buf := Hbm buf List.mem_cons_self
    have Hbs : bufs_modeled bufs := fun b hb => Hbm b (List.mem_cons_of_mem _ hb)
    refine exec_conseq _ _ _ _ (IH Hb Hbs Hh Hlazy Hfd) ?_
    rintro tr o ⟨Heq, Hx⟩
    refine And.intro ?_ Hx
    rw [Heq]
    simp only [wevents, List.append_assoc]
  · -- twm_munmap
    intro ms model x8 bufs code Hsvc Hno Hargs _ IH Hbm Hh Hlazy Hfd
    have Hh' : m_halted (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
        = none := by
      rw [munmap_model_halted]
      exact Hh
    have Hfd' : fd1chan (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) :=
      munmap_model_fd1chan _ _ _ Hfd
    apply exec_step_only segs _ _ []
      (config.mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
    · exact sstep.sstep_syscall ms model x8 (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        Hh Hsvc (munmap_ok segs ms x8 model Hno Hargs) Hh'
        (materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy))
    · intro evs st Hss
      exact sstep_munmap_inv segs ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss
    · refine exec_conseq _ _ _ _ (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') ?_
      rintro tr o ⟨Heq, Hx⟩
      refine And.intro ?_ Hx
      rw [List.nil_append, Heq, munmap_model_fs]
  · -- twm_step
    intro ms ms' model bufs code Hsvc Hstep _ IH Hbm Hh Hlazy Hfd
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    · intro evs st Hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss
    · exact IH Hbm Hh Hlazy Hfd
  · -- twmp_write: every delivered length is a successor
    intro ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb _ IH Hbr Hbm Hh Hlazy Hfd
    refine exec.exec_step _ _ Hh ?_ ?_ ?_
    · exact ⟨_, _, sstep.sstep_syscall ms model x8
        (with_copyins [(ms_gpr ms 1, rest.length)]
          (mkEffect (len_word (rest.take rest.length)) [] [])) model model
        (List.map (WriteEv (Z_to_bv 64 1)) (rest.take rest.length)) Hh Hsvc
        (write1_ok_n segs ms x8 model rest rest.length Hfd Hno Hg Hr Hbr Hnb (Nat.le_refl _))
        Hh (materialize_model_accesses_no_lazy model _ Hlazy)⟩
    · intro evs Hss
      obtain ⟨_, _, _, _, Habs⟩ :=
        sstep_write_inv segs ms model x8 rest evs SError Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss
      cases Habs
    · intro evs c' Hss
      obtain ⟨n, Hn1, Hn2, Hevs, Hc'⟩ :=
        sstep_write_inv segs ms model x8 rest evs (SNext c') Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr
          Hnb Hss
      subst Hevs
      cases Hc'
      refine exec_conseq _ _ _ _
        (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) ?_
      rintro tr o ⟨Heq, Hx⟩
      refine And.intro ?_ Hx
      rw [Heq, ← List.append_assoc, ← List.map_append, List.take_append_drop]
  · -- twmt_done
    intro ms model bufs code _ IH _ Hbm Hh Hlazy Hfd
    refine exec_conseq _ _ _ _ (IH Hbm Hh Hlazy Hfd) ?_
    rintro tr o ⟨Heq, Hx⟩
    refine And.intro ?_ Hx
    rw [Heq, List.map_nil, List.nil_append]
  · -- twmt_more
    intro ms model rest bufs code _ _ IH Hbr Hbm Hh Hlazy Hfd
    exact IH Hbr Hbm Hh Hlazy Hfd
  · -- twmt_step
    intro ms ms' model rest bufs code Hsvc Hstep _ IH Hbr Hbm Hh Hlazy Hfd
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    · intro evs st Hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss
    · exact IH Hbr Hbm Hh Hlazy Hfd

theorem twm_exec (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code) :
    bufs_modeled bufs →
    m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    exec segs (config.mkCfg ms model) (twm_post bufs code (m_fs model)) :=
  (twm_exec_mut segs).1 ms model bufs code Hte

theorem twm_star_admits (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) :
    ∃ c, star segs (config.mkCfg ms model) (wevents bufs ++ [ExitEv code (m_fs model)]) c := by
  obtain ⟨tr, o, Hm, Heq, Hx⟩ :=
    exec_realizes _ _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
  cases o with
  | OError _ => exact False.elim Hx
  | OHalt c' =>
    subst Heq
    exact ⟨c', (mexec_halt_star _ _ _ _ Hm c' rfl).1⟩

theorem twm_star_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) :
    ∀ tr c, star segs (config.mkCfg ms model) tr c →
      is_prefix tr (wevents bufs ++ [ExitEv code (m_fs model)]) := by
  intro tr c Hstar
  obtain ⟨tr', o, _, Heq, _⟩ :=
    exec_realizes _ _ _
      (exec_star _ _ _ _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar)
  rw [← Heq]
  exact is_prefix_app _ _

/-! ## tmw: deterministic prefix, then the branching mmap -/

inductive tmw (segs : List Segment) :
    machine_state → Model → List (List byte) → word → List (List byte) → word → Prop
  | tmw_mmap : ∀ ms model x8 bf cf bs cs,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 222 →
      mmap_args_ok ms →
      (∀ e, e ∈ mmap_errnos →
        twm segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) →
      (∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true →
        twm segs
          (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
          (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) →
      (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) →
      tmw segs ms model bf cf bs cs
  | tmw_step : ∀ ms ms' model bf cf bs cs,
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      tmw segs ms' model bf cf bs cs →
      tmw segs ms model bf cf bs cs

/-- Rocq's generated induction principle for `tmw` (no induction
hypothesis through `tmw_mmap`'s `twm` premises). -/
theorem tmw_ind (segs : List Segment)
    (P : machine_state → Model → List (List byte) → word → List (List byte) → word → Prop)
    (f : ∀ ms model x8 bf cf bs cs, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 222 →
      mmap_args_ok ms →
      (∀ e, e ∈ mmap_errnos →
        twm segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) →
      (∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true →
        twm segs
          (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
          (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) →
      (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) →
      P ms model bf cf bs cs)
    (f0 : ∀ ms ms' model bf cf bs cs, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      tmw segs ms' model bf cf bs cs → P ms' model bf cf bs cs → P ms model bf cf bs cs) :
    ∀ m m0 l w l0 w0, tmw segs m m0 l w l0 w0 → P m m0 l w l0 w0 := by
  intro m m0 l w l0 w0 h
  exact tmw.rec (motive := fun ms model bf cf bs cs _ => P ms model bf cf bs cs) f f0 h

theorem msteps_tmw (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (H : msteps segs ms ms') (Hw : tmw segs ms' model bf cf bs cs) :
    tmw segs ms model bf cf bs cs := by
  induction H with
  | mst_refl _ => exact Hw
  | mst_step ms1 ms2 _ Hsvc Hstep _ ih =>
    exact tmw.tmw_step ms1 ms2 model bf cf bs cs Hsvc Hstep (ih Hw)

/-- Raw-ecall-record constructor for the mmap node: the register file and
memory are exposed, and the two continuations are collapsed to `mkst`
form (`adv_set` / `adv_mmap_grant`). -/
theorem tmw_mmap_rec (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (H17 : bv_unsigned (getr regs 17) = 222)
    (H11 : reg_get regs 11 ≠ Z_to_bv 64 0)
    (H12 : reg_get regs 12 = Z_to_bv 64 3)
    (H13 : reg_get regs 13 = Z_to_bv 64 34)
    (H14 : reg_get regs 14 = Z_to_bv 64 (-1))
    (H15 : reg_get regs 15 = Z_to_bv 64 0)
    (Hfail : ∀ e, e ∈ mmap_errnos →
      twm segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf)
    (Hsucc : ∀ a, grant_ok (reg_get regs 10) model a
        (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true →
      twm segs (mkst (regupd regs 10 a) (v_addi pc 4)
          (zfill a (page_round_up (reg_get regs 11)) mem) rom)
        (mmap_model a (page_round_up (reg_get regs 11)) model) bs cs)
    (Hex : ∃ a, grant_ok (reg_get regs 10) model a
        (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) :
    tmw segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      model bf cf bs cs := by
  have E10 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 := by decide
  have E11 : (Z_to_bv 5 (10 + ((1 : Nat) : Int)) : reg) = 11 := by decide
  have E12 : (Z_to_bv 5 (10 + ((2 : Nat) : Int)) : reg) = 12 := by decide
  have E13 : (Z_to_bv 5 (10 + ((3 : Nat) : Int)) : reg) = 13 := by decide
  have E14 : (Z_to_bv 5 (10 + ((4 : Nat) : Int)) : reg) = 14 := by decide
  have E15 : (Z_to_bv 5 (10 + ((5 : Nat) : Int)) : reg) = 15 := by decide
  -- the argument registers, read through `ms_gpr` of the raw record
  have G : ∀ (k : Nat) (r : reg), (Z_to_bv 5 (10 + ((k : Nat) : Int)) : reg) = r →
      ms_gpr
        { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
          ms_svc_pending := some (getr regs 17), ms_resv := none,
          ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } k = reg_get regs r := by
    intro k r Hk
    exact congrArg (reg_get regs) Hk
  refine tmw.tmw_mmap _ model (getr regs 17) bf cf bs cs rfl H17 ?_ ?_ ?_ ?_
  · unfold mmap_args_ok
    rw [G 1 11 E11, G 2 12 E12, G 3 13 E13, G 4 14 E14, G 5 15 E15]
    exact ⟨H11, H12, H13, H14, H15⟩
  · intro e HIn
    rw [adv_set]
    exact Hfail e HIn
  · intro a Hg
    rw [G 0 10 E10, G 1 11 E11] at Hg
    rw [G 1 11 E11, adv_mmap_grant]
    exact Hsucc a Hg
  · rw [G 0 10 E10, G 1 11 E11]
    exact Hex

/-! ## One-step inversion for the mmap config -/

theorem sstep_mmap_inv (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 222)
    (Hargs : mmap_args_ok ms)
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    evs = [] ∧
      ((∃ e, e ∈ mmap_errnos ∧
          st = SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) ∨
       (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ∧
          st = SNext (config.mkCfg
            (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
            (mmap_model a (page_round_up (ms_gpr ms 1)) model)))) := by
  cases Hss with
  | sstep_instr _ _ _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_syscall _ _ x8' eff m' m'' evs' _ hv hspec _ hmat =>
    rw [Hsvc] at hv
    cases hv
    obtain ⟨Hevs, Hcase⟩ := mmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    subst Hevs
    refine ⟨rfl, ?_⟩
    rcases Hcase with ⟨e, HIn, rfl, rfl⟩ | ⟨a, Hg, rfl, rfl⟩
    · rw [materialize_model_accesses_no_lazy _ _ Hlazy] at hmat
      cases hmat
      refine Or.inl ⟨e, HIn, ?_⟩
      rw [apply_effect_no_write]
    · rw [materialize_model_accesses_no_lazy _ _
        ((mmap_model_lazy a (page_round_up (ms_gpr ms 1)) model).trans Hlazy)] at hmat
      cases hmat
      exact Or.inr ⟨a, Hg, rfl⟩
  | sstep_syscall_materialization_fault _ _ x8' eff m' evs' _ hv hspec _ hmat =>
    -- no lazy range can fault
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, Hcase⟩ := mmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    rcases Hcase with ⟨_, _, _, rfl⟩ | ⟨a, _, _, rfl⟩
    · rw [materialize_model_accesses_no_lazy _ _ Hlazy] at hmat
      cases hmat
    · rw [materialize_model_accesses_no_lazy _ _
        ((mmap_model_lazy a (page_round_up (ms_gpr ms 1)) model).trans Hlazy)] at hmat
      cases hmat
  | sstep_exit _ _ x8' eff m' evs' code _ hv hspec hh' _ =>
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, Hcase⟩ := mmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    rcases Hcase with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · rw [Hh] at hh'
      cases hh'
    · rw [mmap_model_halted, Hh] at hh'
      cases hh'
  | sstep_killed _ _ x8' eff m' evs' sig _ hv hspec hk =>
    -- the same two shapes, through `State.m_killed_of_m_halted_none`
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, Hcase⟩ := mmap_ok_inv segs ms x8 model eff m' _ Hno Hargs hspec
    rcases Hcase with ⟨_, _, _, rfl⟩ | ⟨a, _, _, rfl⟩
    · rw [m_killed_of_m_halted_none _ Hh] at hk
      cases hk
    · have Hhn : m_halted (mmap_model a (page_round_up (ms_gpr ms 1)) model) = none := by
        rw [mmap_model_halted]
        exact Hh
      rw [m_killed_of_m_halted_none _ Hhn] at hk
      cases hk
  | sstep_syscall_unmodeled _ _ x8' _ hv hspec =>
    rw [Hsvc] at hv
    cases hv
    exact absurd hspec (mmap_no_unmodeled segs ms x8 model Hno Hargs)

/-! ## Trace characterization of `tmw` -/

/-- The omni reading of `tmw`: every execution takes one of the two
branches at the mmap node and then runs its `twm` straight line. -/
def tmw_post (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (fs : Fs.Fs) : post :=
  fun tr o => (tr = wevents bf ++ [ExitEv cf fs] ∧ exits_with cf tr o) ∨
    (tr = wevents bs ++ [ExitEv cs fs] ∧ exits_with cs tr o)

theorem tmw_exec (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) :
    bufs_modeled bf → bufs_modeled bs →
    m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    exec segs (config.mkCfg ms model) (tmw_post bf cf bs cs (m_fs model)) := by
  induction Hte with
  | tmw_mmap ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc _ =>
    -- the errno branches and the grants are exactly the successors
    intro Hbf Hbs Hh Hlazy Hfd
    refine exec.exec_step _ _ Hh ?_ ?_ ?_
    · exact ⟨_, _, sstep.sstep_syscall ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model
        model [] Hh Hsvc (mmap_fail_ok segs ms x8 model ENOMEM Hno Hargs ENOMEM_in_mmap_errnos)
        Hh (materialize_model_accesses_no_lazy _ _ Hlazy)⟩
    · intro evs Hss
      obtain ⟨_, ⟨_, _, Habs⟩ | ⟨_, _, Habs⟩⟩ :=
        sstep_mmap_inv segs ms model x8 evs SError Hh Hlazy Hsvc Hno Hargs Hss
      · cases Habs
      · cases Habs
    · intro evs c' Hss
      obtain ⟨rfl, ⟨e, He, Hc'⟩ | ⟨a, Hg, Hc'⟩⟩ :=
        sstep_mmap_inv segs ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hargs Hss
      · -- failure: the first straight line
        cases Hc'
        refine exec_conseq _ _ _ _ (twm_exec segs _ _ _ _ (Hfail e He) Hbf Hh Hlazy Hfd) ?_
        rintro tr o ⟨Heq, Hx⟩
        exact Or.inl ⟨Heq, Hx⟩
      · -- success: the second, at the mapped model
        cases Hc'
        have Hh' : m_halted (mmap_model a (page_round_up (ms_gpr ms 1)) model) = none := by
          rw [mmap_model_halted]
          exact Hh
        have Hfd' : fd1chan (mmap_model a (page_round_up (ms_gpr ms 1)) model) :=
          mmap_model_fd1chan _ _ _ Hfd
        refine exec_conseq _ _ _ _ (twm_exec segs _ _ _ _ (Hsucc a Hg) Hbs Hh'
          ((mmap_model_lazy _ _ _).trans Hlazy) Hfd') ?_
        rintro tr o ⟨Heq, Hx⟩
        refine Or.inr (And.intro ?_ Hx)
        rw [List.nil_append, Heq, mmap_model_fs]
  | tmw_step ms ms' model bf cf bs cs Hsvc Hstep _ IH =>
    intro Hbf Hbs Hh Hlazy Hfd
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    · intro evs st Hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss
    · exact IH Hbf Hbs Hh Hlazy Hfd

theorem tmw_star_admits_fail (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) :
    bufs_modeled bf →
    m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∃ c, star segs (config.mkCfg ms model) (wevents bf ++ [ExitEv cf (m_fs model)]) c := by
  induction Hte with
  | tmw_mmap ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail _ _ =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨c, Hstar⟩ :=
      twm_star_admits segs _ _ _ _ (Hfail ENOMEM ENOMEM_in_mmap_errnos) Hbm Hh Hlazy Hfd
    rw [← apply_effect_no_write] at Hstar
    refine ⟨c, ?_⟩
    have Hs := sstep.sstep_syscall ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model model []
      Hh Hsvc (mmap_fail_ok segs ms x8 model ENOMEM Hno Hargs ENOMEM_in_mmap_errnos) Hh
      (materialize_model_accesses_no_lazy _ _ Hlazy)
    have H := star.star_step _ _ _ _ _ Hs Hstar
    exact H
  | tmw_step ms ms' model bf cf bs cs Hsvc Hstep _ IH =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨c, Hstar⟩ := IH Hbm Hh Hlazy Hfd
    refine ⟨c, ?_⟩
    have Hs : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model)) :=
      sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    have H := star.star_step _ _ _ _ _ Hs Hstar
    exact H

theorem tmw_star_admits_succ (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) :
    bufs_modeled bs →
    m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∃ c, star segs (config.mkCfg ms model) (wevents bs ++ [ExitEv cs (m_fs model)]) c := by
  induction Hte with
  | tmw_mmap ms model x8 bf cf bs cs Hsvc Hno Hargs _ Hsucc Hex =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨a, Hg⟩ := Hex
    have Hh' : m_halted (mmap_model a (page_round_up (ms_gpr ms 1)) model) = none := by
      rw [mmap_model_halted]
      exact Hh
    have Hfd' : fd1chan (mmap_model a (page_round_up (ms_gpr ms 1)) model) :=
      mmap_model_fd1chan _ _ _ Hfd
    have Hlazy' : m_vm_lazy (mmap_model a (page_round_up (ms_gpr ms 1)) model) = [] :=
      (mmap_model_lazy _ _ _).trans Hlazy
    obtain ⟨c, Hstar⟩ := twm_star_admits segs _ _ _ _ (Hsucc a Hg) Hbm Hh' Hlazy' Hfd'
    rw [mmap_model_fs] at Hstar
    refine ⟨c, ?_⟩
    have Hs := sstep.sstep_syscall ms model x8
      (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
      (mmap_model a (page_round_up (ms_gpr ms 1)) model)
      (mmap_model a (page_round_up (ms_gpr ms 1)) model) []
      Hh Hsvc (mmap_succ_ok segs ms x8 model a Hno Hargs Hg) Hh'
      (materialize_model_accesses_no_lazy _ _ Hlazy')
    have H := star.star_step _ _ _ _ _ Hs Hstar
    exact H
  | tmw_step ms ms' model bf cf bs cs Hsvc Hstep _ IH =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨c, Hstar⟩ := IH Hbm Hh Hlazy Hfd
    refine ⟨c, ?_⟩
    have Hs : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model)) :=
      sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    have H := star.star_step _ _ _ _ _ Hs Hstar
    exact H

/-- The two candidate traces. -/
def two_traces (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (fs : Fs.Fs) (tr : List event) : Prop :=
  is_prefix tr (wevents bf ++ [ExitEv cf fs]) ∨ is_prefix tr (wevents bs ++ [ExitEv cs fs])

theorem tmw_star_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) :
    ∀ tr c, star segs (config.mkCfg ms model) tr c → two_traces bf cf bs cs (m_fs model) tr := by
  intro tr c Hstar
  obtain ⟨tr', o, _, ⟨Heq, _⟩ | ⟨Heq, _⟩⟩ :=
    exec_realizes _ _ _
      (exec_star _ _ _ _ _ (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) Hstar)
  · refine Or.inl ?_
    rw [← Heq]
    exact is_prefix_app _ _
  · refine Or.inr ?_
    rw [← Heq]
    exact is_prefix_app _ _

/-! ## No-error characterization -/

/-- No-error: a corollary of `tmw_exec`. -/
theorem tmw_no_error (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    ¬ reaches_error segs (config.mkCfg ms model) := by
  apply exec_no_error
  refine exec_conseq _ _ _ _ (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) ?_
  rintro tr o (⟨_, Hx⟩ | ⟨_, Hx⟩)
  · exact exits_with_never_errors _ _ _ Hx
  · exact exits_with_never_errors _ _ _ Hx

/-- The judgments name the outcome, so the other readings of the same runs
are refuted: neither shape errors, `twm` exits with no other code, and
neither branch of `tmw` alone is the whole run when the two traces are not
prefixes of one another. -/
theorem twm_exec_not_errors (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) :
    ¬ exec segs (config.mkCfg ms model) OmniRun.errors := by
  intro Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes _ _ _ Hex
  obtain ⟨_, Hx⟩ :=
    exec_sound _ _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm
  exact exits_with_never_errors _ _ _ Hx Herr

theorem twm_exec_code_unique (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) :
    ∀ code', exec segs (config.mkCfg ms model) (exits_with code') → code' = code := by
  intro code' Hex
  obtain ⟨tr, o, Hm, _, Hx⟩ :=
    exec_realizes _ _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
  cases o with
  | OError _ => exact False.elim Hx
  | OHalt c' =>
    have Hx' := exec_sound _ _ _ Hex _ _ Hm
    obtain ⟨Hx1, _⟩ := Hx
    obtain ⟨Hx1', _⟩ := Hx'
    rw [Hx1] at Hx1'
    exact (Option.some.inj Hx1').symm

theorem tmw_exec_not_errors (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) :
    ¬ exec segs (config.mkCfg ms model) OmniRun.errors := by
  intro Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes _ _ _ Hex
  obtain ⟨_, Hx⟩ | ⟨_, Hx⟩ :=
    exec_sound _ _ _ (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) _ _ Hm
  · exact exits_with_never_errors _ _ _ Hx Herr
  · exact exits_with_never_errors _ _ _ Hx Herr

/-- The single-trace reading of the failure tail is refuted when the
success trace is not a prefix of it: the success branch is realized. -/
theorem tmw_exec_not_fail_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hnp : ¬ is_prefix (wevents bs ++ [ExitEv cs (m_fs model)])
      (wevents bf ++ [ExitEv cf (m_fs model)])) :
    ¬ exec segs (config.mkCfg ms model) (twm_post bf cf (m_fs model)) := by
  intro Hex
  obtain ⟨c, Hstar⟩ := tmw_star_admits_succ segs ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd
  obtain ⟨tr', o, _, Heq, _⟩ := exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)
  apply Hnp
  rw [← Heq]
  exact is_prefix_app _ _

theorem tmw_exec_not_succ_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hnp : ¬ is_prefix (wevents bf ++ [ExitEv cf (m_fs model)])
      (wevents bs ++ [ExitEv cs (m_fs model)])) :
    ¬ exec segs (config.mkCfg ms model) (twm_post bs cs (m_fs model)) := by
  intro Hex
  obtain ⟨c, Hstar⟩ := tmw_star_admits_fail segs ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd
  obtain ⟨tr', o, _, Heq, _⟩ := exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)
  apply Hnp
  rw [← Heq]
  exact is_prefix_app _ _

/-! ## Run-level packaging and the equivalence glue -/

theorem two_traces_prefix_closed (bf : List (List byte)) (cf : word) (bs : List (List byte))
    (cs : word) (fs : Fs.Fs) (tr tr' : List event)
    (H : two_traces bf cf bs cs fs tr) (Hp : is_prefix tr' tr) :
    two_traces bf cf bs cs fs tr' := by
  rcases H with H | H
  · exact Or.inl (is_prefix_trans _ _ _ Hp H)
  · exact Or.inr (is_prefix_trans _ _ _ Hp H)

theorem mmap_obs_iff_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
      ↔ two_traces bf cf bs cs inp.in_fs tr := by
  intro tr
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none := rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] := rfl
  have Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp) := rfl
  have Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = inp.in_fs := rfl
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    have H2 := tmw_star_only segs _ _ bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd tr' c Hstar
    rw [Hfs] at H2
    exact two_traces_prefix_closed bf cf bs cs _ tr' tr H2 Hp
  · rintro (Hp | Hp)
    · obtain ⟨c, Hstar⟩ := tmw_star_admits_fail segs _ _ bf cf bs cs Hte Hbf Hh Hlazy Hfd
      rw [Hfs] at Hstar
      exact ⟨wevents bf ++ [ExitEv cf inp.in_fs], c, Hstar, Hp⟩
    · obtain ⟨c, Hstar⟩ := tmw_star_admits_succ segs _ _ bf cf bs cs Hte Hbs Hh Hlazy Hfd
      rw [Hfs] at Hstar
      exact ⟨wevents bs ++ [ExitEv cs inp.in_fs], c, Hstar, Hp⟩

theorem mmap_no_error_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) :=
  tmw_no_error segs _ (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs
    rfl rfl rfl Hte Hbf Hbs

/-- The run-level omni judgment of a fail-or-succeed mmap run. -/
theorem mmap_omni_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      (tmw_post bf cf bs cs inp.in_fs) :=
  tmw_exec segs _ _ bf cf bs cs Hte Hbf Hbs rfl rfl rfl

/-- The omni equivalence for two one-mmap binaries whose failure tails and
success tails agree, at the two role budgets. -/
theorem mmap_omni_strong_equiv_te (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word) (inp : ProcInput)
    (Hsource : tmw source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      bf cf bs cs)
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · refine coexec_conseq _ _ _ _
      (exec_coexec _ _ _ (mmap_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp bf cf bs cs Hsource Hbf Hbs)) ?_
    rintro tr o (⟨_, Hx⟩ | ⟨_, Hx⟩)
    · exact never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)
    · exact never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)
  · refine (trace_equiv_iff_omni _ _ _ _ _ _ _).1 ?_
    intro tr
    exact (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp
        bf cf bs cs Hsource Hbf Hbs tr).trans
      (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bf cf bs cs Htarget Hbf Hbs tr).symm
  · exact (bh_errors_iff (Image.mkImage target_segs apc aph) target_alloc_limit
      (ExecEntry.mkEntry asp abrk amb arnd) inp).1
      (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bf cf bs cs Htarget Hbf Hbs)

/-- The `Equivalence`-level equivalence for two one-mmap binaries whose
failure tails and success tails agree. -/
theorem mmap_strong_equiv_te (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (alim : Int)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word) (inp : ProcInput)
    (Hsource : tmw source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) bf cf bs cs)
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    modeled (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
    ∧ equiv (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
            (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd)
              inp) := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact no_error_no_unmodeled _ _
      (mmap_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
        Hsource Hbf Hbs)
  · intro tr
    exact (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
        Hsource Hbf Hbs tr).trans
      (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
        Htarget Hbf Hbs tr).symm
  · exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
      Htarget Hbf Hbs
end LinuxProcessSemantics.Common.MmapSim
