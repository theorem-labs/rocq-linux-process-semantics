import LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.SimInv
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.WallSim

/-! rocq-baseline: 7ba58b45f168d97ca1a555a98fa3b36f29eb5b81 -/

/-! # Common.AllocSim — union-of-resolutions glue for brk-allocating binaries

Ported from `theories/Common/AllocSim.v`, with the Rocq statements
(ticket E-proof-library-2a).  The file was read at the commit named
above (`nightly/09-28-2026`).

Why a brk-allocating binary's behaviour is a union over the kernel's brk
resolutions, and what a `to_outcomes` leaf pins, is argued in the Rocq
file's header.  The `CatSim` and `WallSim` names this file reaches beyond
#1298's ports are appended to those files, in their sections headed
"Additions for E-proof-library-2a", except `to_wexit`, which ticket
E-proof-library-2c appended to `CatSim.lean` with its induction principle
`to_wexit_ind`.

Representation spellings:
- Rocq `Z` is `Int`.  Rocq's `Z.leb` and `Z.ltb` inside a boolean are the
  decided `≤` and `<`, and `if (a <? b)` is `if a < b`.
- Rocq `Forall P l` is `∀ p ∈ l, P p`.
- Rocq's `Section WithSegs` variable `segs` is an explicit leading
  argument of `to_outcomes` and of the section's lemmas that use it.
  Rocq's generated `to_outcomes_ind` is stated as a theorem after
  `to_outcomes`, as `ExitSim.to_exit_ind` is.  Rocq's SProp eliminator
  `to_outcomes_sind` is not ported (Lean has no SProp).
- The local `brk_grow_ok` and `brk_r_ok` shadow the spec's names, as in
  Rocq; their bodies and the lemmas that unfold them spell the spec's
  definitions `Sys.Mm.Mmap.brk_grow_ok` and `Sys.Mm.Mmap.brk_r_ok`.
- Rocq's stdpp `Z_to_bv_bv_unsigned` is the shared width-64
  `PropExec.Z_to_bv_bv_unsigned64`. -/

namespace LinuxProcessSemantics.Common.AllocSim

open LinuxProcessSemantics.Riscv.Prelude
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
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.ExitSim (sstep_instr_inv)

/-! ## Local word-algebra helpers -/

/-- Unsigned value of a non-wrapping `bv` sum. -/
theorem u_add_small (a b : word) (H : bv_unsigned a + bv_unsigned b < 2 ^ 64) :
    bv_unsigned (a + b) = bv_unsigned a + bv_unsigned b := by
  rw [bv_unsigned_add, bv_wrap64_mod]
  have ha := u64_range a
  have hb := u64_range b
  exact Int.emod_eq_of_lt (by omega) H

theorem word_add_0_r (a : word) : a + Z_to_bv 64 0 = a := by
  have h0 : Z_to_bv 64 0 = (0 : word) := by decide
  rw [h0]
  exact BitVec.add_zero a

/-- `r + t - r = t` in the additive group of `bv 64` (no side conditions). -/
theorem word_add_sub_cancel (r t : word) : r + t - r = t := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem word_neq0_unsigned (r : word) (Hne : r ≠ Z_to_bv 64 0) : bv_unsigned r ≠ 0 := by
  intro Hu
  apply Hne
  apply bv_eq_of_unsigned
  rw [Hu, u_zero64]

/-- Address-walk step for `wbytes_app` (`nat_to_word` offset form). -/
theorem word_add_nat_S (a : word) (k : Nat) :
    (a + 1) + nat_to_word k = a + nat_to_word (k + 1) := by
  unfold nat_to_word Z_to_bv
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  exact add_offset_succ a k

/-! ## apply_zeros / zmem: the zero-backed grant as a functional overlay -/

/-- The zero-fill of a single granted range `[b, b+l)`.  Coverage is
checked in `Int` over unsigned values, mirroring `Run.zeros_cover`. -/
def zmem (mem : word → Option byte) (b l : word) : word → Option byte :=
  fun a => if bv_unsigned b ≤ bv_unsigned a && bv_unsigned a < bv_unsigned b + bv_unsigned l
           then some (Z_to_bv 8 0) else mem a

theorem apply_zeros_nil (mem : word → Option byte) : apply_zeros mem [] = mem := rfl

theorem apply_zeros_one (mem : word → Option byte) (b l : word) :
    apply_zeros mem [(b, l)] = zmem mem b l := by
  funext a
  simp only [apply_zeros, zeros_cover, zmem, List.any_cons, List.any_nil, Bool.or_false]

theorem zmem_out (mem : word → Option byte) (b l a : word)
    (Hd : bv_unsigned a < bv_unsigned b ∨ bv_unsigned b + bv_unsigned l ≤ bv_unsigned a) :
    zmem mem b l a = mem a := by
  unfold zmem
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · rfl

/-- The no-overflow hypothesis is inherited from `rdn_ext`. -/
theorem rdn_zmem_out (segs : List Segment) (mem : word → Option byte) (b l a : word) (n : Nat)
    (Hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (Hd : bv_unsigned a + (n : Int) ≤ bv_unsigned b
      ∨ bv_unsigned b + bv_unsigned l ≤ bv_unsigned a) :
    rdn segs (zmem mem b l) a n = rdn segs mem a n := by
  apply rdn_ext segs n _ _ a Hnw
  intro x Hx
  apply zmem_out
  omega

theorem rdn_zmem_in1 (segs : List Segment) (mem : word → Option byte) (b l a : word)
    (H : bv_unsigned b ≤ bv_unsigned a ∧ bv_unsigned a < bv_unsigned b + bv_unsigned l) :
    rdn segs (zmem mem b l) a 1 = some [Z_to_bv 8 0] := by
  have hz : zmem mem b l a = some (Z_to_bv 8 0) := by
    unfold zmem
    rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact H)]
  simp only [rdn, hz]

/-- `wbytes` over a split list, so that a store loop accumulates one flat
`wbytes` over the granted region. -/
theorem wbytes_app {bs1 bs2 : List byte} (m : word → Option byte) (a : word) :
    wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word bs1.length) bs2 := by
  induction bs1 generalizing m a with
  | nil => simp only [List.nil_append, wbytes, List.length_nil, word_add_0]
  | cons b bs1 ih =>
    simp only [List.cons_append, wbytes, List.length_cons]
    rw [ih, word_add_nat_S]

/-! ## Model plumbing for a brk transition -/

theorem with_vmmaps_fds (h : VmMaps) (m : Model) : m_fds (with_vmmaps h m) = m_fds m := rfl
theorem with_vmmaps_fs (h : VmMaps) (m : Model) : m_fs (with_vmmaps h m) = m_fs m := rfl
theorem with_vmmaps_halted (h : VmMaps) (m : Model) :
    m_halted (with_vmmaps h m) = m_halted m := rfl
theorem with_vmmaps_vm (h : VmMaps) (m : Model) : m_vmmaps (with_vmmaps h m) = h := rfl
theorem with_vmmaps_lazy (h : VmMaps) (m : Model) :
    m_vm_lazy (with_vmmaps h m) = m_vm_lazy m := rfl

theorem fd1chan_with_vmmaps (h : VmMaps) (m : Model) (H : fd1chan m) :
    fd1chan (with_vmmaps h m) := H

/-- VM lifecycle cleanup rewrites the sparse-backing ledgers and carries
the fd table across unchanged. -/
theorem fd1chan_forget_vm_ranges (ranges : List (word × word)) (m : Model) (H : fd1chan m) :
    fd1chan (forget_vm_ranges ranges m) := by
  induction ranges generalizing m with
  | nil => exact H
  | cons p ranges ih =>
    obtain ⟨a, n⟩ := p
    simp only [forget_vm_ranges]
    exact ih _ H

/-- advance-past-svc of a brk effect applied at the raw ecall record. -/
theorem adv_brk (regs : bvmap 5 word) (pc x8 : word) (mem rom : word → Option byte) (r : word)
    (zs : List (word × word)) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc, ms_svc_pending := some x8,
        ms_resv := none, ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (mkEffect r [] zs))
    = mkst (regupd regs 10 r) (v_addi pc 4) (apply_zeros mem zs) rom := by
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  have hf : Z_to_bv 32 0 = (0 : BitVec 32) := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte,
    apply_writes, apply_copies, apply_unmaps, ms_pc, mkst, regupd, hf, b_npc4]

/-! ## brk syscall-spec decoding, through the verified checker -/

theorem in_sysno_sys_input214 (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 := rfl

theorem in_arg0_sys_input214 (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl

/-- Which arm answers this number, on the spec side.  `syscall_spec` is
`dispatch spec_table`, so fixing the number settles the table lookup by
conversion, as `CatSim.syscall_spec_write` does for `write`.  See #580. -/
theorem syscall_spec_brk (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome SyscallEffect)
    (Hno : bv_unsigned x8 = 214) :
    syscall_spec (sys_input segs ms x8) model o ↔
      brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o := by
  unfold syscall_spec dispatch
  rw [in_sysno_sys_input214, Hno]
  exact Iff.rfl

/-- The allocator examples have no lazy mappings or materialized sparse
pages; this packages a VM ledger with that empty backing state for the
pure outcome algebra below. -/
def vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] none none none

def brk_grow_ok (h : VmMaps) (req r : word) : Bool :=
  Sys.Mm.Mmap.brk_grow_ok (vm_model h) req r

/-- The admissibility condition used by the pure allocator outcome algebra. -/
def brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  Sys.Mm.Mmap.brk_r_ok (vm_model h) req r = true

/-- The corresponding condition at a live syscall state, whose backing
ledger is part of the decision. -/
def brk_resolution_ok (m : Model) (req r : word) : Prop :=
  Sys.Mm.Mmap.brk_r_ok m req r = true

/-- The model after adopting resolution `r`. -/
def brk_model (req r : word) (m : Model) : Model :=
  with_brk_next m req r

/-- Stated at `brk_model` rather than at its `with_vmmaps` core, so that a
proof stepping over a brk node need not know how `with_brk_next` is
layered. -/
theorem fd1chan_brk_model (req r : word) (m : Model) (H : fd1chan m) :
    fd1chan (brk_model req r m) := by
  unfold brk_model with_brk_next
  exact fd1chan_forget_vm_ranges _ _ (fd1chan_with_vmmaps _ _ H)

theorem check_brk_ok_inv (req : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_brk req eff m = CheckOk m' evs) :
    eff = SyscallEffect.mkEffectU eff.eff_ret []
            (brk_zeros req eff.eff_ret (m_vmmaps m).vm_brk)
            (brk_unmaps eff.eff_ret (m_vmmaps m).vm_brk) [] []
    ∧ evs = []
    ∧ brk_resolution_ok m req eff.eff_ret
    ∧ m' = brk_model req eff.eff_ret m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases cs <;> cases ci <;> simp only [check_brk, reduceCtorEq] at H
  by_cases hc : (Sys.Mm.Mmap.brk_r_ok m req r
      && listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk)
      && listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
  · simp only [hc, ↓reduceIte, check_result.CheckOk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hr, hz⟩, hu⟩ := hc
    rw [listNN_eqb_eq] at hz hu
    subst hz hu
    exact ⟨rfl, rfl, hr, rfl⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at H

theorem check_brk_ok_intro (req r : word) (m : Model) (HR : brk_resolution_ok m req r) :
    check_brk req (SyscallEffect.mkEffectU r [] (brk_zeros req r (m_vmmaps m).vm_brk)
                    (brk_unmaps r (m_vmmaps m).vm_brk) [] []) m
      = CheckOk (brk_model req r m) [] := by
  unfold brk_resolution_ok at HR
  have hz := (listNN_eqb_eq (brk_zeros req r (m_vmmaps m).vm_brk) _).mpr rfl
  have hu := (listNN_eqb_eq (brk_unmaps r (m_vmmaps m).vm_brk) _).mpr rfl
  simp only [check_brk, HR, hz, hu, Bool.and_self, ↓reduceIte, brk_model]

/-- Admissible outcomes of a brk syscall, in terms of the resolved `r`. -/
theorem brk_ok_iff (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event) (Hno : bv_unsigned x8 = 214) :
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ↔
      (eff = SyscallEffect.mkEffectU eff.eff_ret []
              (brk_zeros (ms_gpr ms 0) eff.eff_ret (m_vmmaps model).vm_brk)
              (brk_unmaps eff.eff_ret (m_vmmaps model).vm_brk) [] []
       ∧ evs = []
       ∧ brk_resolution_ok model (ms_gpr ms 0) eff.eff_ret
       ∧ model' = brk_model (ms_gpr ms 0) eff.eff_ret model) := by
  constructor
  · intro H
    have H1 := (syscall_spec_brk segs ms x8 model _ Hno).1 H
    exact check_brk_ok_inv _ _ _ _ _ (check_brk_complete_ok _ _ _ _ _ _ H1)
  · rintro ⟨Heff, rfl, Hok, rfl⟩
    apply (syscall_spec_brk segs ms x8 model _ Hno).2
    apply check_brk_sound_ok
    have H := check_brk_ok_intro _ _ _ Hok
    rw [← Heff] at H
    exact H

theorem brk_ok_intro (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (r : word) (Hno : bv_unsigned x8 = 214) (Hok : brk_resolution_ok model (ms_gpr ms 0) r) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (SyscallEffect.mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
                                   (brk_unmaps r (m_vmmaps model).vm_brk) [] [])
          (brk_model (ms_gpr ms 0) r model) []) :=
  (brk_ok_iff segs ms x8 model _ _ _ Hno).2 ⟨rfl, rfl, Hok, rfl⟩

/-- A brk ecall has no `Unmodeled` outcome. -/
theorem brk_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : bv_unsigned x8 = 214) :
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro H
  have H1 := (syscall_spec_brk segs ms x8 model _ Hno).1 H
  have H2 := check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] []) H1
  simp only [check_brk] at H2
  split at H2 <;> cases H2

/-- brk is receptive: keeping the current break is an admissible
resolution.  The query/invalid arm returns it, and the shrink and grow
arms have a failure branch that keeps it. -/
theorem brk_receptive (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : bv_unsigned x8 = 214) :
    ∃ eff model', syscall_spec (sys_input segs ms x8) model (Ok eff model' []) := by
  refine ⟨_, _, brk_ok_intro segs ms x8 model (m_vmmaps model).vm_brk Hno ?_⟩
  unfold brk_resolution_ok
  have hb : bv_eqb (m_vmmaps model).vm_brk (m_vmmaps model).vm_brk = true :=
    (bv_eqb_eq _ _).mpr rfl
  simp only [Sys.Mm.Mmap.brk_r_ok, Sys.Mm.Mmap.brk_grow_ok, hb, Bool.or_true, Bool.and_true,
    Int.lt_irrefl, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ite_self]

/-- A brk grow of `req ≠ 0` from an established nonzero break to `r` above
it: the visible zero-fill is the shared page-rounded range helper. -/
theorem brk_zeros_grow (req r old : word) (Hreq : req ≠ Z_to_bv 64 0)
    (Hold : 0 < bv_unsigned old) (Hlt : bv_unsigned old < bv_unsigned r) :
    brk_zeros req r old =
      brk_page_range (page_round_up_Z (bv_unsigned old)) (page_round_up_Z (bv_unsigned r)) := by
  have E1 : w_is0 req = false := bv_eqb_neq _ _ Hreq
  simp only [brk_zeros, brk_is_grow, E1, Bool.not_false, Hold, decide_true, Bool.and_self, Hlt,
    ↓reduceIte]

/-- The logical ledger stays byte-granular across the same grow. -/
theorem brk_grants_grow (req r old : word) (Hreq : req ≠ Z_to_bv 64 0)
    (Hold : 0 < bv_unsigned old) (Hlt : bv_unsigned old < bv_unsigned r) :
    brk_grants req r old = [(old, r - old)] := by
  have E1 : w_is0 req = false := bv_eqb_neq _ _ Hreq
  simp only [brk_grants, brk_is_grow, E1, Bool.not_false, Hold, decide_true, Bool.and_self, Hlt,
    ↓reduceIte]

theorem brk_zeros_query (r old : word) : brk_zeros (Z_to_bv 64 0) r old = [] := by
  have E : w_is0 (Z_to_bv 64 0) = true := (bv_eqb_eq _ _).mpr rfl
  simp only [brk_zeros, brk_is_grow, E, Bool.not_true, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]

theorem brk_grants_query (r old : word) : brk_grants (Z_to_bv 64 0) r old = [] := by
  have E : w_is0 (Z_to_bv 64 0) = true := (bv_eqb_eq _ _).mpr rfl
  simp only [brk_grants, brk_is_grow, E, Bool.not_true, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]

theorem brk_zeros_keep (req old : word) : brk_zeros req old old = [] := by
  simp only [brk_zeros, brk_is_grow, Int.lt_irrefl, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

theorem brk_grants_keep (req old : word) : brk_grants req old old = [] := by
  simp only [brk_grants, brk_is_grow, Int.lt_irrefl, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- brk keeps the break: the freed list is empty. -/
theorem brk_unmaps_keep (old : word) : brk_unmaps old old = [] := by
  simp only [brk_unmaps, brk_page_range, Int.lt_irrefl, ↓reduceIte, ite_self]

/-- The query resolution has an empty freed list — the same
`r = vm_brk h` premise `brk_model_query` takes, so a query node
discharges both from it. -/
theorem brk_unmaps_query (h : VmMaps) (r : word) (H : r = h.vm_brk) :
    brk_unmaps r h.vm_brk = [] := by
  subst H
  exact brk_unmaps_keep _

/-- A resolution that does not lower the break has an empty freed list:
page rounding is monotone, so the freed interval is empty.  This covers
the query/invalid path (`r = old`) and both grow resolutions. -/
theorem brk_unmaps_grow (r old : word) (H : bv_unsigned old ≤ bv_unsigned r) :
    brk_unmaps r old = [] := by
  have E := page_round_up_Z_mono _ _ H
  simp only [brk_unmaps, brk_page_range,
    show ¬ (page_round_up_Z (bv_unsigned r) < page_round_up_Z (bv_unsigned old)) by omega,
    ↓reduceIte, ite_self]

/-- Unfolding `brk_grow_ok` on an actual grow. -/
theorem brk_grow_ok_grow (h : VmMaps) (req r : word) (_Hreq : req ≠ Z_to_bv 64 0)
    (H0 : 0 < bv_unsigned h.vm_brk) (Hlt : bv_unsigned h.vm_brk < bv_unsigned r) :
    brk_grow_ok h req r
      = ((if page_round_up_Z (bv_unsigned h.vm_brk) < page_round_up_Z (bv_unsigned r)
          then page_round_up_Z (bv_unsigned r) ≤ alloc_top h
               && region_free (h.vm_reserved ++ h.vm_maps)
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned h.vm_brk)))
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                                 - page_round_up_Z (bv_unsigned h.vm_brk)))
          else true)
         && (vm_backed_bytes h + bv_unsigned (r - h.vm_brk) ≤ h.vm_limit)) := by
  have Hmaps : m_vmmaps (vm_model h) = h := rfl
  have Hbacked : vm_backing_used (vm_model h) = vm_backed_bytes h := by
    show live_bytes (maps_subtract_all (vm_backed_maps h) [])
        + (([] : List word).length : Int) * page_size = live_bytes (vm_backed_maps h)
    simp only [maps_subtract_all, List.length_nil, Int.natCast_zero, Int.zero_mul, Int.add_zero]
  simp only [brk_grow_ok, Sys.Mm.Mmap.brk_grow_ok, Sys.Mm.Mmap.brk_budget_ok, Hmaps, Hbacked,
    H0, Hlt, decide_true, Bool.and_self, ↓reduceIte]

theorem brk_grow_ok_keep (h : VmMaps) (req : word) : brk_grow_ok h req h.vm_brk = true := by
  have Hmaps : m_vmmaps (vm_model h) = h := rfl
  simp only [brk_grow_ok, Sys.Mm.Mmap.brk_grow_ok, Hmaps, Int.lt_irrefl, decide_false,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- Elementary page-rounding facts used by the allocator examples. -/
theorem page_round_up_Z_aligned (z : Int) (_Hz : 0 ≤ z) (Hmod : z % page_size = 0) :
    page_round_up_Z z = z := by
  unfold page_round_up_Z page_size at *
  omega

theorem page_round_up_Z_bounds (z : Int) (_Hz : 0 ≤ z) :
    z ≤ page_round_up_Z z ∧ page_round_up_Z z ≤ z + page_size - 1 := by
  unfold page_round_up_Z page_size
  omega

/-- Eight-byte chunk rounding is contained in page rounding. -/
theorem round8_le_page_round (z : Int) (_Hz : 0 ≤ z) :
    ((z + 7) / 8) * 8 ≤ page_round_up_Z z := by
  unfold page_round_up_Z page_size
  omega

theorem round8_le_page_grant (old n : Int) (_Hold : 0 ≤ old) (_Hn : 0 ≤ n)
    (Hmod : old % page_size = 0) :
    ((n + 7) / 8) * 8 ≤ page_round_up_Z (old + n) - old := by
  unfold page_round_up_Z page_size at *
  omega

/-- A prefix of a free interval with the same base is free. -/
theorem region_free_prefix (maps : List (word × word)) (b small big : word)
    (Hle : bv_unsigned small ≤ bv_unsigned big) (Hfree : region_free maps b big = true) :
    region_free maps b small = true := by
  induction maps with
  | nil => rfl
  | cons p maps ih =>
    obtain ⟨a, sz⟩ := p
    simp only [region_free, iv_overlap, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at Hfree ⊢
    obtain ⟨Hhead, Htail⟩ := Hfree
    refine ⟨?_, ih Htail⟩
    rcases Hhead with H | H
    · exact Or.inl H
    · exact Or.inr (by omega)

/-- On a page-aligned established break, a genuine grow crosses into a
nonempty physical page interval.  This is the proof-facing spelling of
`brk_grow_ok`: physical ceiling and disjointness, then the logical
budget. -/
theorem brk_grow_ok_aligned_grow (h : VmMaps) (req r : word) (Hreq : req ≠ Z_to_bv 64 0)
    (Hpos : 0 < bv_unsigned h.vm_brk) (Hlt : bv_unsigned h.vm_brk < bv_unsigned r)
    (Halign : bv_unsigned h.vm_brk % page_size = 0) :
    brk_grow_ok h req r
      = ((page_round_up_Z (bv_unsigned r) ≤ alloc_top h
          && region_free (h.vm_reserved ++ h.vm_maps) h.vm_brk
               (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                            - bv_unsigned h.vm_brk)))
         && (vm_backed_bytes h + bv_unsigned (r - h.vm_brk) ≤ h.vm_limit)) := by
  rw [brk_grow_ok_grow h req r Hreq Hpos Hlt,
    page_round_up_Z_aligned (bv_unsigned h.vm_brk) (by omega) Halign]
  have Hround : bv_unsigned h.vm_brk < page_round_up_Z (bv_unsigned r) := by
    have := page_round_up_Z_bounds (bv_unsigned r) (by omega)
    omega
  rw [ite_eq_left Hround, Z_to_bv_bv_unsigned64]

theorem brk_zeros_aligned_grow (req r old : word) (Hreq : req ≠ Z_to_bv 64 0)
    (Hpos : 0 < bv_unsigned old) (Hlt : bv_unsigned old < bv_unsigned r)
    (Halign : bv_unsigned old % page_size = 0) :
    brk_zeros req r old =
      [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - bv_unsigned old))] := by
  rw [brk_zeros_grow req r old Hreq Hpos Hlt,
    page_round_up_Z_aligned (bv_unsigned old) (by omega) Halign]
  have Hround : bv_unsigned old < page_round_up_Z (bv_unsigned r) := by
    have := page_round_up_Z_bounds (bv_unsigned r) (by omega)
    omega
  unfold brk_page_range
  rw [ite_eq_left Hround, Z_to_bv_bv_unsigned64]

/-- What a caller needs about the page-rounded grant a successful grow
from `r` to `r + w` hands back, from what the brk spec leaves on the
table: the new break fits under the run's grant top, and the granted
pages and the page above them are free.  For a nonzero `w` from a
nonzero page-aligned `r`, that is the range `Mmap.brk_grow_ok` tests.
Otherwise `Hfree` asks for more: the gate tests no range from `r = 0`,
at `w = 0`, or when `r` and `r + w` round up to the same page, and on
any other grow from an unaligned `r` it tests a range starting above
`r`.  Why `top` and `ceil` are parameters is argued on the Rocq
lemma. -/
theorem brk_aligned_grant_ok (res : List (word × word)) (r w g : word) (top ceil : Int)
    (Hnowrap : bv_unsigned (r + w) = bv_unsigned r + bv_unsigned w)
    (Htop : bv_unsigned (r + w) = top)
    (Hg : g = Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r))
    (Hacp : ceil + page_size < 2 ^ 64)
    (Hceil : page_round_up_Z (bv_unsigned (r + w)) ≤ ceil)
    (Hfree : region_free res r
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                   - bv_unsigned r)) = true) :
    bv_unsigned g = page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r
    ∧ bv_unsigned w ≤ bv_unsigned g
    ∧ bv_unsigned r + bv_unsigned g ≤ ceil
    ∧ top ≤ ceil
    ∧ region_free res r w = true
    ∧ region_free res r g = true := by
  have hr := u64_range r
  have hw := u64_range w
  have hb := page_round_up_Z_bounds (bv_unsigned (r + w)) (u64_range (r + w)).1
  have Hps : (0 : Int) < page_size := by unfold page_size; omega
  -- Rocq reproves `StepTac.u_Z2bv` here, its `StepTac.v` importing
  -- `MmapSim.v`, which imports `AllocSim.v`.  The port follows Rocq,
  -- although the Lean `StepTac` does not import this file.
  have Hu : ∀ z : Int, 0 ≤ z → z < 2 ^ 64 → bv_unsigned (Z_to_bv 64 z) = z := by
    intro z Hlo Hhi
    rw [Z_to_bv_unsigned, bv_wrap64_mod]
    exact Int.emod_eq_of_lt Hlo Hhi
  have HgU : bv_unsigned g = page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r := by
    subst Hg
    exact Hu _ (by omega) (by omega)
  refine ⟨HgU, by omega, by omega, by omega, ?_, ?_⟩
  -- the gate tests one page more than the grant, so both the request and
  -- the grant are prefixes of the range `Hfree` covers
  · exact region_free_prefix res r w _
      (by rw [Hu _ (by omega) (by omega)]; omega) Hfree
  · exact region_free_prefix res r g _
      (by rw [HgU, Hu _ (by omega) (by omega)]; omega) Hfree

/-! ## Two-node brk resolution-set algebra

A binary that queries the break (`req = 0`), then grows it by `t` bytes
(`req = brk + t`), taking the failure exit `([], 4)` on an unusable query
resolution or a refused or wrapping grow, and the success buffers `bufs`
otherwise.  Which examples share this shape, and why `t = 0` is handled
explicitly, is argued in the Rocq file. -/

/-- Can the break grow from `r` by `t` bytes, against reservation list
`reserved`, grant top `top` (the run's `State.alloc_top`) and allocation
budget `lim`?  The free region is the installed pages plus the page
above them, as in `Mmap.brk_grow_ok`.  `t = 0` (re-requesting the current
break) is growable without the top, free-region or budget check. -/
def growable (reserved : List (word × word)) (lim top : Int) (t r : word) : Prop :=
  r ≠ Z_to_bv 64 0 ∧ bv_unsigned r + bv_unsigned t < 2 ^ 64 ∧
  (t = Z_to_bv 64 0 ∨
   ((if page_round_up_Z (bv_unsigned r) < page_round_up_Z (bv_unsigned r + bv_unsigned t)
     then page_round_up_Z (bv_unsigned r + bv_unsigned t) ≤ top
          && region_free reserved
               (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
               (Z_to_bv 64 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                            + page_size - page_round_up_Z (bv_unsigned r)))
     else true)
    && (bv_unsigned t ≤ lim)) = true)

/-- Branch outcome set after the first brk resolved to `r`.  The exit-4
element is present iff a failing continuation exists: `r = 0`, address
wraparound, or `t ≠ 0` (`brk_r_ok` admits the old break at the second
brk, which misses the wanted `r + t`). -/
def T1 (reserved : List (word × word)) (lim top : Int) (t : word) (bufs : List (List byte))
    (r : word) : (List (List byte) × word) → Prop :=
  fun o => (o = ([], Z_to_bv 64 4) ∧
            (r = Z_to_bv 64 0 ∨ 2 ^ 64 ≤ bv_unsigned r + bv_unsigned t ∨ t ≠ Z_to_bv 64 0))
        ∨ (growable reserved lim top t r ∧ o = (bufs, Z_to_bv 64 0))

/-- Branch outcome set after the second brk resolved to `r2`. -/
def T2 (want : word) (bufs : List (List byte)) (r2 : word) :
    (List (List byte) × word) → Prop :=
  fun o => (r2 = want ∧ o = (bufs, Z_to_bv 64 0)) ∨ (r2 ≠ want ∧ o = ([], Z_to_bv 64 4))

/-- `brk_r_ok` at a query (`req = 0`) is deterministic: it admits `r`
exactly when `r` is the current break `vm_brk`. -/
theorem brk_r_ok_query_iff (h : VmMaps) (r : word) :
    brk_r_ok h (Z_to_bv 64 0) r ↔ r = h.vm_brk := by
  have E : w_is0 (Z_to_bv 64 0) = true := (bv_eqb_eq _ _).mpr rfl
  have Hmaps : m_vmmaps (vm_model h) = h := rfl
  simp only [brk_r_ok, Sys.Mm.Mmap.brk_r_ok, Hmaps, E, Bool.true_or, ↓reduceIte]
  exact bv_eqb_eq _ _

/-- `reserved_top` bounds the reservations from above — the shape the
ASLR-base bound `Run.valid_brk` hands a `region_free_above`-style
argument. -/
theorem reserved_top_above (reserved : List (word × word)) (r : Int)
    (Hr : reserved_top reserved ≤ r) :
    ∀ p ∈ reserved, bv_unsigned p.1 + bv_unsigned p.2 ≤ r := by
  induction reserved with
  | nil => intro p hp; cases hp
  | cons q l ih =>
    obtain ⟨a, sz⟩ := q
    simp only [reserved_top] at Hr
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Int.le_trans (Int.le_max_left _ _) Hr
    · exact ih (Int.le_trans (Int.le_max_right _ _) Hr) p hp

/-- A region at or above the image top is free of the reservations. -/
theorem region_free_above_top (reserved : List (word × word)) (lo n : word)
    (Hr : reserved_top reserved ≤ bv_unsigned lo) : region_free reserved lo n = true := by
  induction reserved with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨a, sz⟩ := q
    simp only [reserved_top] at Hr
    have H1 : bv_unsigned a + bv_unsigned sz ≤ bv_unsigned lo :=
      Int.le_trans (Int.le_max_left _ _) Hr
    have H2 : reserved_top l ≤ bv_unsigned lo := Int.le_trans (Int.le_max_right _ _) Hr
    have E : decide (bv_unsigned lo < bv_unsigned a + bv_unsigned sz) = false :=
      decide_eq_false (by omega)
    simp only [region_free, iv_overlap, E, Bool.false_and, Bool.not_false, Bool.true_and]
    exact ih H2

/-- A region above the listed reservations is free of them. -/
theorem region_free_above (l : List (word × word)) (lo n : word)
    (Hf : ∀ p ∈ l, bv_unsigned p.1 + bv_unsigned p.2 ≤ bv_unsigned lo) :
    region_free l lo n = true := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨a, sz⟩ := q
    have Ha : bv_unsigned a + bv_unsigned sz ≤ bv_unsigned lo := Hf (a, sz) List.mem_cons_self
    have E : decide (bv_unsigned lo < bv_unsigned a + bv_unsigned sz) = false :=
      decide_eq_false (by omega)
    simp only [region_free, iv_overlap, E, Bool.false_and, Bool.not_false, Bool.true_and]
    exact ih (fun p hp => Hf p (List.mem_cons_of_mem _ hp))

/-- A region below the listed reservations is free of them. -/
theorem region_free_below (l : List (word × word)) (lo n : word)
    (Hf : ∀ p ∈ l, bv_unsigned lo + bv_unsigned n ≤ bv_unsigned p.1) :
    region_free l lo n = true := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨a, sz⟩ := q
    have Ha : bv_unsigned lo + bv_unsigned n ≤ bv_unsigned a := Hf (a, sz) List.mem_cons_self
    have E : decide (bv_unsigned a < bv_unsigned lo + bv_unsigned n) = false :=
      decide_eq_false (by omega)
    simp only [region_free, iv_overlap, E, Bool.and_false, Bool.not_false, Bool.true_and]
    exact ih (fun p hp => Hf p (List.mem_cons_of_mem _ hp))

/-- The page-rounded disjunct of `growable`, for a page-aligned established
break `r` above the reservations, grown by a positive `t` that fits under
the physical ceiling and the budget.  Which grow sites hold these five
hypotheses, and why the ceiling is stated on `r + t + page_size - 1`, is
argued on the Rocq lemma. -/
theorem growable_aligned_grow (reserved : List (word × word)) (lim top : Int) (t r : word)
    (Halign : bv_unsigned r % page_size = 0)
    (Htop : reserved_top reserved ≤ bv_unsigned r)
    (Hpos : 0 < bv_unsigned t)
    (Hceil : bv_unsigned r + bv_unsigned t + page_size - 1 ≤ top)
    (Hlim : bv_unsigned t ≤ lim) :
    ((if page_round_up_Z (bv_unsigned r) < page_round_up_Z (bv_unsigned r + bv_unsigned t)
      then page_round_up_Z (bv_unsigned r + bv_unsigned t) ≤ top
           && region_free reserved
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                             + page_size - page_round_up_Z (bv_unsigned r)))
      else true)
     && (bv_unsigned t ≤ lim)) = true := by
  have Hr0 := (u64_range r).1
  rw [page_round_up_Z_aligned (bv_unsigned r) Hr0 Halign]
  have Hru := page_round_up_Z_bounds (bv_unsigned r + bv_unsigned t) (by omega)
  have Hltpage : bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t) := by omega
  rw [ite_eq_left Hltpage, Z_to_bv_bv_unsigned64, region_free_above_top reserved r _ Htop]
  simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, Hlim⟩

theorem brk_aslr_max_val : brk_aslr_max = 1073741824 := by
  unfold brk_aslr_max
  decide

/-- The model after a brk(0) query is unchanged up to re-tagging the
break: the resolution is the current break, and the granted and freed
lists are empty. -/
theorem brk_model_next_query (h : VmMaps) (r : word) (H : r = h.vm_brk) :
    brk_model_next h (Z_to_bv 64 0) r
      = VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps h.vm_noaccess h.vm_start_brk r
          h.vm_limit h.vm_mmap_base h.vm_init_sp := by
  subst H
  simp only [brk_model_next, brk_maps_next, Int.lt_irrefl, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, brk_grants_query, brk_unmaps_keep, List.nil_append,
    maps_subtract_ranges, List.foldl_nil]

theorem brk_model_query (r : word) (m : Model) (H : r = (m_vmmaps m).vm_brk) :
    brk_model (Z_to_bv 64 0) r m
      = with_vmmaps
          (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps
            (m_vmmaps m).vm_noaccess (m_vmmaps m).vm_start_brk r
            (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m := by
  subst H
  simp only [brk_model, with_brk_next, brk_unmaps_keep, forget_vm_ranges,
    brk_model_next_query (m_vmmaps m) (m_vmmaps m).vm_brk rfl]

/-- The grow-node decode: on an established break `r` with heap base
(`vm_start_brk`) `s`, `brk(req)` with `req` positive and at or above
both `s` and `r` resolves to `req` (grow) or `r` (kept), gated by
`brk_grow_ok`; the
query/invalid and shrink guards are excluded. -/
theorem brk_r_ok_grow_iff (reserved : List (word × word)) (lim : Int) (s r : word)
    (maps noaccess : List (word × word)) (mb sp req r2 : word)
    (Hpos : 0 < bv_unsigned req) (Hs : bv_unsigned s ≤ bv_unsigned req)
    (Hreq : bv_unsigned r ≤ bv_unsigned req) :
    brk_r_ok (VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 ↔
      (r2 = req ∨ r2 = r)
      ∧ brk_grow_ok (VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2
        = true := by
  have E0 : w_is0 req = false := by
    apply bv_eqb_neq
    intro He
    rw [He, u_zero64] at Hpos
    omega
  have Hmin : ¬ bv_unsigned req < bv_unsigned s := by omega
  have Hlt : ¬ bv_unsigned req < bv_unsigned r := by omega
  have Hmaps : m_vmmaps (vm_model (VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp))
      = VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp := rfl
  simp only [brk_r_ok, brk_grow_ok, Sys.Mm.Mmap.brk_r_ok, Hmaps, min_brk, E0, Bool.false_or,
    Hmin, Hlt, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    Bool.or_eq_true, bv_eqb_eq, iff_self]

/-- The ledger is spelled with a free `sp` (and an mmap base `mb` that
`brk_r_ok` does not read) because `brk_grow_ok` compares against
`State.alloc_top` of the ledger it
is handed: the `top` the set algebra was stated at has to be that ledger's,
`bv_unsigned sp - stack_max_size`. -/
theorem T1_iff_T2 (reserved : List (word × word)) (lim : Int) (s mb sp t : word)
    (bufs : List (List byte)) (r : word)
    (Hr0 : r ≠ Z_to_bv 64 0) (Hs : bv_unsigned s ≤ bv_unsigned r)
    (Hnw : bv_unsigned r + bv_unsigned t < 2 ^ 64) :
    ∀ o, T1 reserved lim (bv_unsigned sp - stack_max_size) t bufs r o ↔
      ∃ r2, brk_r_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
            ∧ T2 (r + t) bufs r2 o := by
  intro o
  have Hur := u64_range r
  have Hut := u64_range t
  have Hur0 := word_neq0_unsigned r Hr0
  have Huadd : bv_unsigned (r + t) = bv_unsigned r + bv_unsigned t := u_add_small r t Hnw
  have Hwant0 : r + t ≠ Z_to_bv 64 0 := by
    intro He
    have := congrArg bv_unsigned He
    rw [Huadd, u_zero64] at this
    omega
  have Bridge : ∀ r2,
      brk_r_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 ↔
        (r2 = r + t ∨ r2 = r)
        ∧ brk_grow_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 = true :=
    fun r2 => brk_r_ok_grow_iff reserved lim s r [] [] mb sp (r + t) r2
      (by omega) (by omega) (by omega)
  -- the grow gate of this ledger at `r + t`, in the spelling `growable` uses
  have Hgrow_eq : t ≠ Z_to_bv 64 0 →
      brk_grow_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) (r + t)
        = ((if page_round_up_Z (bv_unsigned r)
                < page_round_up_Z (bv_unsigned r + bv_unsigned t)
            then page_round_up_Z (bv_unsigned r + bv_unsigned t)
                   ≤ bv_unsigned sp - stack_max_size
                 && region_free reserved
                      (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                      (Z_to_bv 64 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                                   + page_size - page_round_up_Z (bv_unsigned r)))
            else true)
           && (bv_unsigned t ≤ lim)) := by
    intro Ht0
    have Hut0 := word_neq0_unsigned t Ht0
    have H0 : 0 < bv_unsigned r := by omega
    have Hlt : bv_unsigned r < bv_unsigned (r + t) := by rw [Huadd]; omega
    rw [brk_grow_ok_grow _ _ _ Hwant0 H0 Hlt]
    simp only [alloc_top, vm_backed_bytes, vm_backed_maps, maps_subtract_all, live_bytes,
      List.append_nil, word_add_sub_cancel, Huadd, Int.zero_add]
  constructor
  · intro H
    rcases H with ⟨rfl, Hcase⟩ | ⟨Hg, rfl⟩
    · -- exit 4: the failure resolution r2 = r, which exists iff t ≠ 0
      have Ht0 : t ≠ Z_to_bv 64 0 := by
        rcases Hcase with Hc | Hc | Hc
        · exact absurd Hc Hr0
        · omega
        · exact Hc
      have Hut0 := word_neq0_unsigned t Ht0
      refine ⟨r, (Bridge r).2 ⟨Or.inr rfl,
        brk_grow_ok_keep (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)⟩,
        Or.inr ⟨?_, rfl⟩⟩
      intro He
      have := congrArg bv_unsigned He
      rw [Huadd] at this
      omega
    · -- success: r2 = want
      obtain ⟨_, _, Hb⟩ := Hg
      refine ⟨r + t, (Bridge (r + t)).2 ⟨Or.inl rfl, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
      by_cases Hz : bv_unsigned t = 0
      · have Ht0 : t = Z_to_bv 64 0 := bv_eq_of_unsigned _ _ (by rw [Hz, u_zero64])
        rw [Ht0, word_add_0_r]
        exact brk_grow_ok_keep (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) r
      · rcases Hb with Hb | Hb
        · exact absurd (by rw [Hb, u_zero64]) Hz
        · rw [Hgrow_eq (fun Ht0 => Hz (by rw [Ht0, u_zero64]))]
          exact Hb
  · rintro ⟨r2, Hrok, Hb⟩
    obtain ⟨Hcase, Hgrow⟩ := (Bridge r2).1 Hrok
    rcases Hb with ⟨rfl, rfl⟩ | ⟨Hne, rfl⟩
    · -- success resolution
      refine Or.inr ⟨⟨Hr0, Hnw, ?_⟩, rfl⟩
      by_cases Hz : bv_unsigned t = 0
      · exact Or.inl (bv_eq_of_unsigned _ _ (by rw [Hz, u_zero64]))
      · refine Or.inr ?_
        rw [Hgrow_eq (fun Ht0 => Hz (by rw [Ht0, u_zero64]))] at Hgrow
        exact Hgrow
    · -- failure resolution: r2 = r, and t ≠ 0 or r2 = want
      refine Or.inl ⟨rfl, Or.inr (Or.inr ?_)⟩
      intro Ht0
      subst Ht0
      rw [word_add_0_r] at Hne Hcase
      rcases Hcase with Hc | Hc <;> exact Hne Hc

theorem T2_fail_iff (want : word) (bufs : List (List byte)) (r2 : word) (Hne : r2 ≠ want) :
    ∀ o, T2 want bufs r2 o ↔ o = ([], Z_to_bv 64 4) := by
  intro o
  unfold T2
  constructor
  · rintro (⟨Heq, _⟩ | ⟨_, Ho⟩)
    · exact absurd Heq Hne
    · exact Ho
  · intro Ho
    exact Or.inr ⟨Hne, Ho⟩

theorem T2_succ_iff (want : word) (bufs : List (List byte)) (o : List (List byte) × word) :
    T2 want bufs want o ↔ o = (bufs, Z_to_bv 64 0) := by
  unfold T2
  constructor
  · rintro (⟨_, Ho⟩ | ⟨Hne, _⟩)
    · exact Ho
    · exact absurd rfl Hne
  · intro Ho
    exact Or.inl ⟨rfl, Ho⟩

/-! ## to_outcomes: the exact outcome set of a brk-branching run -/

/-- From machine state `ms` and a running model `model` with no lazy
mappings, the reachable set of `(bufs, code)` outcomes is `U`.  The two
conditions, `m_halted model = none` and `m_vm_lazy model = []`, are
premises of `to_outcomes_exec` and of the `to_outcomes_*` theorems after
it, not of the judgment, and `init_model` meets both by `rfl`.  At a
halted model, whose configuration takes no step, the judgment can still
hold, naming outcomes outside what that configuration reaches, as
`to_outcomes_at_halted` pins.  Leaves are `WallSim.to_wallexit` retry
loops; an interior node is either an instruction step taken with no
syscall pending, which keeps `U`, or a brk syscall branching over the
admissible resolutions. -/
inductive to_outcomes (segs : List Segment) :
    machine_state → Model → ((List (List byte) × word) → Prop) → Prop
  | tou_wexit : ∀ ms model bufs code (U : (List (List byte) × word) → Prop),
      fd1chan model →
      to_wallexit segs (Z_to_bv 64 1) bufs code ms →
      bufs_modeled bufs →
      (∀ o, U o ↔ o = (bufs, code)) →
      to_outcomes segs ms model U
  | tou_step : ∀ ms ms' model U,
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      to_outcomes segs ms' model U →
      to_outcomes segs ms model U
  | tou_brk : ∀ ms model x8
      (T : SyscallEffect → Model → (List (List byte) × word) → Prop)
      (U : (List (List byte) × word) → Prop),
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 214 →
      (∀ eff model' evs,
         syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
         to_outcomes segs (advance_past_svc (apply_effect ms eff)) model' (T eff model')) →
      (∀ o, U o ↔
         (∃ eff model' evs,
            syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
            ∧ T eff model' o)) →
      to_outcomes segs ms model U

/-- Rocq's generated induction principle for `to_outcomes`, stated with
the Rocq statement for the reason `ExitSim.to_exit_ind` gives. -/
theorem to_outcomes_ind (segs : List Segment)
    (P : machine_state → Model → ((List (List byte) × word) → Prop) → Prop)
    (f : ∀ ms model bufs code (U : (List (List byte) × word) → Prop),
      fd1chan model → to_wallexit segs (Z_to_bv 64 1) bufs code ms → bufs_modeled bufs →
      (∀ o, U o ↔ o = (bufs, code)) → P ms model U)
    (f0 : ∀ ms ms' model U, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_outcomes segs ms' model U → P ms' model U → P ms model U)
    (f1 : ∀ ms model x8 (T : SyscallEffect → Model → (List (List byte) × word) → Prop)
      (U : (List (List byte) × word) → Prop),
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 214 →
      (∀ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        to_outcomes segs (advance_past_svc (apply_effect ms eff)) model' (T eff model')) →
      (∀ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        P (advance_past_svc (apply_effect ms eff)) model' (T eff model')) →
      (∀ o, U o ↔ ∃ eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ∧ T eff model' o) →
      P ms model U) :
    ∀ m m0 P0, to_outcomes segs m m0 P0 → P m m0 P0 := by
  intro m m0 P0 h
  induction h with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU => exact f ms model bufs code U Hfd Hte Hbm HU
  | tou_step ms ms' model U Hsvc Hstep Hto IH => exact f0 ms ms' model U Hsvc Hstep Hto IH
  | tou_brk ms model x8 T U Hsvc Hno Hcont HU IH =>
    exact f1 ms model x8 T U Hsvc Hno Hcont IH HU

/-- Prepend a deterministic instruction run. -/
theorem tou_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (H : msteps segs ms ms') (Ht : to_outcomes segs ms' model U) :
    to_outcomes segs ms model U := by
  induction H with
  | mst_refl _ => exact Ht
  | mst_step ms1 ms2 _ Hsvc Hstep _ ih =>
    exact to_outcomes.tou_step ms1 ms2 model U Hsvc Hstep (ih Ht)

/-- Forgetting VM ranges preserves the non-VM state and introduces no
sparse mappings. -/
theorem forget_vm_ranges_frame (ranges : List (word × word)) (model : Model) :
    m_halted (forget_vm_ranges ranges model) = m_halted model ∧
    m_fs (forget_vm_ranges ranges model) = m_fs model ∧
    m_fds (forget_vm_ranges ranges model) = m_fds model ∧
    (m_vm_lazy model = [] → m_vm_lazy (forget_vm_ranges ranges model) = []) := by
  induction ranges generalizing model with
  | nil => exact ⟨rfl, rfl, rfl, id⟩
  | cons p ranges ih =>
    obtain ⟨a, n⟩ := p
    obtain ⟨Hhalt, Hfs, Hfds, Hlazy⟩ :=
      ih (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) model)
    refine ⟨Hhalt, Hfs, Hfds, fun Hempty => Hlazy ?_⟩
    show maps_subtract (m_vm_lazy model) _ _ = []
    rw [Hempty]
    rfl

/-- brk transitions keep the model running and the fs and fds untouched.
Starting from a model with no lazy mappings, lifecycle cleanup also
leaves no lazy mappings. -/
theorem brk_step_shape (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hno : bv_unsigned x8 = 214)
    (Hs : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) :
    evs = [] ∧ m_halted model' = none ∧ m_fs model' = m_fs model
    ∧ m_fds model' = m_fds model
    ∧ m_vm_lazy model' = m_vm_lazy model := by
  obtain ⟨_, rfl, _, rfl⟩ := (brk_ok_iff segs ms x8 model eff model' evs Hno).1 Hs
  obtain ⟨Hhalt, Hfs, Hfds, Hlazy'⟩ := forget_vm_ranges_frame
    (brk_unmaps eff.eff_ret (m_vmmaps model).vm_brk)
    (with_vmmaps (brk_model_next (m_vmmaps model) (ms_gpr ms 0) eff.eff_ret) model)
  refine ⟨rfl, Hhalt.trans Hh, Hfs, Hfds, ?_⟩
  rw [Hlazy]
  exact Hlazy' Hlazy

/-- One-step inversion at a brk ecall. -/
theorem sstep_brk_inv (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 214)
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    ∃ eff model',
      syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ∧
      evs = [] ∧
      st = SNext (config.mkCfg (advance_past_svc (apply_effect ms eff)) model') := by
  cases Hss with
  | sstep_instr _ _ _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_syscall _ _ x8' eff m' m'' evs' _ hv hspec _ hmat =>
    rw [Hsvc] at hv
    cases hv
    obtain ⟨He, _, _, _, Hlazy'⟩ :=
      brk_step_shape segs ms x8 model eff m' _ Hh Hlazy Hno hspec
    subst He
    rw [materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy)] at hmat
    cases hmat
    exact ⟨eff, m', hspec, rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ x8' eff m' evs' _ hv hspec _ hmat =>
    -- no lazy range can fault
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, _, _, _, Hlazy'⟩ :=
      brk_step_shape segs ms x8 model eff m' _ Hh Hlazy Hno hspec
    rw [materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy)] at hmat
    cases hmat
  | sstep_exit _ _ x8' eff m' evs' code _ hv hspec hh' _ =>
    -- brk does not halt the model
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, Hm, _, _, _⟩ := brk_step_shape segs ms x8 model eff m' _ Hh Hlazy Hno hspec
    rw [Hm] at hh'
    cases hh'
  | sstep_killed _ _ x8' eff m' evs' sig _ hv hspec hk =>
    -- nor kill it
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, Hm, _, _, _⟩ := brk_step_shape segs ms x8 model eff m' _ Hh Hlazy Hno hspec
    rw [m_killed_of_m_halted_none _ Hm] at hk
    cases hk
  | sstep_syscall_unmodeled _ _ x8' _ hv hspec =>
    rw [Hsvc] at hv
    cases hv
    exact absurd hspec (brk_no_unmodeled segs ms x8 model Hno)

/-! ## Trace characterization -/

def outcome_trace (fs : Fs.Fs) (o : List (List byte) × word) : List event :=
  wevents o.1 ++ [ExitEv o.2 fs]

/-- The omni reading of a brk-branching run: an execution ends by halting
with one of the outcomes, having emitted that outcome's trace. -/
def outcomes_post (fs : Fs.Fs) (U : (List (List byte) × word) → Prop) : post :=
  fun tr o => ∃ out, U out ∧ tr = outcome_trace fs out ∧ exits_with out.2 tr o

/-- One induction over `to_outcomes`; the leaves are
`WallSim.to_wallexit_exec`, and the brk node's successors are the
admissible resolutions (`sstep_brk_inv`). -/
theorem to_outcomes_exec (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop) (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    exec segs (config.mkCfg ms model) (outcomes_post (m_fs model) U) := by
  induction Hto with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU =>
    refine exec_conseq _ _ _ _
      (to_wallexit_exec segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
        Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte) ?_
    rintro tr o ⟨Heq, Hx⟩
    refine Exists.intro (bufs, code) ⟨(HU _).2 rfl, ?_, Hx⟩
    rw [Heq, wevents_ch_fd1]
    rfl
  | tou_step ms ms' model U Hsvc Hstep _ IH =>
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    · intro evs st Hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss
    · exact exec_conseq _ _ _ _ (IH Hh Hlazy) (fun _ _ H => H)
  | tou_brk ms model x8 T U Hsvc Hno _ HU IH =>
    -- the resolutions the spec admits are the successors
    apply exec.exec_step _ _ Hh
    · obtain ⟨eff, model', Hspec⟩ := brk_receptive segs ms x8 model Hno
      obtain ⟨_, Hh', _, _, Hlazy'⟩ :=
        brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
      exact ⟨_, _, sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
        (materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy))⟩
    · intro evs Hss
      obtain ⟨_, _, _, _, Habs⟩ :=
        sstep_brk_inv segs ms model x8 evs SError Hh Hlazy Hsvc Hno Hss
      cases Habs
    · intro evs c' Hss
      obtain ⟨eff, model', Hspec, rfl, Hc'⟩ :=
        sstep_brk_inv segs ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hss
      cases Hc'
      obtain ⟨_, Hh', Hfs, _, Hlazy'⟩ :=
        brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
      refine exec_conseq _ _ _ _ (IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy)) ?_
      rintro tr o ⟨out, Hout, Heq, Hx⟩
      refine Exists.intro out ⟨(HU out).2 ⟨eff, model', [], Hspec, Hout⟩, ?_, Hx⟩
      rw [List.nil_append, Heq, Hfs]

/-- The judgment names the outcome, so a different reading of the same
run is refuted: no exit code outside the outcome set (this theorem), and
no silence (`to_outcomes_not_silent`, next). -/
theorem to_outcomes_no_other_exit (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop) (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (code' : word) (Hne : ∀ o, U o → o.2 ≠ code') :
    ¬ exec segs (config.mkCfg ms model) (exits_with code') := by
  intro Hex
  obtain ⟨tr, o, Hm, out, Hout, _, Hx⟩ :=
    exec_realizes _ _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy)
  cases o with
  | OError _ => exact Hx
  | OHalt c' =>
    have Hx' := exec_sound _ _ _ Hex _ _ Hm
    obtain ⟨Hx1, _⟩ := Hx
    obtain ⟨Hx1', _⟩ := Hx'
    rw [Hx1] at Hx1'
    exact Hne out Hout (Option.some.inj Hx1')

theorem to_outcomes_not_silent (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop) (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ¬ cosafe segs (config.mkCfg ms model) (fun tr => tr = []) := by
  intro Hc
  obtain ⟨tr, o, Hm, out, _, Heq, Hx⟩ :=
    exec_realizes _ _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy)
  cases o with
  | OError _ => exact Hx
  | OHalt c' =>
    obtain ⟨Hstar, _⟩ := mexec_halt_star _ _ _ _ Hm c' rfl
    have Hnil : tr = [] := cosafe_star _ _ (fun tr => tr = []) _ _ Hc Hstar
    rw [Heq] at Hnil
    simp only [outcome_trace, List.append_eq_nil_iff, List.cons_ne_self, and_false] at Hnil

theorem to_outcomes_star_only (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop) (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (tr : List event) (c : config) (Hstar : star segs (config.mkCfg ms model) tr c) :
    ∃ o, U o ∧ is_prefix tr (outcome_trace (m_fs model) o) := by
  obtain ⟨tr', _, _, out, Hout, Heq, _⟩ :=
    exec_realizes _ _ _
      (exec_star _ _ _ _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy) Hstar)
  refine ⟨out, Hout, ?_⟩
  rw [← Heq]
  exact is_prefix_app _ _

theorem to_outcomes_star_admits (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop) (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ∀ o, U o → ∃ c, star segs (config.mkCfg ms model) (outcome_trace (m_fs model) o) c := by
  induction Hto with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU =>
    intro o Ho
    obtain rfl := (HU o).1 Ho
    have H := to_wallexit_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms
      model Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte
    rw [wevents_ch_fd1] at H
    exact H
  | tou_step ms ms' model U Hsvc Hstep _ IH =>
    intro o Ho
    obtain ⟨c, Hstar⟩ := IH Hh Hlazy o Ho
    refine ⟨c, ?_⟩
    have Hs : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model)) :=
      sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    have H := star.star_step _ _ _ _ _ Hs Hstar
    exact H
  | tou_brk ms model x8 T U Hsvc Hno _ HU IH =>
    intro o Ho
    obtain ⟨eff, model', evs, Hspec, Ht⟩ := (HU o).1 Ho
    obtain ⟨Hevs, Hh', Hfs, _, Hlazy'⟩ :=
      brk_step_shape segs ms x8 model eff model' evs Hh Hlazy Hno Hspec
    subst Hevs
    obtain ⟨c, Hstar⟩ := IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy) o Ht
    refine ⟨c, ?_⟩
    have Hs := sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
      (materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy))
    have H := star.star_step _ _ _ _ _ Hs Hstar
    rw [Hfs] at H
    exact H

/-! ## No-error characterization -/

theorem to_outcomes_no_error (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop) (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ¬ reaches_error segs (config.mkCfg ms model) := by
  apply exec_no_error
  refine exec_conseq _ _ _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy) ?_
  rintro tr o ⟨out, _, _, Hx⟩
  exact exits_with_never_errors _ _ _ Hx

/-! ## Ergonomic brk node: stated on the resolved break value `r` -/

/-- `tou_brk` specialized to a continuation family indexed by the
resolved break `r`.  Per-binary proofs receive the admissibility facts on
`r`, the post state `advance_past_svc (apply_effect ms eff)` of that
resolution's effect, which sets `a0` to `r`, erases the freed pages
(`brk_unmaps`) and then zero-fills the granted ones (`brk_zeros`), and
the updated model, and return the branch outcome set `T' r`. -/
theorem tou_brk_r (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (T' : word → (List (List byte) × word) → Prop) (U : (List (List byte) × word) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 214)
    (Hcont : ∀ r, brk_resolution_ok model (ms_gpr ms 0) r →
      to_outcomes segs
        (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
                                   (brk_unmaps r (m_vmmaps model).vm_brk) [] [])))
        (brk_model (ms_gpr ms 0) r model)
        (T' r))
    (HU : ∀ o, U o ↔ ∃ r, brk_resolution_ok model (ms_gpr ms 0) r ∧ T' r o) :
    to_outcomes segs ms model U := by
  apply to_outcomes.tou_brk ms model x8 (fun eff _ => T' eff.eff_ret) U Hsvc Hno
  · intro eff model' evs Hspec
    obtain ⟨Heff, _, Hok, rfl⟩ := (brk_ok_iff segs ms x8 model eff model' evs Hno).1 Hspec
    have H := Hcont eff.eff_ret Hok
    rw [← Heff] at H
    exact H
  · intro o
    rw [HU]
    constructor
    · rintro ⟨r, Hok, Ht⟩
      exact ⟨_, _, [], brk_ok_intro segs ms x8 model r Hno Hok, Ht⟩
    · rintro ⟨eff, model', evs, Hspec, Ht⟩
      obtain ⟨_, _, Hok, _⟩ := (brk_ok_iff segs ms x8 model eff model' evs Hno).1 Hspec
      exact ⟨eff.eff_ret, Hok, Ht⟩

/-- Singleton leaf, ergonomic form. -/
theorem tou_wexit_eq (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word)
    (Hfd : fd1chan model) (Hte : to_wallexit segs (Z_to_bv 64 1) bufs code ms)
    (Hbm : bufs_modeled bufs) :
    to_outcomes segs ms model (fun o => o = (bufs, code)) :=
  to_outcomes.tou_wexit ms model bufs code _ Hfd Hte Hbm (fun _ => Iff.rfl)

/-- Lean-only pin of `to_outcomes`'s docstring sentence: a halted leaf can
satisfy the outcome judgment while its empty execution trace fails the outcome
postcondition. This declaration has no Rocq twin. -/
theorem to_outcomes_at_halted :
    let ms := { mkst bvmap_empty 0 (fun _ => none) (fun _ => none) with
      ms_svc_pending := some (Z_to_bv 64 93) }
    let model := with_halted 0
      (mkModel [(1, FdEntry.FdChannel 1)] (mkVmMaps [] [] 0 0 0) IEof [] none none none)
    let U := fun o : List (List byte) × word => o = ([], 0)
    to_outcomes [] ms model U ∧
      ¬ exec [] (config.mkCfg ms model) (outcomes_post (m_fs model) U) := by
  dsimp only
  constructor
  · apply tou_wexit_eq
    · rfl
    · exact to_wexit.tw_exit _ (Z_to_bv 64 93) rfl (Or.inl rfl)
    · intro b hb
      cases hb
  · intro hex
    obtain ⟨out, _, htr, _⟩ := exec_sound _ _ _ hex [] _
      (mexec.mexec_halt _ (by decide))
    simp only [outcome_trace, BitVec.ofNat_eq_ofNat, List.nil_eq,
      List.append_eq_nil_iff, List.cons_ne_self, and_false] at htr

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tou_equiv (segs : List Segment) (ms : machine_state) (model : Model)
    (U V : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U) (HV : ∀ o, V o ↔ U o) :
    to_outcomes segs ms model V := by
  induction Hto generalizing V with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU =>
    exact to_outcomes.tou_wexit ms model bufs code V Hfd Hte Hbm
      (fun o => (HV o).trans (HU o))
  | tou_step ms ms' model U Hsvc Hstep _ IH =>
    exact to_outcomes.tou_step ms ms' model V Hsvc Hstep (IH V HV)
  | tou_brk ms model x8 T U Hsvc Hno Hcont HU _ =>
    exact to_outcomes.tou_brk ms model x8 T V Hsvc Hno Hcont
      (fun o => (HV o).trans (HU o))

/-! ## Run-level packaging and the equivalence glue -/

/-- The run-level omni judgment of a brk-branching run. -/
theorem alloc_omni_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    omni_run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      (outcomes_post inp.in_fs U) :=
  to_outcomes_exec segs _ _ U Hto rfl rfl

theorem alloc_obs_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
      ↔ ∃ o, U o ∧ is_prefix tr (outcome_trace inp.in_fs o) := by
  intro tr
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none := rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] := rfl
  have Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = inp.in_fs := rfl
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨o, Ho, Hp'⟩ := to_outcomes_star_only segs _ _ U Hto Hh Hlazy tr' c Hstar
    rw [Hfs] at Hp'
    exact ⟨o, Ho, is_prefix_trans _ _ _ Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ := to_outcomes_star_admits segs _ _ U Hto Hh Hlazy o Ho
    rw [Hfs] at Hstar
    exact ⟨outcome_trace inp.in_fs o, c, Hstar, Hp⟩

theorem alloc_no_error_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  apply exec_no_error
  refine exec_conseq _ _ _ _ (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) ?_
  rintro tr o ⟨out, _, _, Hx⟩
  exact exits_with_never_errors _ _ _ Hx

/-- The omni equivalence for two brk-allocating binaries with the same
outcome set `U`, at the two role budgets. -/
theorem alloc_omni_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (U : (List (List byte) × word) → Prop) (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U)
    (Htarget : to_outcomes target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · refine coexec_conseq _ _ _ _
      (exec_coexec _ _ _ (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp U Hsource)) ?_
    rintro tr o ⟨out, _, _, Hx⟩
    exact never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)
  · refine (trace_equiv_iff_omni _ _ _ _ _ _ _).1 ?_
    intro tr
    exact (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U
        Hsource tr).trans
      (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U
        Htarget tr).symm
  · exact (bh_errors_iff (Image.mkImage target_segs apc aph) target_alloc_limit
      (ExecEntry.mkEntry asp abrk amb arnd) inp).1
      (alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget)

/-- The `Equivalence`-level equivalence for two brk-allocating binaries
with the same outcome set `U`, the two runs at their own quantified break
bases: `U` has to be base-independent, which `Run.valid_brk`'s bounds
give the examples. -/
theorem alloc_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (alim : Int)
    (U : (List (List byte) × word) → Prop) (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U)
    (Htarget : to_outcomes target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) U) :
    modeled (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
    ∧ equiv (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
            (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd)
              inp) := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact SimInv.no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource)
  · intro tr
    exact (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).trans
      (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
  · exact alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget

end LinuxProcessSemantics.Common.AllocSim
