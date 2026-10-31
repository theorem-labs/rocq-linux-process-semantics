import LinuxProcessSemantics.Common.SeqExec

/-! # Common.StreamExec — `write_to_mem` read-back and the read post-state

Ported from `theories/Common/StreamExec.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), with the Rocq statements.

The `write_to_mem` frame/read-back lemmas are thin corollaries of the
CatExec/SeqExec `wbytes` theory (the interpreter's byte writer IS
`wbytes`, `CatExec.write_to_mem_wbytes`); the wrapping `bv` address walk
gives them the CatExec-standard no-overflow hypotheses, trivially
discharged downstream.

Unported (cat1024_ns reaches none of them): `v_lui_4096`, `c_lts_0_0` and
`adv_apply_delivered`.  Rocq's file imports `ExitSim` and `CatSim`; the
ported part uses neither. -/

namespace LinuxProcessSemantics.Common.StreamExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.SeqExec

/-- Below the written region, `write_to_mem` leaves memory unchanged.
The no-overflow hypothesis `buf + length data ≤ 2^64` is needed
because the write walk is a wrapping `bv` add — mirrors
`CatExec.wbytes_below`. -/
theorem write_to_mem_below (data : List byte) (mem : word → Option byte) (buf a : word)
    (hnw : bv_unsigned buf + (data.length : Int) ≤ 2 ^ 64)
    (ha : bv_unsigned a < bv_unsigned buf) :
    write_to_mem mem buf data a = mem a := by
  rw [write_to_mem_wbytes]
  exact wbytes_below data mem buf a hnw ha

/-- Outside `[buf, buf + length data)`, `write_to_mem` leaves memory alone
(above-side companion of `write_to_mem_below`; no extra no-overflow
needed — `a < 2^64` already caps the walk). -/
theorem write_to_mem_above (data : List byte) (mem : word → Option byte) (buf a : word)
    (ha : bv_unsigned buf + (data.length : Int) ≤ bv_unsigned a) :
    write_to_mem mem buf data a = mem a := by
  rw [write_to_mem_wbytes]
  exact wbytes_above data mem buf a ha

/-- `rdn` reads through a disjoint `write_to_mem`.  The two no-overflow
hypotheses are the standard `rdn_ext`/`wbytes_below` ones. -/
theorem rdn_wtm_out (segs : List Segment) (data : List byte) (m : word → Option byte)
    (buf a : word) (n : Nat)
    (hna : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hnb : bv_unsigned buf + (data.length : Int) ≤ 2 ^ 64)
    (hd : bv_unsigned buf + (data.length : Int) ≤ bv_unsigned a ∨
      bv_unsigned a + (n : Int) ≤ bv_unsigned buf) :
    rdn segs (write_to_mem m buf data) a n = rdn segs m a n := by
  apply rdn_ext segs n _ _ a hna
  intro x hx
  rcases hd with hd | hd
  · exact write_to_mem_above data m buf x (by omega)
  · exact write_to_mem_below data m buf x hnb (by omega)

/-- `rdn` reads back exactly the bytes just written by `write_to_mem`
(no-overflow hypothesis, as in `SeqExec.rdn_wbytes_hit`). -/
theorem rdn_write_to_mem (segs : List Segment) (data : List byte) (mem : word → Option byte)
    (buf : word) (hnw : bv_unsigned buf + (data.length : Int) ≤ 2 ^ 64) :
    rdn segs (write_to_mem mem buf data) buf data.length = some data := by
  rw [write_to_mem_wbytes]
  exact rdn_wbytes_hit segs data mem buf hnw

/-- `advance_past_svc` of `apply_effect` with a single-buffer write effect
(the read post-state): sets x10 to the return value, advances pc by 4,
clears svc, and writes `data` into `ms_mem` at `buf`.  The input
record carries the (post-ecall) `ms_resv := none`. -/
theorem adv_apply_write (regs : bvmap 5 word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (ret buf : word) (data : List byte) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (mkEffect ret [(buf, data)] []))
    = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom := by
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  have hf : Z_to_bv 32 0 = (0 : BitVec 32) := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte,
    apply_writes, apply_copies, apply_zeros, apply_unmaps, ms_pc, mkst, regupd, hf, b_npc4]

end LinuxProcessSemantics.Common.StreamExec
