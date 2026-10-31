import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs
import LinuxProcessSemantics.Common.Hoare
import LinuxProcessSemantics.Common.MuslCall
import LinuxProcessSemantics.Common.SymTac

/-! rocq-baseline: 36031418350290d5d51fae6e71cbf0b73d7cc91e -/

/-! conditional-bug-ns: reuse the address-parametric musl write summary.
The blob is instantiated at CBB = 0x110fc using the generated fetch proofs.
Proof-side wrapper for the caller's write-all continuation. -/

namespace LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_hoare

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.Hoare
open LinuxProcessSemantics.Common.MuslCall
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_code
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def CBB : word := 0x110fc

theorem fetch_at (segs : List Segment) (b : word) (d : Int) (a : word) (w : BitVec 32)
    (ha : at_ b d = a) (hf : fetch_word segs a = some w) :
    fetch_word segs (at_ b d) = some w := by
  rw [ha]
  exact hf

theorem f00 : fetch_word source_segs (at_ CBB 0x00) = some Wsp16m := SF_110fc

theorem f04 : fetch_word source_segs (at_ CBB 0x04) = some Wmv_a3a2 := SF_11100

theorem f08 : fetch_word source_segs (at_ CBB 0x08) = some Wli_a6_0 := SF_11104

theorem f0c : fetch_word source_segs (at_ CBB 0x0c) = some Wmv_a2a1 := SF_11108

theorem f10 : fetch_word source_segs (at_ CBB 0x10) = some Wli_a5_0 := SF_1110c

theorem f14 : fetch_word source_segs (at_ CBB 0x14) = some Wmv_a1a0 := SF_11110

theorem f18 : fetch_word source_segs (at_ CBB 0x18) = some Wli_a4_0 := SF_11114

theorem f1c : fetch_word source_segs (at_ CBB 0x1c) = some Wli_a0_64 := SF_11118

theorem f20 : fetch_word source_segs (at_ CBB 0x20) = some Wsd_ra8 := SF_1111c

theorem f24 : fetch_word source_segs (at_ CBB 0x24) = some Wjal_cp := SF_11120

theorem f28 : fetch_word source_segs (at_ CBB 0x28) = some Wld_ra8 := SF_11124

theorem f2c : fetch_word source_segs (at_ CBB 0x2c) = some Wsp16p := SF_11128

theorem f30 : fetch_word source_segs (at_ CBB 0x30) = some Wj4 := SF_1112c

theorem f34 : fetch_word source_segs (at_ CBB 0x34) = some Wlui_a5 := SF_11130

theorem f38 : fetch_word source_segs (at_ CBB 0x38) = some Wbltu := SF_11134

theorem f3c : fetch_word source_segs (at_ CBB 0x3c) = some Wret := SF_11138

theorem f6c : fetch_word source_segs (at_ CBB 0x6c) = some Wmv_a7a0 := SF_11168

theorem f70 : fetch_word source_segs (at_ CBB 0x70) = some Wmv_a0a1 := SF_1116c

theorem f74 : fetch_word source_segs (at_ CBB 0x74) = some Wmv_a1a2 := SF_11170

theorem f78 : fetch_word source_segs (at_ CBB 0x78) = some Wmv_a2a3 := SF_11174

theorem f7c : fetch_word source_segs (at_ CBB 0x7c) = some Wmv_a3a4 := SF_11178

theorem f80 : fetch_word source_segs (at_ CBB 0x80) = some Wmv_a4a5 := SF_1117c

theorem f84 : fetch_word source_segs (at_ CBB 0x84) = some Wmv_a5a6 := SF_11180

theorem f88 : fetch_word source_segs (at_ CBB 0x88) = some Wecall := SF_11184

theorem f8c : fetch_word source_segs (at_ CBB 0x8c) = some Wret := SF_11188

theorem f90 : fetch_word source_segs (at_ CBB 0x90) = some Wj_cpc := SF_1118c

theorem cb_write_wall0
    (k : machine_state → Prop)
    (regs : bvmap 5 word) (mem rom : word → Option byte)
    (kra sp0 buf len : word) (out : List byte)
    (Hrom : rom = seg_rom source_segs)
    (Hk : ret_ok kra) (Hr28 : ret_ok (at_ CBB 0x28))
    (H1 : getr regs 1 = kra) (H2 : getr regs 2 = sp0)
    (H10 : getr regs 10 = Z_to_bv 64 1) (H11 : getr regs 11 = buf) (H12 : getr regs 12 = len)
    (Hok : store_ok source_segs mem (at_ sp0 (-8)) 8 = true)
    (Hnw : bv_unsigned (at_ sp0 (-8)) + 8 ≤ 2 ^ 64)
    (Hlen : bv_unsigned len ≤ 18446744073709547520)
    (Hread : rdn source_segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
      buf (word_to_nat len) = some out)
    (Hnb : 1 ≤ out.length)
    (Hcont : ∀ (regs' : bvmap 5 word) (n : Nat), 1 ≤ n → n ≤ out.length →
      regs_agree musl_clob regs regs' →
      getr regs' 1 = kra → getr regs' 2 = sp0 →
      getr regs' 10 = len_word (out.take n) →
      to_wall_tail source_segs (Z_to_bv 64 1)
        (mkst regs' kra (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) rom)
        (out.drop n) k) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs (at_ CBB 0x00) mem rom) out k :=
  musl_write_wall source_segs CBB
    f00 f04 f08 f0c f10 f14 f18 f1c f20 f24 f28 f2c f30 f34 f38 f3c
    f6c f70 f74 f78 f7c f80 f84 f88 f8c f90
    k regs mem rom kra sp0 buf len out Hrom Hk Hr28 H1 H2 H10 H11 H12
    Hok Hnw Hlen Hread Hnb Hcont

theorem cb_write_call (k : machine_state → Prop)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (kra sp0 buf len : word) (out : List byte)
    (Hev : bv_unsigned kra % 2 = 0)
    (H1 : getr regs 1 = kra) (H2 : getr regs 2 = sp0)
    (H10 : getr regs 10 = Z_to_bv 64 1) (H11 : getr regs 11 = buf)
    (H12 : getr regs 12 = len)
    (Hok : store_ok source_segs mem (at_ sp0 (-8)) 8 = true)
    (Hnw : bv_unsigned (at_ sp0 (-8)) + 8 ≤ 2^64)
    (Hlen : bv_unsigned len ≤ 18446744073709547520)
    (Hread : rdn source_segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
      buf (word_to_nat len) = some out)
    (Hnb : 1 ≤ out.length)
    (Hcont : ∀ regs' n, 1 ≤ n → n ≤ out.length →
      getr regs' 1 = kra → getr regs' 2 = sp0 →
      getr regs' 10 = len_word (out.take n) →
      to_wall_tail source_segs (Z_to_bv 64 1)
        (mkst regs' kra (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
          (seg_rom source_segs)) (out.drop n) k) :
    to_wall_tail source_segs (Z_to_bv 64 1)
      (mkst regs 0x110fc mem (seg_rom source_segs)) out k := by
  apply cb_write_wall0 k regs mem (seg_rom source_segs) kra sp0 buf len out
    rfl (ret_ok_even kra Hev) (ret_ok_even _ (by decide +kernel))
    H1 H2 H10 H11 H12 Hok Hnw Hlen Hread Hnb
  intro regs' n Hn1 Hn2 _ R1 R2 R10
  exact Hcont regs' n Hn1 Hn2 R1 R2 R10

end LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_hoare
