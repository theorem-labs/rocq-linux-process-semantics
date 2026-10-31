import LinuxProcessSemantics.Common.MuslCall
import LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # modprint-ns: instantiate the musl write-call summary

PROOF-SIDE, not trusted spec. Rocq `Z` is `Int`, `nat` is `Nat`, `Some`
is `some`, and `firstn n out` is `out.take n`. Closed address equations
replace the Rocq fetch-rebasing tactic; the shared summary is reused.
-/

namespace LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_hoare

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.Hoare
open LinuxProcessSemantics.Common.MuslCall
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def WB : word := 0x11098

theorem fetch_at (segs : List Segment) (b : word) (d : Int) (a : word) (w : BitVec 32)
    (ha : at_ b d = a) (hf : fetch_word segs a = some w) :
    fetch_word segs (at_ b d) = some w := by
  rw [ha]
  exact hf

theorem f00 : fetch_word source_segs (at_ WB 0x00) = some Wsp16m := by
  exact fetch_at source_segs WB 0x00 0x11098 Wsp16m (by decide +kernel) SF_11098

theorem f04 : fetch_word source_segs (at_ WB 0x04) = some Wmv_a3a2 := by
  exact fetch_at source_segs WB 0x04 0x1109c Wmv_a3a2 (by decide +kernel) SF_1109c

theorem f08 : fetch_word source_segs (at_ WB 0x08) = some Wli_a6_0 := by
  exact fetch_at source_segs WB 0x08 0x110a0 Wli_a6_0 (by decide +kernel) SF_110a0

theorem f0c : fetch_word source_segs (at_ WB 0x0c) = some Wmv_a2a1 := by
  exact fetch_at source_segs WB 0x0c 0x110a4 Wmv_a2a1 (by decide +kernel) SF_110a4

theorem f10 : fetch_word source_segs (at_ WB 0x10) = some Wli_a5_0 := by
  exact fetch_at source_segs WB 0x10 0x110a8 Wli_a5_0 (by decide +kernel) SF_110a8

theorem f14 : fetch_word source_segs (at_ WB 0x14) = some Wmv_a1a0 := by
  exact fetch_at source_segs WB 0x14 0x110ac Wmv_a1a0 (by decide +kernel) SF_110ac

theorem f18 : fetch_word source_segs (at_ WB 0x18) = some Wli_a4_0 := by
  exact fetch_at source_segs WB 0x18 0x110b0 Wli_a4_0 (by decide +kernel) SF_110b0

theorem f1c : fetch_word source_segs (at_ WB 0x1c) = some Wli_a0_64 := by
  exact fetch_at source_segs WB 0x1c 0x110b4 Wli_a0_64 (by decide +kernel) SF_110b4

theorem f20 : fetch_word source_segs (at_ WB 0x20) = some Wsd_ra8 := by
  exact fetch_at source_segs WB 0x20 0x110b8 Wsd_ra8 (by decide +kernel) SF_110b8

theorem f24 : fetch_word source_segs (at_ WB 0x24) = some Wjal_cp := by
  exact fetch_at source_segs WB 0x24 0x110bc Wjal_cp (by decide +kernel) SF_110bc

theorem f28 : fetch_word source_segs (at_ WB 0x28) = some Wld_ra8 := by
  exact fetch_at source_segs WB 0x28 0x110c0 Wld_ra8 (by decide +kernel) SF_110c0

theorem f2c : fetch_word source_segs (at_ WB 0x2c) = some Wsp16p := by
  exact fetch_at source_segs WB 0x2c 0x110c4 Wsp16p (by decide +kernel) SF_110c4

theorem f30 : fetch_word source_segs (at_ WB 0x30) = some Wj4 := by
  exact fetch_at source_segs WB 0x30 0x110c8 Wj4 (by decide +kernel) SF_110c8

theorem f34 : fetch_word source_segs (at_ WB 0x34) = some Wlui_a5 := by
  exact fetch_at source_segs WB 0x34 0x110cc Wlui_a5 (by decide +kernel) SF_110cc

theorem f38 : fetch_word source_segs (at_ WB 0x38) = some Wbltu := by
  exact fetch_at source_segs WB 0x38 0x110d0 Wbltu (by decide +kernel) SF_110d0

theorem f3c : fetch_word source_segs (at_ WB 0x3c) = some Wret := by
  exact fetch_at source_segs WB 0x3c 0x110d4 Wret (by decide +kernel) SF_110d4

theorem f6c : fetch_word source_segs (at_ WB 0x6c) = some Wmv_a7a0 := by
  exact fetch_at source_segs WB 0x6c 0x11104 Wmv_a7a0 (by decide +kernel) SF_11104

theorem f70 : fetch_word source_segs (at_ WB 0x70) = some Wmv_a0a1 := by
  exact fetch_at source_segs WB 0x70 0x11108 Wmv_a0a1 (by decide +kernel) SF_11108

theorem f74 : fetch_word source_segs (at_ WB 0x74) = some Wmv_a1a2 := by
  exact fetch_at source_segs WB 0x74 0x1110c Wmv_a1a2 (by decide +kernel) SF_1110c

theorem f78 : fetch_word source_segs (at_ WB 0x78) = some Wmv_a2a3 := by
  exact fetch_at source_segs WB 0x78 0x11110 Wmv_a2a3 (by decide +kernel) SF_11110

theorem f7c : fetch_word source_segs (at_ WB 0x7c) = some Wmv_a3a4 := by
  exact fetch_at source_segs WB 0x7c 0x11114 Wmv_a3a4 (by decide +kernel) SF_11114

theorem f80 : fetch_word source_segs (at_ WB 0x80) = some Wmv_a4a5 := by
  exact fetch_at source_segs WB 0x80 0x11118 Wmv_a4a5 (by decide +kernel) SF_11118

theorem f84 : fetch_word source_segs (at_ WB 0x84) = some Wmv_a5a6 := by
  exact fetch_at source_segs WB 0x84 0x1111c Wmv_a5a6 (by decide +kernel) SF_1111c

theorem f88 : fetch_word source_segs (at_ WB 0x88) = some Wecall := by
  exact fetch_at source_segs WB 0x88 0x11120 Wecall (by decide +kernel) SF_11120

theorem f8c : fetch_word source_segs (at_ WB 0x8c) = some Wret := by
  exact fetch_at source_segs WB 0x8c 0x11124 Wret (by decide +kernel) SF_11124

theorem f90 : fetch_word source_segs (at_ WB 0x90) = some Wj_cpc := by
  exact fetch_at source_segs WB 0x90 0x11128 Wj_cpc (by decide +kernel) SF_11128

theorem modprint_write_call
    (regs : bvmap 5 word) (mem : word → Option byte)
    (sp0 buf : word) (out : List byte) (bufs : List (List byte)) (code : word)
    (h1 : getr regs 1 = (0x11034 : word))
    (h2 : getr regs 2 = sp0)
    (h10 : getr regs 10 = Z_to_bv 64 1)
    (h11 : getr regs 11 = buf)
    (h12 : getr regs 12 = Z_to_bv 64 2)
    (hok : RiscvSemantics.store_ok source_segs mem (at_ sp0 (-8)) 8 = true)
    (hnw : bv_unsigned (at_ sp0 (-8)) + 8 ≤ 2 ^ 64)
    (hread : rdn source_segs
      (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 (0x11034 : word)))
      buf 2 = some out)
    (hcont : ∀ (regs' : bvmap 5 word) (n : Nat), 1 ≤ n → n ≤ out.length →
      getr regs' 1 = (0x11034 : word) →
      getr regs' 2 = sp0 →
      getr regs' 10 = len_word (out.take n) →
      to_wexit source_segs
        (mkst regs' (0x11034 : word)
          (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 (0x11034 : word)))
          (seg_rom source_segs)) bufs code) :
    to_wexit source_segs
      (mkst regs (0x11098 : word) mem (seg_rom source_segs)) (out :: bufs) code := by
  exact musl_write_wexit source_segs WB
    f00 f04 f08 f0c f10 f14 f18 f1c f20 f24 f28 f2c f30 f34 f38 f3c
    f6c f70 f74 f78 f7c f80 f84 f88 f8c f90
    regs mem (seg_rom source_segs) 0x11034 sp0 buf (Z_to_bv 64 2) out bufs code
    rfl (ret_ok_even _ (by decide +kernel)) (ret_ok_even _ (by decide +kernel))
    h1 h2 h10 h11 h12 hok hnw (by decide +kernel) hread
    (by have hlen := rdn_length _ _ _ _ _ hread; omega) hcont

end LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_hoare
