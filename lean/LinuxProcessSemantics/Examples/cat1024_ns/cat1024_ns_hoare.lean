import LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs
import LinuxProcessSemantics.Common.Hoare
import LinuxProcessSemantics.Common.MuslCall
import LinuxProcessSemantics.Common.SymTac

/-! rocq-baseline: 8bef2933e7063c3b77d628343969f2352008c3ca -/

/-! Mirrors `theories/Examples/cat1024_ns/cat1024_ns_hoare.v` at the
baseline above; see that Rocq file for the argument. The Rocq Ltac `fat`
and its closed-equation helper `bveq` are replaced by conversion against
the generated fetch lemmas. `reg_neq_tac` is replaced by `decide`.
Rocq `Z` becomes `Int`, `nat` becomes `Nat`, and `firstn`/`skipn`
become `List.take`/`List.drop`.
-/

namespace LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_hoare

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.Hoare
open LinuxProcessSemantics.Common.MuslCall
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_code
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def CATB : word := 0x11104

theorem fetch_at (segs : List Segment) (b : word) (d : Int) (a : word) (w : BitVec 32)
    (ha : at_ b d = a) (hf : fetch_word segs a = some w) :
    fetch_word segs (at_ b d) = some w := by
  rw [ha]
  exact hf

theorem f00 : fetch_word source_segs (at_ CATB 0x00) = some Wsp16m := SF_11104

theorem f04 : fetch_word source_segs (at_ CATB 0x04) = some Wmv_a3a2 := SF_11108

theorem f08 : fetch_word source_segs (at_ CATB 0x08) = some Wli_a6_0 := SF_1110c

theorem f0c : fetch_word source_segs (at_ CATB 0x0c) = some Wmv_a2a1 := SF_11110

theorem f10 : fetch_word source_segs (at_ CATB 0x10) = some Wli_a5_0 := SF_11114

theorem f14 : fetch_word source_segs (at_ CATB 0x14) = some Wmv_a1a0 := SF_11118

theorem f18 : fetch_word source_segs (at_ CATB 0x18) = some Wli_a4_0 := SF_1111c

theorem f1c : fetch_word source_segs (at_ CATB 0x1c) = some Wli_a0_64 := SF_11120

theorem f20 : fetch_word source_segs (at_ CATB 0x20) = some Wsd_ra8 := SF_11124

theorem f24 : fetch_word source_segs (at_ CATB 0x24) = some Wjal_cp := SF_11128

theorem f28 : fetch_word source_segs (at_ CATB 0x28) = some Wld_ra8 := SF_1112c

theorem f2c : fetch_word source_segs (at_ CATB 0x2c) = some Wsp16p := SF_11130

theorem f30 : fetch_word source_segs (at_ CATB 0x30) = some Wj4 := SF_11134

theorem f34 : fetch_word source_segs (at_ CATB 0x34) = some Wlui_a5 := SF_11138

theorem f38 : fetch_word source_segs (at_ CATB 0x38) = some Wbltu := SF_1113c

theorem f3c : fetch_word source_segs (at_ CATB 0x3c) = some Wret := SF_11140

theorem f6c : fetch_word source_segs (at_ CATB 0x6c) = some Wmv_a7a0 := SF_11170

theorem f70 : fetch_word source_segs (at_ CATB 0x70) = some Wmv_a0a1 := SF_11174

theorem f74 : fetch_word source_segs (at_ CATB 0x74) = some Wmv_a1a2 := SF_11178

theorem f78 : fetch_word source_segs (at_ CATB 0x78) = some Wmv_a2a3 := SF_1117c

theorem f7c : fetch_word source_segs (at_ CATB 0x7c) = some Wmv_a3a4 := SF_11180

theorem f80 : fetch_word source_segs (at_ CATB 0x80) = some Wmv_a4a5 := SF_11184

theorem f84 : fetch_word source_segs (at_ CATB 0x84) = some Wmv_a5a6 := SF_11188

theorem f88 : fetch_word source_segs (at_ CATB 0x88) = some Wecall := SF_1118c

theorem f8c : fetch_word source_segs (at_ CATB 0x8c) = some Wret := SF_11190

theorem f90 : fetch_word source_segs (at_ CATB 0x90) = some Wj_cpc := SF_11194

theorem cat_write_enter
    (k sp0 fd buf len : word) (mem0 : word → Option byte) :
    triple source_segs musl_clob (musl_wset sp0)
      (fun regs mem _ =>
         mem = mem0
         ∧ getr regs 1 = k ∧ getr regs 2 = sp0
         ∧ getr regs 10 = fd ∧ getr regs 11 = buf ∧ getr regs 12 = len
         ∧ store_ok source_segs mem0 (at_ sp0 (-8)) 8 = true)
      (at_ CATB 0x00) (at_ CATB 0x88)
      (fun regs mem _ =>
         mem = wbytes mem0 (at_ sp0 (-8)) (word_to_le_bytes 8 k)
         ∧ getr regs 1 = at_ CATB 0x28 ∧ getr regs 2 = at_ sp0 (-16)
         ∧ getr regs 10 = fd ∧ getr regs 11 = buf ∧ getr regs 12 = len
         ∧ getr regs 17 = Z_to_bv 64 64) :=
  musl_write_enter source_segs CATB
  f00 f04 f08 f0c f10 f14 f18 f1c f20 f24 f6c f70 f74 f78 f7c f80 f84 f90 k sp0 fd buf len mem0

theorem cat_write_leave
    (k sp0 rv : word) (mem1 : word → Option byte)
    (Hk : ret_ok k) (Hr28 : ret_ok (at_ CATB 0x28)) :
    triple source_segs musl_clob (musl_wset sp0)
      (fun regs mem _ =>
         mem = mem1
         ∧ getr regs 1 = at_ CATB 0x28 ∧ getr regs 2 = at_ sp0 (-16)
         ∧ getr regs 10 = rv
         ∧ rdn source_segs mem1 (at_ sp0 (-8)) 8 = some (word_to_le_bytes 8 k)
         ∧ c_ltu errno_lo rv = false)
      (at_ CATB 0x8c) k
      (fun regs mem _ =>
         mem = mem1 ∧ getr regs 1 = k ∧ getr regs 2 = sp0 ∧ getr regs 10 = rv) :=
  musl_write_leave source_segs CATB f28 f2c f30 f34 f38 f3c f8c k sp0 rv mem1 Hk Hr28

theorem cat_write_twr (LH : machine_state → Prop)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (k sp0 buf len : word) (bs : List byte)
    (hev : bv_unsigned k % 2 = 0)
    (h1 : getr regs 1 = k) (h2 : getr regs 2 = sp0)
    (h10 : getr regs 10 = Z_to_bv 64 1) (h11 : getr regs 11 = buf)
    (h12 : getr regs 12 = len)
    (hok : store_ok source_segs mem (at_ sp0 (-8)) 8 = true)
    (hnw : bv_unsigned (at_ sp0 (-8)) + 8 ≤ 2 ^ 64)
    (hlen : bv_unsigned len ≤ 18446744073709547520)
    (hread : rdn source_segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
      buf (word_to_nat len) = some bs)
    (hnb : 1 ≤ bs.length)
    (hcont : ∀ n regs', 1 ≤ n → n ≤ bs.length →
      regs_agree musl_clob regs regs' →
      getr regs' 1 = k → getr regs' 2 = sp0 →
      getr regs' 10 = len_word (bs.take n) →
      to_wall_tail source_segs (Z_to_bv 64 1)
        (mkst regs' k (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
          (seg_rom source_segs))
        (bs.drop n) (lh_next source_segs LH)) :
    to_wr source_segs LH bs (mkst regs 0x11104 mem (seg_rom source_segs)) := by
  have hk : ret_ok k := ret_ok_even k hev
  have hr28 : ret_ok (at_ CATB 0x28) := ret_ok_even _ (by decide)
  have hlbs : (bs.length : Int) ≤ 18446744073709547520 := by
    rw [rdn_length source_segs _ _ _ _ hread]
    exact hlen
  obtain ⟨regs1, mem1, hst, ⟨hm, q1, q2, q10, q11, q12, q17⟩, hag1, _⟩ :=
    cat_write_enter k sp0 (Z_to_bv 64 1) buf len mem regs mem (seg_rom source_segs)
      ⟨rfl, h1, h2, h10, h11, h12, hok⟩
  subst hm
  refine msteps_to_wr source_segs LH bs _ _ hst ?_
  refine to_wr.twr_step _ _ rfl
    (step_ecall source_segs regs1 (at_ CATB 0x88) _ (seg_rom source_segs) Wecall f88 E_ecall) ?_
  refine twr_here_rec source_segs LH bs regs1 (at_ CATB 0x88) _ (seg_rom source_segs)
    ?_ ?_ ?_ hnb ?_
  · rw [q17]
    decide
  · rw [← getr_nz regs1 10 (by decide)]
    exact q10
  · rw [ms_read_bytes_rdn source_segs]
    · rw [← getr_nz regs1 11 (by decide), ← getr_nz regs1 12 (by decide), q11, q12]
      exact hread
    · rfl
  · intro n hn1 hn2
    have hru : bv_unsigned (len_word (bs.take n)) = (n : Int) :=
      u_len_word_firstn n bs hn2 (by omega)
    rw [at_step CATB 0x88 4 0x8c (by decide)]
    obtain ⟨regs2, mem2, hst2, ⟨hm2, r1, r2, r10⟩, hag2, _⟩ :=
      cat_write_leave k sp0 (len_word (bs.take n))
        (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) hk hr28
        (regupd regs1 10 (len_word (bs.take n)))
        (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) (seg_rom source_segs)
        ⟨rfl,
         by rw [getr_other _ _ _ _ (by decide)]; exact q1,
         by rw [getr_other _ _ _ _ (by decide)]; exact q2,
         by rw [getr_same _ _ _ (by decide)],
         rdn_wbytes_hit8 source_segs mem _ k hnw,
         not_errno _ (by rw [hru]; omega)⟩
    subst hm2
    refine msteps_to_wall_tail source_segs _ _ _ _ _ hst2 ?_
    refine hcont n regs2 hn1 hn2 ?_ r1 r2 r10
    refine regs_agree_trans _ _ _ _ hag1 (regs_agree_trans _ _ _ _ ?_ hag2)
    exact regs_agree_upd _ _ _ _ _ (by unfold musl_clob; decide) (regs_agree_refl _ _)

end LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_hoare
